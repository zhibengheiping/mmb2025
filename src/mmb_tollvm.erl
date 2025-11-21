%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_tollvm).

-export([convert/1]).

-include("mmb_ssa.hrl").


convert(SSA) ->
    Fns = mmb_ssa:collect_fns(SSA),
    {Alloc, Values, SSA1} = create_myalloc(SSA#ssa{types=#{}}),
    {Values1, SSA2} = convert_fns(maps:to_list(Fns), #{}, Values, Alloc, SSA1),
    convert_types(maps:keys(Values1), SSA2).

create_myalloc(SSA) ->
    {GStart, SSA1} = mmb_ssa:add_node({const, ptr, {op, {zero, ptr}, []}}, SSA),
    {GEnd, SSA2} = mmb_ssa:add_node({const, ptr, {op, {zero, ptr}, []}}, SSA1),
    {N, SSA3} = mmb_ssa:add_node({var, i32, arg}, SSA2),
    {CMask, SSA4} = add_const('Int', 16#FFFFFFF0, SSA3),
    {N3, SSA8} = mmb_ssa:add_node({var, i32, {op, 'and', [N, CMask]}}, SSA4),

    %% Start = load ptr, @start
    {Start, SSA9} = mmb_ssa:add_node({var, ptr, {op, load, [GStart]}}, SSA8),
    % Start1 = Start + N3
    {Start1, SSA10} = mmb_ssa:add_node({var, ptr, {op, {gep, i8}, [Start, N3]}}, SSA9),
    % End = load ptr, @end
    {End, SSA11} = mmb_ssa:add_node({var, ptr, {op, load, [GEnd]}}, SSA10),
    %% Start1 > End
    {Cond, SSA12} = mmb_ssa:add_node({var, i1, {op, 'icmp ugt', [Start1, End]}}, SSA11),

    {Malloc, SSA13} = add_const(ptr, {fn, malloc}, SSA12),
    {C1M, SSA14} = add_const('Int', 1048576, SSA13),
    %% Start2 = malloc(1M)
    {Start2, SSA15} = mmb_ssa:add_node({var, ptr, {call, Malloc, [C1M]}}, SSA14),
    %% End1 = Start2 + 1M
    {End1, SSA16} = mmb_ssa:add_node({var, ptr, {op, {gep, i8}, [Start2, C1M]}}, SSA15),
    {Start3, SSA17} = mmb_ssa:add_node({var, ptr, {op, {gep, i8}, [Start2, N3]}}, SSA16),

    {Result, SSA18} = mmb_ssa:add_node({var, ptr, phi}, SSA17),
    {Start4, SSA19} = mmb_ssa:add_node({var, ptr, phi}, SSA18),

    {Exit, SSA20} = mmb_ssa:add_node({bb, [], none, [{return, Result}]}, SSA19),
    {Merge, SSA21} = mmb_ssa:add_node({bb, [Result, Start4], {Exit, []}, [{op, store, [Start4, GStart]}]}, SSA20),
    {Branch, SSA22} = mmb_ssa:add_node({bb, [], {Merge, [Start2, Start3]}, [{'let', Start2}, {'let', End1}, {op, store, [End1, GEnd]}, {'let', Start3}]}, SSA21),
    {Entry, SSA23} = mmb_ssa:add_node({bb, [], {'if', Cond, {Branch, []}, {Merge, [Start, Start1]}}, [{'let', N3}, {'let', Start}, {'let', Start1}, {'let', End}, {'let', Cond}]}, SSA22),
    {Fn, SSA24} = mmb_ssa:add_node({fn, none, [N], ptr, Entry, Exit}, SSA23),
    {Alloc, SSA25} = mmb_ssa:add_node({const, ptr, {fn, Fn}}, SSA24),
    {Alloc, #{C1M => [], CMask => []}, SSA25}.



convert_fns([], _, Values, _, SSA) ->
    {Values, SSA};
convert_fns([H|T], Globals, Values, Alloc, SSA) ->
    {Globals1, Values1, SSA1} = convert_fn(H, Globals, Values, Alloc, SSA),
    convert_fns(T, Globals1, Values1, Alloc, SSA1).

convert_fn({ID, []}, Globals, Values, _, SSA) when is_atom(ID) ->
    {Globals, Values, SSA};
convert_fn({ID, Blocks}, Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    #{ID := {fn, none, Params, ReturnType, Entry, Exit}} = Nodes,
    ReturnType1 = type_name(ReturnType, Nodes),
    Values1 = collect_args(Params, Values),
    SSA1 = mmb_ssa:set_node(ID, {fn, none, Params, ReturnType1, Entry, Exit}, SSA),
    convert_blocks(Blocks, Globals, Values1, Alloc, SSA1).


convert_blocks([], Globals, Values, _, SSA) ->
    {Globals, Values, SSA};
convert_blocks([H|T], Globals, Values, Alloc, SSA) ->
    {Globals1, Values1, SSA1} = convert_block(H, Globals, Values, Alloc, SSA),
    convert_blocks(T, Globals1, Values1, Alloc, SSA1).

convert_block(ID, Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Values1 = collect_args(Input, Values),
    {Stmts1, Globals1, Values2, SSA1} = convert_stmts(Stmts, Globals, Values1, Alloc, SSA),
    {Output1, Values3, SSA2} = convert_output(Output, Values2, SSA1),
    SSA3 = mmb_ssa:set_node(ID, {bb, Input, Output1, Stmts1}, SSA2),
    {Globals1, Values3, SSA3}.

convert_output(none, Values, SSA) ->
    {none, Values, SSA};
convert_output({ExitID, List}, Values, SSA) ->
    {List1, Values1, SSA1} = convert_values(List, Values, SSA),
    {{ExitID, List1}, Values1, SSA1};
convert_output({'if', Cond, True, False}, Values, SSA) ->
    {Cond1, Values1, SSA1} = convert_value(Cond, Values, SSA),
    {True1, Values2, SSA2} = convert_output(True, Values1, SSA1),
    {False1, Values3, SSA3} = convert_output(False, Values2, SSA2),
    {{'if', Cond1, True1, False1}, Values3, SSA3}.

convert_stmts([], Globals, Values, _, SSA) ->
    {[], Globals, Values, SSA};
convert_stmts([{'let', ID}|T], Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, Expr}} = Nodes,
    case Expr of
        {op, {cast, _, _}, _} ->
            convert_stmts(T, Globals, Values, Alloc, SSA);
        _ ->
            convert_expr(ID, Type, Expr, T, Globals, Values#{ID => []}, Alloc, SSA)
    end;
convert_stmts([fail|T], Globals, Values, Alloc, SSA) ->
    {T1, Globals1, Values1, SSA1} = convert_stmts(T, Globals, Values, Alloc, SSA),
    {[fail|T1], Globals1, Values1, SSA1};
convert_stmts([return|T], Globals, Values, Alloc, SSA) ->
    {T1, Globals1, Values1, SSA1} = convert_stmts(T, Globals, Values, Alloc, SSA),
    {[return|T1], Globals1, Values1, SSA1};
convert_stmts([{return, Expr}|T], Globals, Values, Alloc, SSA) ->
    {Expr1, Values1, SSA1} = convert_value(Expr, Values, SSA),
    {T1, Globals1, Values2, SSA2} = convert_stmts(T, Globals, Values1, Alloc, SSA1),
    {[{return, Expr1}|T1], Globals1, Values2, SSA2};
convert_stmts([{call, Fun, Args}|T], Globals, Values, Alloc, SSA) ->
    {[Fun1|Args1], Values1, SSA1} = convert_values([Fun|Args], Values, SSA),
    {T1, Globals1, Values2, SSA2} = convert_stmts(T, Globals, Values1, Alloc, SSA1),
    {[{call, Fun1, Args1}|T1], Globals1, Values2, SSA2};
convert_stmts([{op, {store, ref}, [Value, Ref]}|T], Globals, Values, Alloc, SSA) ->
    {[Value1, Ref1], Values1, SSA1} = convert_values([Value, Ref], Values, SSA),
    {T1, Globals1, Values2, SSA2} = convert_stmts(T, Globals, Values1, Alloc, SSA1),
    {[{op, store, [Value1, Ref1]}|T1], Globals1, Values2, SSA2};
convert_stmts([{op, {store, array}, [Value, Array, Index]}|T], Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    Type = var_type(Value, Nodes),
    {[Value1, Array1, Index1], Values1, SSA1} = convert_values([Value, Array, Index], Values, SSA),
    {Ptr, SSA2} = mmb_ssa:add_node({var, ptr, {op, {gep, Type}, [Array1, Index1]}}, SSA1),
    {T1, Globals1, Values2, SSA3} = convert_stmts(T, Globals, Values1, Alloc, SSA2),
    {[{'let', Ptr},{op, store, [Value1, Ptr]}|T1], Globals1, Values2, SSA3};
convert_stmts([{op, {store, global, G}, [Value]}|T], Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    Type = var_type(Value, Nodes),
    {Value1, Values1, SSA1} = convert_value(Value, Values, SSA),
    {ID, Globals1, SSA2} = global_id(G, Globals, SSA1),
    {T1, Globals2, Values2, SSA3} = convert_stmts(T, Globals1, Values1, Alloc, SSA2),
    SSA4 = mmb_ssa:set_node(ID, {const, ptr, {op, {zero, Type}, []}}, SSA3),
    {[{op, store, [Value1, ID]}|T1], Globals2, Values2, SSA4}.

convert_expr(ID, Type, {op, {load, global, G}, []}, T, Globals, Values, Alloc, SSA) ->
    {G1, Globals1, SSA1} = global_id(G, Globals, SSA),
    {T1, Globals2, Values1, SSA2} = convert_stmts(T, Globals1, Values, Alloc, SSA1),
    SSA3 = mmb_ssa:set_node(ID, {var, Type, {op, load, [G1]}}, SSA2),
    {[{'let', ID}|T1], Globals2, Values1, SSA3};
convert_expr(ID, Type, {op, {load, array}, [Array, Index]}, T, Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    Type1 = type_name(Type, Nodes),
    {[Array1, Index1], Values1, SSA1} = convert_values([Array, Index], Values, SSA),
    {Ptr, SSA2} = mmb_ssa:add_node({var, ptr, {op, {gep, Type1}, [Array1, Index1]}}, SSA1),
    {T1, Globals1, Values2, SSA3} = convert_stmts(T, Globals, Values1, Alloc, SSA2),
    SSA4 = mmb_ssa:set_node(ID, {var, Type, {op, load, [Ptr]}}, SSA3),
    {[{'let', Ptr},{'let', ID}|T1], Globals1, Values2, SSA4};
convert_expr(ID, Type, {op, {load, tuple, Index}, [Tuple]}, T, Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    #{Tuple := {_, TupleType, _}} = Nodes,
    {Struct, SSA1} = convert_struct(TupleType, SSA),
    {Tuple1, Values1, SSA2} = convert_value(Tuple, Values, SSA1),
    {Zero, SSA3} = add_const('Int', 0, SSA2),
    {Index1, SSA4} = add_const('Int', Index, SSA3),
    Values2 = Values1#{Zero => [], Index1 => []},
    {Ptr, SSA5} = mmb_ssa:add_node({var, ptr, {op, {gep, Struct}, [Tuple1, Zero, Index1]}}, SSA4),
    {T1, Globals1, Values3, SSA6} = convert_stmts(T, Globals, Values2, Alloc, SSA5),
    SSA7 = mmb_ssa:set_node(ID, {var, Type, {op, load, [Ptr]}}, SSA6),
    {[{'let', Ptr},{'let', ID}|T1], Globals1, Values3, SSA7};
convert_expr(ID, Type, {op, {load, _}, [Expr]}, T, Globals, Values, Alloc, SSA) ->
    {Expr1, Values1, SSA1} = convert_value(Expr, Values, SSA),
    {T1, Globals1, Values2, SSA2} = convert_stmts(T, Globals, Values1, Alloc, SSA1),
    SSA3 = mmb_ssa:set_node(ID, {var, Type, {op, load, [Expr1]}}, SSA2),
    {[{'let', ID}|T1], Globals1, Values2, SSA3};
convert_expr(ID, Type, {op, {make, tuple}, List}, T, Globals, Values, Alloc, SSA) ->
    {Struct, SSA1} = convert_struct(Type, SSA),
    {List1, Values1, SSA2} = convert_values(List, Values, SSA1),
    {Size, SSA3} = add_const('Int', {op, {sizeof, Struct}, []}, SSA2),
    Values2 = Values1#{Size => []},
    {T1, Globals1, Values3, SSA4} = convert_stmts(T, Globals, Values2, Alloc, SSA3),
    SSA5 = mmb_ssa:set_node(ID, {var, Type, {call, Alloc, [Size]}}, SSA4),
    {T2, Values4, SSA6} = settuple(0, List1, ID, Struct, T1, Values3, SSA5),
    {[{'let', ID}|T2], Globals1, Values4, SSA6};
convert_expr(ID, Type, {op, {make, ref}, [Expr]}, T, Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    Type1 = type_name(Type, Nodes),
    {Expr1, Values1, SSA1} = convert_value(Expr, Values, SSA),
    {Size, SSA2} = add_const('Int', {op, {sizeof, Type1}, []}, SSA1),
    Values2 = Values1#{Size => []},
    {T1, Globals1, Values3, SSA3} = convert_stmts(T, Globals, Values2, Alloc, SSA2),
    SSA4 = mmb_ssa:set_node(ID, {var, Type, {call, Alloc, [Size]}}, SSA3),
    {[{'let', ID}, {op, store, [Expr1, ID]}|T1], Globals1, Values3, SSA4};
convert_expr(ID, Type, {op, {make, array}, [N, K]}, T, Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    #{K := {_, ElemType, _}} = Nodes,
    {Func, SSA1} = array_func(ElemType, SSA),
    {[N1, K1], Values1, SSA2} = convert_values([N,K], Values, SSA1),
    {T1, Globals1, Values2, SSA3} = convert_stmts(T, Globals, Values1, Alloc, SSA2),
    SSA4 = mmb_ssa:set_node(ID, {var, Type, {call, Func, [N1, K1]}}, SSA3),
    {[{'let', ID}|T1], Globals1, Values2, SSA4};
convert_expr(ID, Type, {op, {make, array}, [N]}, T, Globals, Values, Alloc, SSA) ->
    {Func, SSA1} = add_const(ptr, {fn, malloc}, SSA),
    {N1, Values1, SSA2} = convert_value(N, Values, SSA1),
    case Type of
        'Bool' ->
            N2 = N1,
            Values2 = Values1,
            SSA4 = SSA2;
        'Int' ->
            {C2, SSA3} = add_const('Int', 2, SSA2),
            Values2 = Values1#{C2 => []},
            {N2, SSA4} = mmb_ssa:add_node({var, i32, {op, shl, [N1, C2]}}, SSA3);
        _ ->
            {C3, SSA3} = add_const('Int', 3, SSA2),
            Values2 = Values1#{C3 => []},
            {N2, SSA4} = mmb_ssa:add_node({var, i32, {op, shl, [N1, C3]}}, SSA3)
    end,
    {T1, Globals1, Values3, SSA5} = convert_stmts(T, Globals, Values2, Alloc, SSA4),
    SSA6 = mmb_ssa:set_node(ID, {var, Type, {call, Func, [N2]}}, SSA5),
    Stmts = [{'let', ID}|T1],
    Stmts1 =
        case N2 of
            N1 ->
                Stmts;
            _ ->
                [{'let', N2}|Stmts]
        end,
    {Stmts1, Globals1, Values3, SSA6};
convert_expr(ID, Type, {call, Fun, Args}, T, Globals, Values, Alloc, SSA = #ssa{nodes=Nodes}) ->
    case Nodes of
        #{Fun := {const, _, {fn, float_of_int}}} ->
            {[X], Values1, SSA1} = convert_values(Args, Values, SSA),
            {T1, Globals1, Values2, SSA2} = convert_stmts(T, Globals, Values1, Alloc, SSA1),
            SSA3 = mmb_ssa:set_node(ID, {var, Type, {op, sitofp, [X]}}, SSA2),
            {[{'let', ID}|T1], Globals1, Values2, SSA3};
        _ ->
            {[Fun1|Args1], Values1, SSA1} = convert_values([Fun|Args], Values, SSA),
            {T1, Globals1, Values2, SSA2} = convert_stmts(T, Globals, Values1, Alloc, SSA1),
            SSA3 = mmb_ssa:set_node(ID, {var, Type, {call, Fun1, Args1}}, SSA2),
            {[{'let', ID}|T1], Globals1, Values2, SSA3}
    end;
convert_expr(ID, Type, {op, Op, List}, T, Globals, Values, Alloc, SSA) ->
    {List1, Values1, SSA1} = convert_values(List, Values, SSA),
    {T1, Globals1, Values2, SSA2} = convert_stmts(T, Globals, Values1, Alloc, SSA1),
    SSA3 = mmb_ssa:set_node(ID, {var, Type, {op, op(Op), List1}}, SSA2),
    {[{'let', ID}|T1], Globals1, Values2, SSA3}.

settuple(_, [], _, _, Rest, Values, SSA) ->
    {Rest, Values, SSA};
settuple(Index, [H|T], Tuple, Struct, Rest, Values, SSA) ->
    {H1, Values1, SSA1} = setelem(Index, Tuple, Struct, Values, SSA),
    {T1, Values2, SSA2} = settuple(Index + 1, T, Tuple, Struct, Rest, Values1, SSA1),
    {[{'let', H1}, {op, store, [H, H1]}|T1], Values2, SSA2}.

setelem(Index, Tuple, Struct, Values, SSA) ->
    {Zero, SSA1} = add_const('Int', 0, SSA),
    {Index1, SSA2} = add_const('Int', Index, SSA1),
    {Ptr, SSA3} = mmb_ssa:add_node({var, ptr, {op, {gep, Struct}, [Tuple, Zero, Index1]}}, SSA2),
    Values1 = Values#{Zero => [], Index1 => []},
    {Ptr, Values1, SSA3}.

array_func('Bool', SSA) ->
    add_const(ptr, {fn, create_array}, SSA);
array_func('Int', SSA) ->
    add_const(ptr, {fn, create_array}, SSA);
array_func('Double', SSA) ->
    add_const(ptr, {fn, create_float_array}, SSA);
array_func(_, SSA) ->
    add_const(ptr, {fn, create_ptr_array}, SSA).

op({cmp, 'Bool', '=='}) ->
    'icmp eq';
op({cmp, 'Int', '<'}) ->
    'icmp slt';
op({cmp, 'Int', '<='}) ->
    'icmp sle';
op({cmp, 'Int', '>'}) ->
    'icmp sgt';
op({cmp, 'Int', '>='}) ->
    'icmp sge';
op({cmp, 'Int', '=='}) ->
    'icmp eq';
op({cmp, 'Int', '!='}) ->
    'icmp ne';
op({cmp, 'Double', '<'}) ->
    'fcmp olt';
op({cmp, 'Double', '<='}) ->
    'fcmp ole';
op({cmp, 'Double', '>'}) ->
    'fcmp ogt';
op({cmp, 'Double', '>='}) ->
    'fcmp oge';
op({cmp, 'Double', '=='}) ->
    'fcmp oeq';
op({cmp, 'Double', '!='}) ->
    'fcmp one';
op({bool, 'and'}) ->
    'and';
op({bool, 'or'}) ->
    'or';
op({bool, 'not'}) ->
    'not';
op({arith, 'Int', '+'}) ->
    add;
op({arith, 'Int', '-'}) ->
    sub;
op({arith, 'Int', '*'}) ->
    mul;
op({arith, 'Int', '/'}) ->
    sdiv;
op({arith, 'Int', '%'}) ->
    srem;
op({arith, 'Int', neg}) ->
    neg;
op({arith, 'Double', '+'}) ->
    fadd;
op({arith, 'Double', '-'}) ->
    fsub;
op({arith, 'Double', '*'}) ->
    fmul;
op({arith, 'Double', '/'}) ->
    fdiv;
op({arith, 'Double', '%'}) ->
    frem;
op({arith, 'Double', neg}) ->
    fneg;
op(select) ->
    select;
op(is_same_ptr) ->
    'icmp eq'.


collect_args([], Values) ->
    Values;
collect_args([H|T], Values) ->
    collect_args(T, Values#{H => []}).

convert_values([], Values, SSA) ->
    {[], Values, SSA};
convert_values([H|T], Values, SSA) ->
    {H1, Values1, SSA1} = convert_value(H, Values, SSA),
    {T1, Values2, SSA2} = convert_values(T, Values1, SSA1),
    {[H1|T1], Values2, SSA2}.

convert_value(ID, Values, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {Kind, Type, Expr}} = Nodes,
    case Expr of
        {op, {cast, _, _}, [Y]} ->
            convert_value(Y, Values, SSA);
        _ ->
            case Kind of
                var ->
                    {ID, Values, SSA};
                const when is_map_key(ID, Values) ->
                    {ID, Values, SSA};
                const ->
                    case Expr of
                        X when is_integer(X); is_float(X); is_atom(X) ->
                            {ID, Values#{ID => []}, SSA};
                        {fn, _} ->
                            {ID, Values#{ID => []}, SSA};
                        {op, {make, tuple}, List} ->
                            {_, SSA1} = convert_struct(Type, SSA),
                            {List1, Values1, SSA2} = convert_values(List, Values, SSA1),
                            SSA3 = mmb_ssa:set_node(ID, {const, Type, {op, {make, tuple}, List1}}, SSA2),
                            {ID, Values1#{ID => []}, SSA3}
                    end
            end
    end.

add_const(Type, Value, SSA = #ssa{values=Values}) ->
    Const = {const, Type, Value},
    case Values of
        #{Const := ID} ->
            {ID, SSA};
        _ ->
            {ID, SSA1} = mmb_ssa:add_node(Const, SSA),
            Values1 = Values#{Const => ID},
            {ID, SSA1#ssa{values=Values1}}
    end.


global_id(G, Globals, SSA) ->
    case Globals of
        #{G := ID} ->
            {ID, Globals, SSA};
        _ ->
            {ID, SSA1} = new_id(SSA),
            {ID, Globals#{G => ID}, SSA1}
    end.

type_name(ID, Nodes) when is_integer(ID) ->
    #{ID := {type, Type}} = Nodes,
    case Type of
        {closure, _, _} ->
            ptr;
        {tuple, _} ->
            ptr;
        {struct, _} ->
            ptr;
        {enum, _} ->
            ptr;
        {array, _} ->
            ptr;
        {fn, _, _} ->
            ptr;
        {ref, _} ->
            ptr
    end;
type_name('Unit', _) ->
    void;
type_name('Int', _) ->
    i32;
type_name('Bool', _) ->
    i1;
type_name('Double', _) ->
    double.

var_type(ID, Nodes) when is_integer(ID) ->
    #{ID := {_, Type, _}} = Nodes,
    type_name(Type, Nodes).

new_id(SSA = #ssa{count = Count}) ->
    {Count, SSA#ssa{count = Count + 1}}.


convert_struct(ID, SSA = #ssa{nodes=Nodes, types=Types}) ->
    #{ID := {type, Type}} = Nodes,
    TypeList =
        case Type of
            {struct, List} ->
                [type_name(T, Nodes) || {_, T} <- List];
            {tuple, List} ->
                [type_name(T, Nodes) || T <- List]
        end,
    Struct = {struct, TypeList},
    case Types of
        #{Struct := ID1} ->
            {ID1, SSA};
        _ ->
            {ID1, SSA1} = mmb_ssa:add_node({type, Struct}, SSA),
            Types1 = Types#{Struct => ID1},
            {ID1, SSA1#ssa{types=Types1}}
    end.


convert_types([], SSA) ->
    SSA;
convert_types([H|T], SSA) ->
    convert_types(T, convert_type(H, SSA)).

convert_type(ID, SSA = #ssa{nodes = Nodes, values=Values}) ->
    #{ID := {Kind, Type, Expr}} = Nodes,
    Type1 = type_name(Type, Nodes),
    Value = {Kind, Type1, Expr},
    Values1 =
        case Kind of
            const ->
                case Type1 of
                    ptr ->
                        Values;
                    _ ->
                        Values#{Value => ID}
                end;
            _ ->
                Values
        end,

    mmb_ssa:set_node(ID, Value, SSA#ssa{values=Values1}).
