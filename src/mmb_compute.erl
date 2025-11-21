%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_compute).

-export([init/0, resolve_vars/3, get_value_id/2, set_var/3, get_var/2, add_value/2, bind_value/3, eval/4, is_const/2, is_var/2, is_eval/2, uses/2, phi_back/3, get_type/2, get_value/2, is_pure/2]).

-include("mmb_ssa.hrl").

-record(ctx, {var2id=#{}, value2id=#{}, id2value=#{}}).

init() ->
    #ctx{}.

set_var(Var, ValueID, Context = #ctx{var2id=Vars}) ->
    Vars1 = Vars#{Var => ValueID},
    Context#ctx{var2id=Vars1}.

get_var(Var, #ctx{var2id=Vars}) ->
    #{Var := ValueID} = Vars,
    ValueID.


get_value_id(Value, #ctx{value2id=Value2ID}) ->
    #{Value := ID} = Value2ID,
    ID.

bind_value(Value, ID, Context = #ctx{value2id=Value2ID}) ->
    Value2ID1 = Value2ID#{Value => ID},
    Context#ctx{value2id=Value2ID1}.

add_value(Value, Context = #ctx{value2id=Value2ID, id2value=ID2Value}) ->
    case Value2ID of
        #{Value := ValueID} ->
            Value2ID1 = Value2ID,
            ID2Value1 = ID2Value;
        _ ->
            ValueID = maps:size(ID2Value),
            Value2ID1 = Value2ID#{Value => ValueID},
            ID2Value1 = ID2Value#{ValueID => Value}
    end,
    {ValueID, Context#ctx{value2id=Value2ID1, id2value=ID2Value1}}.

eval(Type, {op, Op, List}, Nodes, Context) ->
    {List1, Context1} = resolve_vars(List, Nodes, Context),
    eval_op(Op, Type, List1, Context1);
eval(Type, {call, Fun, Args}=Expr, Nodes, Context) ->
    case is_pure(Expr, Nodes) of
        false ->
            none;
        true ->
            {[Fun1|Args1], Context1} = resolve_vars([Fun|Args], Nodes, Context),
            add_value({eval, Type, {call, Fun1, Args1}}, Context1)
    end.

eval_const_op(Op, Type, List, Context) ->
    Kind =
        case is_all_const(List, Context) of
            true ->
                const;
            false ->
                eval
        end,
    add_value({Kind, Type, {op, Op, List}}, Context).

elem(0, [H|_]) ->
    H;
elem(N, [_|T]) ->
    elem(N-1, T).

eval_op(poison, _Type, _List, _Context) ->
    none;
eval_op({make, vref}=Op, Type, List, Context) ->
    add_value({eval, Type, {op, Op, List}}, Context);
eval_op({make, varray}=Op, Type, List, Context) ->
    add_value({eval, Type, {op, Op, List}}, Context);
eval_op({load, vref}=Op, Type, [Version, Ref]=List, Context = #ctx{id2value=Values}) ->
    #{Ref := Src} = Values,
    case Src of
        {_, _, {op, {make, vref}, [Version, Value]}} ->
            {Value, Context};
        {_, _, {op, {store, vref}, [Version, Value, _]}} ->
            {Value, Context};
        _ ->
            add_value({eval, Type, {op, Op, List}}, Context)
    end;
eval_op({load, varray}=Op, Type, [Version, Array, Index]=List, Context = #ctx{id2value=Values}) ->
    #{Array := Src} = Values,
    case Src of
        {_, _, {op, {make, varray}, [Version, _, K]}} ->
            {K, Context};
        {_, _, {op, {store, varray}, [Version, Value, _, Index]}} ->
            {Value, Context};
        _ ->
            add_value({eval, Type, {op, Op, List}}, Context)
    end;
eval_op({store, vref}=Op, Type, List, Context) ->
    add_value({eval, Type, {op, Op, List}}, Context);
eval_op({store, varray}=Op, Type, List, Context) ->
    add_value({eval, Type, {op, Op, List}}, Context);
eval_op({store, global, _}, _, _, _) ->
    none;
eval_op({load, global, _}=Op, Type, List, Context) ->
    add_value({eval, Type, {op, Op, List}}, Context);
eval_op({load, ref}, _, _, _) ->
    none;
eval_op({make, ref}, _, _, _) ->
    none;
eval_op({make, array}, _, _, _) ->
    none;
eval_op({load, array}, _, _, _) ->
    none;
eval_op({load, tuple, Index}=Op, Type, [TupleID], Context = #ctx{id2value=Values}) ->
    #{TupleID := Src} = Values,
    case Src of
        {_, _, {op, {make, tuple}, List}} ->
            {elem(Index, List), Context};
        _ ->
            eval_const_op(Op, Type, [TupleID], Context)
    end;
eval_op({make, tuple}=Op, Type, List, Context) ->
    eval_const_op(Op, Type, List, Context);
eval_op({cast, up, _}=Op, Type, List, Context) ->
    eval_const_op(Op, Type, List, Context);
eval_op({cast, down, Tag}=Op, Type, [ID]=List, Context = #ctx{id2value=Values}) ->
    #{ID := Src} = Values,
    case Src of
        {_, _, {op, {cast, up, Tag}, [TupleID]}} ->
            {TupleID, Context};
        _ ->
            case Tag of
                {fn, _} ->
                    eval_const_op(Op, Type, List, Context);
                _ ->
                    none
            end
    end;
eval_op({load, tag}=Op, Type, [ID], Context = #ctx{id2value=Values}) ->
    #{ID := Closure} = Values,
    case Closure of
        {_, _, {op, {cast, up, _}, [TupleID]}} ->
            #{TupleID := {_, _, {op, {make, tuple}, [Fun|_]}}} = Values,
            {Fun, Context};
       _ ->
            add_value({eval, Type, {op, Op, [ID]}}, Context)
    end;
eval_op({cmp, _, _}=Op, Type, List, Context) ->
    eval_calc(Op, Type, List, Context);
eval_op({arith, _, _}=Op, Type, List, Context) ->
    eval_calc(Op, Type, List, Context);
eval_op({bool, _}=Op, Type, List, Context) ->
    eval_calc(Op, Type, List, Context);
eval_op(select, Type, List, Context) ->
    eval_select(Type, List, Context);
eval_op(is_same_ptr=Op, Type, [X, Y]=List, Context) ->
    if X =:= Y ->
            add_value({const, Type, true}, Context);
       true ->
            case is_all_const(List, Context) of
                true ->
                    add_value({const, Type, false}, Context);
                false ->
                    add_value({eval, Type, {op, Op, List}}, Context)
            end
    end.

eval_select(_, [_, X, X], Context) ->
    {X, Context};
eval_select(Type, [Cond, X, Y]=List, Context) ->
    case is_const(Cond, Context) of
        true ->
            case get_const_value(Cond, Context) of
                true ->
                    {X, Context};
                false ->
                    {Y, Context}
            end;
        false ->
            case Type of
                'Bool' ->
                    XC = is_const(X, Context),
                    YC = is_const(Y, Context),

                    if XC and YC ->
                            case get_const_value(X, Context) of
                                true ->
                                    {Cond, Context};
                                false ->
                                    add_value({eval, Type, {op, {bool, 'not'}, [Cond]}}, Context)
                            end;
                       XC ->
                            case get_const_value(X, Context) of
                                true ->
                                    add_value({eval, Type, {op, {bool, 'or'}, [Cond, Y]}}, Context);
                                false ->
                                    add_value({eval, Type, {op, select, List}}, Context)
                            end;
                       YC ->
                            case get_const_value(Y, Context) of
                                false ->
                                    add_value({eval, Type, {op, {bool, 'and'}, [Cond, X]}}, Context);
                                true ->
                                    add_value({eval, Type, {op, select, List}}, Context)
                            end;
                       true ->
                            add_value({eval, Type, {op, select, List}}, Context)
                    end;
                _ ->
                    add_value({eval, Type, {op, select, List}}, Context)
            end
    end.

eval_calc({arith, 'Int', '+'}=Op, Type, List, Context) ->
    case is_all_const(List, Context) of
        true ->
            List1 = [get_const_value(X, Context) || X <- List],
            Value = eval_calc(Op, List1),
            add_value({const, Type, Value}, Context);
        false ->
            [X, Y] = List,
            case is_const(Y, Context) andalso get_const_value(Y, Context) =:= 0 of
                true ->
                    {X, Context};
                false ->
                    add_value({eval, Type, {op, Op, List}}, Context)
            end
    end;
eval_calc({arith, 'Int', '*'}=Op, Type, List, Context) ->
    case is_all_const(List, Context) of
        true ->
            List1 = [get_const_value(X, Context) || X <- List],
            Value = eval_calc(Op, List1),
            add_value({const, Type, Value}, Context);
        false ->
            [X, Y] = List,
            case is_const(Y, Context) of
                false ->
                    add_value({eval, Type, {op, Op, List}}, Context);
                true ->
                    case get_const_value(Y, Context) of
                        1 ->
                            {X, Context};
                        2 ->
                            add_value({eval, Type, {op, {'arith', 'Int', '+'}, [X, X]}}, Context);
                        _ ->
                            add_value({eval, Type, {op, Op, List}}, Context)
                    end
            end
    end;
eval_calc({arith, 'Int', '/'}=Op, Type, List, Context) ->
    case is_all_const(List, Context) of
        true ->
            List1 = [get_const_value(X, Context) || X <- List],
            Value = eval_calc(Op, List1),
            add_value({const, Type, Value}, Context);
        false ->
            [X, Y] = List,
            case is_const(Y, Context) andalso get_const_value(Y, Context) =:= 1 of
                true ->
                    {X, Context};
                false ->
                    add_value({eval, Type, {op, Op, List}}, Context)
            end
    end;
eval_calc({arith, 'Double', '/'}=Op, Type, [X, Y], Context) ->
    XC = is_const(X, Context),
    YC = is_const(Y, Context),
    case {XC, YC} of
        {true, true} ->
            Value = eval_calc(Op, [get_const_value(X, Context), get_const_value(Y, Context)]),
            add_value({const, Type, Value}, Context);
        {false, true} ->
            YV = get_const_value(Y, Context),
            if is_float(YV) ->
                    {Y1, Context1} = add_value({const, 'Double', 1.0/YV}, Context),
                    add_value({eval, Type, {op, {arith, 'Double', '*'}, [X, Y1]}}, Context1);
               true ->
                    add_value({eval, Type, {op, Op, [X, Y]}}, Context)
            end;
        _ ->
            add_value({eval, Type, {op, Op, [X, Y]}}, Context)
    end;
eval_calc(Op, Type, List, Context) ->
    case is_all_const(List, Context) of
        true ->
            List1 = [get_const_value(X, Context) || X <- List],
            Value = eval_calc(Op, List1),
            add_value({const, Type, Value}, Context);
        false ->
            add_value({eval, Type, {op, Op, List}}, Context)
    end.

eval_calc({arith, _, neg}, [X]) ->
    -X;
eval_calc({arith, _, '+'}, [X, Y]) ->
    X + Y;
eval_calc({arith, _, '-'}, [X, Y]) ->
    X - Y;
eval_calc({arith, 'Double', '*'}, [inf, inf]) ->
    inf;
eval_calc({arith, 'Double', '*'}, [inf, X]) when is_float(X)->
    inf;
eval_calc({arith, 'Double', '*'}, [X, inf]) when is_float(X)->
    inf;
eval_calc({arith, _, '*'}, [X, Y]) ->
    X * Y;
eval_calc({arith, _, '/'}, [0.0, 0.0]) ->
    nan;
eval_calc({arith, _, '/'}, [X, 0.0]) when X > 0.0 ->
    inf;
eval_calc({arith, _, '/'}, [X, 0.0]) when X < 0.0 ->
    ninf;
eval_calc({arith, 'Int', '/'}, [X, Y]) ->
    X div Y;
eval_calc({arith, _, '/'}, [X, Y]) ->
    X / Y;
eval_calc({arith, 'Int', '%'}, [X, Y]) ->
    X rem Y;
eval_calc({arith, _, '%'}, [X, Y]) ->
    math:fmod(X, Y);
eval_calc({cmp, _, '=='}, [X, Y]) ->
    X == Y;
eval_calc({cmp, _, '!='}, [X, Y]) ->
    X /= Y;
eval_calc({cmp, _, '<='}, [X, Y]) ->
    X =< Y;
eval_calc({cmp, _, '>='}, [X, Y]) ->
    X >= Y;
eval_calc({cmp, _, '>'}, [X, Y]) ->
    X > Y;
eval_calc({cmp, _, '<'}, [X, Y]) ->
    X < Y;
eval_calc({bool, 'and'}, [X, Y]) ->
    X and Y;
eval_calc({bool, 'or'}, [X, Y]) ->
    X or Y;
eval_calc({bool, 'not'}, [X]) ->
    not X.

get_const_value(ID, #ctx{id2value=Values}) ->
    #{ID := {const, _, Value}} = Values,
    Value.

is_all_const([], _) ->
    true;
is_all_const([H|T], Context) ->
    is_const(H, Context) andalso is_all_const(T, Context).

is_const(ID, #ctx{id2value=Values}) ->
    case Values of
        #{ID := {const, _, _}} ->
            true;
        _ ->
            false
    end.

is_eval(ID, #ctx{id2value=Values}) ->
    case Values of
        #{ID := {eval, _, _}} ->
            true;
        _ ->
            false
    end.

is_var(ID, #ctx{id2value=Values}) ->
    case Values of
        #{ID := {var, _, _}} ->
            true;
        _ ->
            false
    end.

resolve_vars([], _, Context) ->
    {[], Context};
resolve_vars([H|T], Nodes, Context = #ctx{var2id=Vars}) ->
    case Vars of
        #{H := H1} ->
            Context2 = Context;
        _ ->
            #{H := {const, Type, Value}} = Nodes,
            {H1, Context2} =
                case Value of
                    {op, Op, List} ->
                        {List1, Context1} = resolve_vars(List, Nodes, Context),
                        add_value({const, Type, {op, Op, List1}}, Context1);
                    _ ->
                        add_value({const, Type, Value}, Context)
                end
    end,
    {T1, Context3} = resolve_vars(T, Nodes, Context2),
    {[H1|T1], Context3}.


uses(ValueID, #ctx{id2value=Values}) ->
    #{ValueID := Value} = Values,
    case Value of
        {const, _, _} ->
            [];
        {eval, _, {op, _, List}} ->
            List;
        {eval, _, {call, Fun, Args}} ->
            [Fun|Args];
        {var, _, _} ->
            []
    end.

phi_back(ValueID, Phi, Context = #ctx{id2value=Values}) ->
    #{ValueID := {eval, Type, Expr}} = Values,
    Expr1 = phi_back_expr(Expr, Phi),
    case add_value({eval, Type, Expr1}, Context) of
        {ValueID, Context1} ->
            {ValueID, Phi, Context1};
        {ValueID1, Context1} ->
            {ValueID1, Phi#{ValueID => ValueID1}, Context1}
    end.

phi_back_expr({op, Op, List}, Phi) ->
    List1 = phi_back_list(List, Phi),
    {op, Op, List1};
phi_back_expr({call, Fun, Args}, Phi) ->
    [Fun1|Args1] = phi_back_list([Fun|Args], Phi),
    {call, Fun1, Args1}.

phi_back_list(List, Phi) ->
    [maps:get(ID, Phi, ID) || ID <- List].


get_type(ValueID, #ctx{id2value=Values}) ->
    #{ValueID := {_, Type, _}} = Values,
    Type.

get_value(ValueID, #ctx{id2value=Values}) ->
    #{ValueID := Value} = Values,
    Value.


is_pure({call, Fun, _}, Nodes) ->
    case Nodes of
        #{Fun := {const, _, {fn, Fn}}} when is_atom(Fn) ->
            case Fn of
                int_of_float -> true;
                float_of_int -> true;
                truncate -> true;
                floor -> true;
                abs_int -> true;
                abs_float -> true;
                max_float -> true;
                sqrt -> true;
                sin -> true;
                cos -> true;
                atan -> true;
                _ -> false
            end;
        _ ->
            false
    end;
is_pure({op, {store, _}, _}, _Nodes) ->
    false;
is_pure({op, {store, _, _}, _}, _Nodes) ->
    false;
is_pure({op, poison, _}, _Nodes) ->
    false;
is_pure({op, _, _}, _Nodes) ->
    true.
