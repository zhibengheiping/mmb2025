%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_compact).

-export([compact/4]).

-include("mmb_ssa.hrl").

-record(
   s,
   {
    count = 0,
    varmap = #{},
    fns,
    typemap,
    defines,
    typeids = #{},
    valueids = #{},
    queue = mmb_queue:init(),
    fnmap = #{},
    genmap = #{},
    nodes = #{},
    labelmap = #{}
   }).

compact(Root, Fns, TypeMap, Defines) ->
    {ID, State} = access_fn({Root, []}, #s{fns=Fns, typemap=TypeMap, defines=Defines}),
    {Count, Nodes, Types, Values} = process(State),
    #ssa{count=Count, root=ID, nodes=Nodes, types=Types, values=Values}.

process(State = #s{fnmap=FnMap, fns=Fns, count=Count, nodes=Nodes, typeids=Types, valueids=Values, queue=Queue}) ->
    case mmb_queue:pop(Queue) of
        none ->
            {Count, Nodes, Types, Values};
        {{FnID, Gen} = Key, Queue1} ->
            #{Key := ID} = FnMap,
            #{FnID := Fn} = Fns,
            process(fn(ID, Gen, Fn, State#s{queue=Queue1}))
    end.

fn(ID, GenArgs, {fn, Free, Gen, Params, Return, Blocks}, State = #s{varmap = VarMap, labelmap=LabelMap}) ->
    GenMap = mmb_type:gen_map(Gen, GenArgs),
    State1 = State#s{genmap = GenMap},
    {Free2, State3} =
        case Free of
            none ->
                {none, State1};
            _ ->
                {Free1, State2} = new_vars(Free, State1),
                create(Free1, free, State2)
        end,
    {Params1, State4} = new_vars(Params, State3),
    {Params2, State5} = create(Params1, arg, State4),
    {[Exit|Entry], State6} = blocks(Blocks, State5),
    {Return1, State7} = vartype(Return, State6),
    State8 = add(ID, {fn, Free2, Params2, Return1, Entry, Exit}, State7),
    State8#s{varmap = VarMap, labelmap = LabelMap}.

blocks([E], State) ->
    {E1, State1} = block(E, State),
    {[E1], State1};
blocks([H|T], State) ->
    {H1, State1} = block(H, State),
    {[T1|_], State2} = blocks(T, State1),
    {[T1|H1], State2}.

block({BlockID, Input, Output, Stmts}, State) ->
    {BlockID1, State1} = label(BlockID, State),
    {Input1, State2} = new_vars(Input, State1),
    {Input2, State3} = create(Input1, phi, State2),
    {Stmts1, State4} = stmts(Stmts, State3),
    {Output1, State5} = output(Output, State4),
    {BlockID1, add(BlockID1, {bb, Input2, Output1, Stmts1}, State5)}.

create([], _, State) ->
    {[], State};
create([{ID, Type}|T], Kind, State) ->
    {T1, State1} = create(T, Kind, add_var(ID, Type, Kind, State)),
    {[ID|T1], State1}.

new_vars([], State) ->
    {[], State};
new_vars([H|T], State) ->
    {H1, State1} = new_var(H, State),
    {T1, State2} = new_vars(T, State1),
    case H1 of
        {_, 'Unit'} ->
            {T1, State2};
        _ ->
            {[H1|T1], State2}
    end.

new_var(Var, State = #s{varmap = VarMap}) ->
    case maps:is_key(Var, VarMap) of
        false ->
            {ID, State1} = new_id(State),
            VarMap1 = VarMap#{Var => ID},
            {Type, State2} = vartype(Var, State1#s{varmap = VarMap1}),
            {{ID, Type}, State2}
    end.

add_var(ID, Type, Expr, State) ->
    add(ID, {var, Type, Expr}, State).

add(ID, Node, State = #s{nodes = Nodes}) ->
    Nodes1 = Nodes#{ID => Node},
    State#s{nodes = Nodes1}.

new_const(Var, Value, State) ->
    {Type, State1 = #s{valueids = Values, varmap = VarMap, nodes = Nodes}} = vartype(Var, State),
    Const = {const, Type, Value},
    case Values of
        #{Const := ID} ->
            #{ID := Const} = Nodes,
            VarMap1 = VarMap#{Var => ID},
            State1#s{varmap = VarMap1};
        _ ->
            {ID, State2} = new_id(State1),
            VarMap1 = VarMap#{Var => ID},
            Values1 = Values#{Const => ID},
            add(ID, Const, State2#s{varmap = VarMap1, valueids=Values1})
    end.

stmts([], State) ->
    {[], State};
stmts([{'let', Var, {move, Expr}}|Rest], State) ->
    {Expr1, State1 = #s{varmap = VarMap}} = var(Expr, State),
    VarMap1 =
        case Expr1 of
            'Unit' ->
                VarMap;
            _ ->
                {ID, _} = Expr1,
                VarMap#{Var => ID}
        end,
    stmts(Rest, State1#s{varmap = VarMap1});
stmts([{'let', Var, Expr}|Rest], State) ->
    {Expr1, State1} = expr(Expr, State),
    case Expr1 of
        'Unit' ->
            stmts(Rest, State1);
        {literal, X} ->
            stmts(Rest, new_const(Var, X, State1));
        _ ->
            {{ID, Type}, State2} = new_var(Var, State1),
            {Rest1, State3} = stmts(Rest, State2),
            case Type of
                'Unit' ->
                    case Expr1 of
                        {op, {make, array}, _} ->
                            {Rest1, State3};
                        {op, {make, ref}, _} ->
                            {Rest1, State3};
                        {op, {load, array}, _} ->
                            {Rest1, State3};
                        {op, {load, ref}, _} ->
                            {Rest1, State3};
                        _ ->
                            {[Expr1|Rest1], State3}
                    end;
                _ ->
                    case Expr1 of
                        {closure, ClosureType, [Fn|_]=List} ->
                            {Closure, State4=#s{nodes=Nodes}} = new_id(State3),
                            #{Fn := {const, _, {fn, FnID}}} = Nodes,
                            State5 = add_var(Closure, ClosureType, {op, {make, tuple}, List}, State4),
                            State6 = add_var(ID, Type, {op, {cast, up, {fn, FnID}}, [Closure]}, State5),
                            {[{'let', Closure}, {'let', ID}|Rest1], State6};
                        _ ->
                            {[{'let', ID}|Rest1], add_var(ID, Type, Expr1, State3)}
                    end
            end
    end;
stmts([{destruct, N, Vars, Expr}|Rest], State) ->
    {Expr1, State1} = var(Expr, State),
    {Vars1, State2} = new_vars(Vars, State1),
    {Rest1, State3} = stmts(Rest, State2),
    case Vars1 of
        [] ->
            {Rest1, State3};
        Vars2 ->
            {ID, _} = Expr1,
            destruct(N, Vars2, ID, Rest1, State3)
    end;
stmts([{return, Expr}|Rest], State) ->
    {Expr1, State1} = var(Expr, State),
    {Rest1, State2} = stmts(Rest, State1),
    case Expr1 of
        'Unit' ->
            {[return|Rest1], State2};
        _ ->
            {ID, _} = Expr1,
            {[{return, ID}|Rest1], State2}
    end;
stmts([{op, {store, Kind}, List}|Rest], State) ->
    {[Value|_]=List1, State1} = vars(List, State),
    {Rest1, State2} = stmts(Rest, State1),
    case Value of
        'Unit' ->
            {Rest1, State2};
        _ ->
            {[{op, {store, Kind}, [V || {V, _} <- List1]}|Rest1], State2}
    end;
stmts([fail|Rest], State) ->
    {Rest1, State1} = stmts(Rest, State),
    {[fail|Rest1], State1}.

destruct(_, [], _, Rest, State) ->
    {Rest, State};
destruct(Index, [{ID, Type}|T], Expr, Rest, State) ->
    {Rest1, State1} = destruct(Index + 1, T, Expr, Rest, State),
    {[{'let', ID}|Rest1], add_var(ID, Type, {op, {load, tuple, Index}, [Expr]}, State1)}.

expr({literal, {fn, Fn, Gen}}, State) ->
    {ID, State1} = access_fn({Fn, Gen}, State),
    {{literal, {fn, ID}}, State1};
expr({literal, '()'}, State) ->
    {'Unit', State};
expr({literal, _}=Value, State) ->
    {Value, State};
expr({op, {make, tuple}, List}, State) ->
    {List1, State1} = vars(List, State),
    case [V || {V,_} <- List1] of
        [] ->
            {'Unit', State1};
        List2 ->
            {{op, {make, tuple}, List2}, State1}
    end;
expr({op, {arith, Op}, List}, State) ->
    {[H|_] = List1, State1} = vars(List, State),
    List2 = [V || {V,_} <- List1],
    case H of
        {_, 'Double'} ->
            {{op, {arith, 'Double', Op}, List2}, State1};
        {_, 'Int'} ->
            {{op, {arith, 'Int', Op}, List2}, State1}
    end;
expr({op, {cmp, Op}, List}, State) ->
    {[H|_] = List1, State1} = vars(List, State),
    List2 = [V || {V,_} <- List1],
    case H of
        {_, 'Bool'} ->
            {{op, {cmp, 'Bool', Op}, List2}, State1};
        {_, 'Double'} ->
            {{op, {cmp, 'Double', Op}, List2}, State1};
        {_, 'Int'} ->
            {{op, {cmp, 'Int', Op}, List2}, State1}
    end;
expr({op, Op, List}, State) ->
    {List1, State1} = vars(List, State),
    {{op, Op, [V || {V,_} <- List1]}, State1};
expr({call, Fun, Args}, State) ->
    {[Fun1|Args1], State1} = vars([Fun|Args], State),
    {ID, _} = Fun1,
    {{call, ID, [V || {V,_} <- Args1]}, State1};
expr({closure, Fn, FnID}, State = #s{fns = Fns}) ->
    #{FnID := {fn, Free, _, _, _, _}} = Fns,
    {List, State1} = vars([Fn|Free], State),
    {Type, State2} = typeid({tuple, [T || {_,T} <- List]}, State1),
    {{closure, Type, [V || {V,_} <- List]}, State2};
expr({attr, Name, Struct}, State) ->
    {Struct1, State1 = #s{nodes = Types}} = var(Struct, State),
    case Struct1 of
        'Unit' ->
            {'Unit', State1};
        _ ->
            {ID, Type} = Struct1,
            case lookup_field_index(Name, Type, Types) of
                'Unit' ->
                    {'Unit', State1};
                Index ->
                    {{op, {load, tuple, Index}, [ID]}, State1}
            end
    end.


lookup_field_index(Name, Type, Types) ->
    #{Type := {type, {struct, Fields}}} = Types,
    lookup_index(0, Name, Fields).

lookup_index(_, _, []) ->
    'Unit';
lookup_index(Index, Name, [{Name, _}|_]) ->
    Index;
lookup_index(Index, Name, [_|Rest]) ->
    lookup_index(Index+1, Name, Rest).

vars([], State) ->
    {[], State};
vars([H|T], State) ->
    {H1, State1} = var(H, State),
    {T1, State2} = vars(T, State1),
    {[H1|T1], State2}.

var(Var, State) ->
    {Type, State1 = #s{varmap = VarMap}} = vartype(Var, State),
    case Type of
        'Unit' ->
            {'Unit', State1};
        _ ->
            case VarMap of
                #{Var := ID} ->
                    {{ID, Type}, State}
            end
    end.

new_id(State = #s{count = Count}) ->
    {Count, State#s{count = Count + 1}}.

output(none, State) ->
    {none, State};
output({BlockID, List}, State) ->
    {BlockID1, State1} = label(BlockID, State),
    {List1, State2} = vars(List, State1),
    List2 = filter_unit(List1),
    {{BlockID1, [V ||{V,_} <- List2]}, State2};
output({'if', Cond, True, False}, State) ->
    {{Cond1, _}, State1} = var(Cond, State),
    {True1, State2} = output(True, State1),
    {False1, State3} = output(False, State2),
    {{'if', Cond1, True1, False1}, State3}.

access_fn({Fn, Gen}, State) when is_atom(Fn) ->
    [] = Gen,
    {Fn, State};
access_fn({Fn, Gen}, State = #s{typemap=TypeMap, genmap=GenMap, fnmap = FnMap, queue=Queue}) ->
    Gen1 = [mmb_type:bind(G, GenMap, TypeMap) || G <- Gen],
    Key = {Fn, Gen1},
    case FnMap of
        #{Key := ID} ->
            {ID, State};
        _ ->
            {ID, State2} = new_id(State),
            FnMap1 = FnMap#{Key => ID},
            Queue1 = mmb_queue:push(Key, Queue),
            {ID, State2#s{fnmap=FnMap1, queue=Queue1}}
    end.


vartype(Var, State = #s{genmap = GenMap}) ->
    type(Var, GenMap, State).

type(Type, GenMap, State = #s{typemap = TypeMap}) ->
    type(mmb_type:bind(Type, GenMap, TypeMap), State).

type(Type, State) when is_atom(Type) ->
    {Type, State};
type({ref, Type}, State) ->
    {Type1, State1} = type(Type, State),
    case Type1 of
        'Unit' ->
            {'Unit', State1};
        _ ->
            typeid({ref, Type1}, State1)
    end;
type({array, Type}, State) ->
    {Type1, State1} = type(Type, State),
    case Type1 of
        'Unit' ->
            {'Unit', State1};
        _ ->
            typeid({array, Type1}, State1)
    end;
type({tuple, List}, State) ->
    {List1, State1} = types(List, State),
    case filter_unit(List1) of
        [] ->
            {'Unit', State1};
        List2 ->
            typeid({tuple, List2}, State1)
    end;
type({fn, Params, Return}, State) ->
    {[Return1|Params1], State1} = types([Return|Params], State),
    Params2 = filter_unit(Params1),
    typeid({fn, Params2, Return1}, State1);
type({closure, Params, Return}, State) ->
    {[Return1|Params1], State1} = types([Return|Params], State),
    Params2 = filter_unit(Params1),
    typeid({closure, Params2, Return1}, State1);
type({typedef, N, Gen}, State=#s{genmap = GenMap, typemap=TypeMap}) ->
    Gen1 = [mmb_type:bind(G, GenMap, TypeMap) || G <- Gen],
    {Gen2, State1} = types(Gen1, State),
    typedef_typeid({typedef, N, Gen2}, Gen1, State1).

filter_unit(List) ->
    [X || X <- List, X =/= 'Unit'].

types([], State) ->
    {[], State};
types([H|T], State) ->
    {H1, State1} = type(H, State),
    {T1, State2} = types(T, State1),
    {[H1|T1], State2}.

typeid(Key, State = #s{typeids = Ids, nodes = Types}) ->
    case Ids of
        #{Key := ID} ->
            {ID, State};
        _ ->
            {ID, State1} = new_id(State),
            Ids1 = Ids#{Key => ID},
            Types1 = Types#{ID => {type, Key}},
            {ID, State1#s{typeids = Ids1, nodes = Types1}}
    end.

typedef_typeid(Key = {typedef, N, _}, Gen, State = #s{typeids = Ids}) ->
    case Ids of
        #{Key := ID} ->
            {ID, State};
        _ ->
            {ID, State1 = #s{defines = Defines}} = new_id(State),
            #{N := Type} = Defines,
            Ids1 = Ids#{Key => ID},
            {Type1, State2 = #s{typeids = Ids2, nodes = Types}} =
                typedef(Gen, Type, State1#s{typeids = Ids1}),
            case Type1 of
                'Unit' ->
                    Ids3 = Ids2#{Key => 'Unit'},
                    {'Unit', State2#s{typeids = Ids3}};
                _ ->
                    Types1 = Types#{ID => {type, Type1}},
                    {ID, State2#s{nodes = Types1}}
            end
    end.

typedef(GenArgs, {enum, Gen, Variants}, State) ->
    Map = mmb_type:gen_map(Gen, GenArgs),
    {Variants1, State1} = variants(Variants, Map, State),
    {{enum, Variants1}, State1};
typedef(GenArgs, {struct, Gen, Fields}, State) ->
    Map = mmb_type:gen_map(Gen, GenArgs),
    {Fields1, State1} = fields(Fields, Map, State),
    case Fields1 of
        [] ->
            {'Unit', State1};
        _ ->
            {{struct, Fields1}, State1}
    end.

variants([], _, State) ->
    {[], State};
variants([H|T], GenMap, State) ->
    {H1, State1} = variant(H, GenMap, State),
    {T1, State2} = variants(T, GenMap, State1),
    {[H1|T1], State2}.

variant({Name, List}, GenMap, State) ->
    {List1, State1} = types(List, GenMap, State),
    List2 = filter_unit(List1),
    {{Name, List2}, State1}.

fields([], _, State) ->
    {[], State};
fields([H|T], GenMap, State) ->
    {H1, State1} = field(H, GenMap, State),
    {T1, State2} = fields(T, GenMap, State1),
    case H1 of
        {_, 'Unit'} ->
            {T1, State2};
        _ ->
            {[H1|T1], State2}
    end.

field({Name, Type}, GenMap, State) ->
    {Type1, State1} = type(Type, GenMap, State),
    {{Name, Type1}, State1}.

types([], _GenMap, State) ->
    {[], State};
types([H|T], GenMap, State) ->
    {H1, State1} = type(H, GenMap, State),
    {T1, State2} = types(T, GenMap, State1),
    {[H1|T1], State2}.

label(Label, State=#s{labelmap = LabelMap}) ->
    case LabelMap of
        #{Label := ID} ->
            {ID, State};
        _ ->
            {ID, State1} = new_id(State),
            LabelMap1 = LabelMap#{Label => ID},
            {ID, State1#s{labelmap = LabelMap1}}
    end.
