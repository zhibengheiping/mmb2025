%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_scope).

-export([resolve/2]).

-record(
   s,
   {
    count = 0,
    level = 0,
    return = none,
    fns = [],
    vnames= #{},
    values = #{},
    types = #{},
    tnames = #{},
    typedefs = #{},
    dnames = #{},
    access = #{},
    depends = #{},
    gen = []
   }).

resolve(Types, Globals) ->
    Builtins =
        [
         {read_int, [], 'Int'},
         {print_int, [{i, 'Int'}], 'Unit'},
         {read_char, [], 'Int'},
         {print_char, [{c, 'Int'}], 'Unit'},
         {print_endline, [], 'Unit'},
         {int_of_float, [{f, 'Double'}], 'Int'},
         {float_of_int, [{i, 'Int'}], 'Double'},
         {truncate, [{f, 'Double'}], 'Int'},
         {floor, [{f, 'Double'}], 'Double'},
         {abs_float, [{f, 'Double'}], 'Double'},
         {sqrt, [{f, 'Double'}], 'Double'},
         {sin, [{f, 'Double'}], 'Double'},
         {cos, [{f, 'Double'}], 'Double'},
         {atan, [{f, 'Double'}], 'Double'}
        ],

    State = make_builtins(Builtins, #s{}),
    State1 = resolve_types(Types, State),
    State2 = resolve_globals(Globals, State1),
    collect(State2).

make_builtins([], State) ->
    State;
make_builtins([H|T], State) ->
    make_builtins(T, make_builtin(H, State)).

make_builtin({Atom, Params, Return}, State) ->
    Name = atom_to_binary(Atom),
    Fn = {fn, [], Name, Params, Return, builtin},
    State1 = #s{vnames = Names, values = Values} = declare_global(Fn, State),
    #{Name := {0, ClosureID}} = Names,
    #{ClosureID := {fn, ClosureID, [], Params1, Return1}} = Values,
    State2 = #s{depends=Depends} = make_wrapper(Atom, ClosureID, [], Params1, Return1, State1),
    State2#s{depends=Depends#{ClosureID => []}}.

resolve_types(Types, State) ->
    make_types(Types, declare_types(Types, State)).

declare_types([], State) ->
    State;
declare_types([H|T], State) ->
    declare_types(T, declare_type(H, State)).

declare_type({_, Gen, Name, _}, State = #s{tnames = Names}) ->
    false = maps:is_key(Name, Names),
    {ID, State1} = new_id(State),
    State1#s{tnames = Names#{Name => {typedef, ID, length(Gen)}}}.

make_types([], State) ->
    State;
make_types([Type|Rest], State) ->
    make_types(Rest, make_type(Type, State)).

make_type({Kind, Gen, Name, Body}, State = #s{tnames = Names}) ->
    #{Name := {typedef, ID, Length}} = Names,
    Length = length(Gen),
    {Gen1, State1} = declare_gens(Gen, State),
    {Body1, State2 = #s{typedefs = Defines}} = make_type_body(Kind, ID, Gen1, Body, State1),
    State2#s{typedefs = Defines#{ID => {Kind, Gen1, Body1}},
             tnames = Names}.

make_type_body(struct, _ID, _Gen, Body, State) ->
    make_fields(Body, State);
make_type_body(enum, ID, Gen, Body, State) ->
    {Variants, State1} = make_variants(ID, Gen, 0, Body, State),
    {Variants, State1}.

make_fields([], State) ->
    {[], State};
make_fields([H|T], State) ->
    {H1, State1} = make_field(H, State),
    {T1, State2} = make_fields(T, State1),
    {[H1|T1], State2}.

make_field({Name, Type}, State) ->
    {Type1, State1} = type(Type, State),
    {{Name, Type1}, State1}.

make_variants(_, _, _, [], State) ->
    {[], State};
make_variants(ID, Gen, N, [H|T], State) ->
    {H1, State1} = make_variant(ID, Gen, N, H, State),
    {T1, State2} = make_variants(ID, Gen, N+1, T, State1),
    {[H1|T1], State2}.

make_variant(ID, Gen, Index, {Name, Types}, State = #s{dnames = Names}) ->
    {Types1, State1} = types(Types, State),
    Global =
        case Names of
            #{Name := _} ->
                conflict;
            _ ->
                {ID, Gen, Index, Types1}
        end,
    Names1 = Names#{Name => Global},
    {{Name, Types1}, State1#s{dnames = Names1}}.

types([], State) ->
    {[], State};
types([H|T], State) ->
    {H1, State1} = type(H, State),
    {T1, State2} = types(T, State1),
    {[H1|T1], State2}.

type({ref, Type}, State) ->
    {Type1, State1} = type(Type, State),
    {{ref, Type1}, State1};
type({array, Type}, State) ->
    {Type1, State1} = type(Type, State),
    {{array, Type1}, State1};
type({tuple, List}, State) ->
    {List1, State1} = types(List, State),
    {{tuple, List1}, State1};
type({closure, Params, Return}, State) ->
    {[Return1|Params1], State1} = types([Return|Params], State),
    {{closure, Params1, Return1}, State1};
type({type, Name}, State = #s{tnames = Names}) ->
    #{Name := Type} = Names,
    case Type of
        {typedef, ID, 0} ->
            Type1 = {typedef, ID, []};
        {param, _} ->
            Type1 = Type
    end,
    {Type1, State};
type({type, Name, Args}, State = #s{tnames = Names}) ->
    #{Name := {typedef, ID, Length}} = Names,
    Length = length(Args),
    {Args1, State1} = types(Args, State),
    {{typedef, ID, Args1}, State1};
type('_', State) ->
    new_id(State);
type(Type, State) when is_atom(Type) ->
    {Type, State}.

resolve_globals(Globals, State) ->
    make_globals(Globals, declare_globals(Globals, State)).

declare_globals([], State) ->
    State;
declare_globals([H|T], State) ->
    declare_globals(T, declare_global(H, State)).

declare_global({'let', Name, Type, _}, State = #s{vnames = Names}) ->
    false = maps:is_key(Name, Names),
    {ID, State1} = new_id(State),
    Names1 = Names#{Name => {0, ID}},
    {Type1, State2} = type(Type, State1#s{vnames = Names1}),
    unify(ID, Type1, State2);
declare_global({fn, Gen, Name, Params, Return, _}, State=#s{vnames=Names, tnames=Types}) ->
    false = maps:is_key(Name, Names),
    {Gen1, State1} = declare_gens(Gen, State),
    {_, State2} = declare_fn(Gen1, Name, Params, Return, State1),
    State2#s{tnames=Types}.

declare_fn(Gen, Name, Params, Return, State) ->
    {ID, State1} = new_var(Name, State),
    {ClosureID, State2} = new_id(State1),
    {ParamsID, State3} = declare_params(Params, State2),
    {ReturnID, State4} = new_id(State3),
    {Return1, State5} = type(Return, State4),
    State6 = unify(ReturnID, Return1, State5),
    State7 = #s{values = Values} = unify(ClosureID, {closure, ParamsID, ReturnID}, State6),
    Fn = {fn, ID, Gen, [ClosureID|ParamsID], ReturnID},
    {Fn, State7#s{values=Values#{ID=>Fn}}}.

declare_params([], State) ->
    {[], State};
declare_params([{_, Type}|T], State) ->
    {ID, State1} = new_id(State),
    {Type1, State2 = #s{types = Types}} = type(Type, State1),
    Types1 = Types#{ID => Type1},
    {T1, State3} = declare_params(T, State2#s{types = Types1}),
    {[ID|T1], State3}.

declare_gens([], State) ->
    {[], State};
declare_gens([H|T], State) ->
    {H1, State1} = declare_gen(H, State),
    {T1, State2} = declare_gens(T, State1),
    {[H1|T1], State2}.

declare_gen(Name, State) ->
    {ID, State1 = #s{tnames = Names}} = new_id(State),
    {{param, ID}, State1#s{tnames = Names#{Name => {param, ID}}}}.

make_globals([], State) ->
    State;
make_globals([Global|Rest], State) ->
    make_globals(Rest, make_global(Global, State)).

make_global({'let', Name, _, Expr}, State = #s{vnames = Names}) ->
    #{Name := {0, ID}} = Names,
    {Expr1, State1} = expr(Expr, State#s{access = #{}, level=1}),
    State2 = #s{values = Values, depends=Depends, access=Access} = unify(ID, Expr1, State1),
    State2#s{
      values=Values#{ID => {alias, Expr1}},
      depends=Depends#{ID => maps:keys(Access)}};
make_global({fn, Gen, Name, Params, _, Body}, State = #s{vnames = Names, values = Values}) ->
    #{Name := {0, ID}} = Names,
    #{ID := {fn, ID, Gen1, Params1, Return}} = Values,
    {Body1, State1 = #s{access=Access, fns = Fns, depends=Depends}} =
        make_body(Gen, Gen1, [Name|[N||{N,_} <- Params]], Params1, Return, Body,
                  State#s{level=1, access=#{}, gen=Gen1}),
    Free = maps:keys(Access),
    Fn = {fn, ID, Free, Gen1, Params1, Return, Body1},
    State1#s{fns=[Fn|Fns], gen=[], depends=Depends#{ID=>Free}}.

make_wrapper(FunID, ID, Gen, Params=[_|Args], Return, State) ->
    {Fun, State1} = access_fn(FunID, Gen, Args, Return, State),
    {Args1, State2} = access_values(Args, State1),
    {Expr, State3} = new_value({call, Fun, Args1}, State2),
    State4 = #s{fns = Fns} = unify(Expr, Return, State3),
    Fn = {fn, ID, [], Gen, Params, Return, {block, [], Expr}},
    State4#s{fns=[Fn|Fns]}.

access_values([], State) ->
    {[], State};
access_values([H|T], State) ->
    {H1, State1} = access_value(H, State),
    {T1, State2} = access_values(T, State1),
    {[H1|T1], State2}.

access_value(V, State) ->
    {V1, State1} = new_value({var, V}, State),
    {V1, unify(V1, V, State1)}.

make_body(GenNames, Gen, ParamNames, Params, Return, Body, State = #s{level=Level, vnames = Names, tnames = Types, return=OutReturn}) ->
    Types1 = bind_gens(GenNames, Gen, Types),
    Names1 = bind_params(ParamNames, Params, Level, Names),
    {{block, _, Expr}=Body1, State1} =
        block(Body, State#s{return=Return, vnames=Names1, tnames=Types1}),
    State2 = unify(Expr, Return, State1),
    {Body1, State2#s{vnames=Names, tnames=Types, return=OutReturn}}.

bind_gens([], [], Types) ->
    Types;
bind_gens([H1|T1], [H2|T2], Types) ->
    bind_gens(T1, T2, Types#{H1 => H2}).

bind_params([], [], _Level, Vars) ->
    Vars;
bind_params([H1|T1], [H2|T2], Level, Vars) ->
    bind_params(T1, T2, Level, Vars#{H1 => {Level, H2}}).

block({block, Stmts, Expr}, State) ->
    {Stmts1, State1} = exprs(Stmts, State),
    {Expr1, State2} = expr(Expr, State1),
    {{block, Stmts1, Expr1}, State2}.

exprs([], State) ->
    {[], State};
exprs([H|T], State) ->
    {H1, State1} = expr(H, State),
    {T1, State2} = exprs(T, State1),
    {[H1|T1], State2}.

expr({destruct, Names, Type, Expr}, State) ->
    {ID, State1} = expr(Expr, State),
    {Vars, State2} = new_vars(Names, State1),
    {Type1, State3} = type(Type, State2),
    State4 = unify(ID, Type1, State3),
    State5 = unify(ID, {tuple, Vars}, State4),
    new_stmt({destruct, 0, Vars, ID}, State5);
expr({'let', Name, Type, Expr}, State) ->
    {ID, State1} = expr(Expr, State),
    {Type1, State2} = type(Type, State1),
    #s{vnames = Names, level = Level} = State3 = unify(ID, Type1, State2),
    Names1 =
        case Name of
            '_' ->
                Names;
            _ ->
                Names#{Name => {Level, ID}}
        end,
    new_stmt({'let', ID}, State3#s{vnames = Names1});
expr({do_while, Expr, Stmts}, State) ->
    {Expr1, State1} = expr(Expr, State),
    {Stmts1, State2} = exprs(Stmts, unify(Expr1, 'Bool', State1)),
    new_stmt({do_while, Expr1, Stmts1}, State2);
expr({while, Expr, Stmts}, State) ->
    {Expr1, State1} = expr(Expr, State),
    {Stmts1, State2} = exprs(Stmts, unify(Expr1, 'Bool', State1)),
    new_stmt({while, Expr1, Stmts1}, State2);
expr({assign, {var, Name}, Expr}, State) ->
    {Expr1, State1} = expr(Expr, State),
    {ID, State2 = #s{values = Values}} = access_var(Name, State1),
    #{ID := {op, {make, ref}, _}} = Values,
    new_stmt({assign, ID, Expr1}, unify(ID, {ref, Expr1}, State2));
expr({assign, {sub, Array, Index}, Expr}, State) ->
    {[Array1,Index1,Expr1], State1} = exprs([Array,Index,Expr], State),
    State2 = unify(Index1, 'Int', State1),
    State3 = unify(Array1, {array, Expr1}, State2),
    new_stmt({assign, Array1, Index1, Expr1}, State3);
expr({return, Expr}, State) ->
    {Cond, State1} = expr({literal, 'Bool', true}, State),
    {False, State2} = expr({literal, 'Unit', '()'}, State1),
    {Expr1, State3 = #s{return = Return}} = expr(Expr, State2),
    {True, State4} = new_stmt({return, Expr1}, unify(Expr1, Return, State3)),
    {ID, State5} = new_value({'if', Cond, True, False}, State4),
    {ID, unify_each(ID, [True, False], State5)};
expr({literal, Type, Value}, State) ->
    {ID, State1} = new_value({literal, Value}, State),
    {ID, unify(ID, Type, State1)};
expr({var, Name}, State) ->
    {Var, State1 = #s{values = Values}} = access_var(Name, State),
    case Values of
        #{Var := {fn, FunID, Gen, [_|Params], Return}} ->
            {Type, Value, State2} = closure(FunID, Gen, Params, Return, State1),
            {ID, State3} = new_value(Value, State2),
            {ID, unify(ID, Type, State3)};
        #{Var := {op, {make, ref}, _}} ->
            {Var1, State2} = access_value(Var, State1),
            {ID, State3} = new_value({op, {load, ref}, [Var1]}, State2),
            {ID, unify({ref, ID}, Var, State3)};
        _ ->
            {ID, State2} = new_value({var, Var}, State1),
            {ID, unify(ID, Var, State2)}
    end;
expr({ref, Expr}, State) ->
    {Expr1, State1} = expr(Expr, State),
    {ID, State2} = new_value({op, {make, ref}, [Expr1]}, State1),
    {ID, unify(ID, {ref, Expr1}, State2)};
expr({enum, Name, Variant, List}, State) ->
    {ID, Gen, Index, Params, State1} = variant(Name, Variant, State),
    {List1, State2} = exprs([{literal,'Int',Index}|List], State1),
    {TupleID, State3} = new_value({op, {make, tuple}, List1}, State2),
    State4 = unify_each({tuple, List1}, [TupleID, Params], State3),
    {Expr, State5} = new_value({op, {cast, up, Index}, [TupleID]}, State4),
    State6 = unify(Expr, {typedef, ID, Gen}, State5),
    {Expr, State6};
expr({attr, Expr, Name}, State) ->
    {Expr1, State1 = #s{types = Types, typedefs = Defines}} = expr(Expr, State),
    {typedef, TypeID, Gen} = mmb_type:get(Expr1, Types),
    #{TypeID := {struct, Gen1, Fields}} = Defines,
    {_Index, Type} = lookup_index(0, Name, Fields),
    Type1 = mmb_type:bind(Type, mmb_type:gen_map(Gen1, Gen), Types),
    {ID, State2} = new_value({attr, Name, Expr1}, State1),
    {ID, unify(ID, Type1, State2)};
expr({struct, Name, Body}, State = #s{tnames = Names, typedefs = Defines}) ->
    #{Name := {typedef, TypeID, _Gen}} = Names,
    #{TypeID := {struct, Gen, Fields}} = Defines,
    {Gen1, Map, State1} = new_instance(Gen, State),
    Body1 = maps:from_list(Body),
    {Fields1, State2} = fields(Fields, Map, Body1, State1),
    {ID, State3} = new_value({op, {make, tuple}, Fields1}, State2),
    {ID, unify(ID, {typedef, TypeID, Gen1}, State3)};
expr({tuple, List}, State) ->
    {List1, State1} = exprs(List, State),
    {ID, State2} = new_value({op, {make, tuple}, List1}, State1),
    {ID, unify(ID, {tuple, List1}, State2)};
expr({array, List}, State) ->
    {N, State1} = expr({literal, 'Int', length(List)}, State),
    {List1, State2} = exprs(List, State1),
    {ID, State3} = new_value({op, {make, array}, [N]}, State2),
    {Array, State4} = access_value(ID, State3),
    {Elem, State5} = new_id(State4),
    State6 = unify(Array, {array, Elem}, State5),
    {List2, State7} = setelements(0, List1, Array, State6),
    {Block, State8} = new_value({block, [ID|List2], Array}, State7),
    {Block, unify(Block, Array, State8)};
expr({sub, Array, Index}, State) ->
    {[Array1, Index1], State1} = exprs([Array, Index], State),
    {ID, State2} = new_value({op, {load, array}, [Array1, Index1]}, State1),
    State3 = unify(Index1, 'Int', State2),
    State4 = unify(Array1, {array, ID}, State3),
    {ID, State4};
expr({array, N, K}, State) ->
    {[N1,K1], State1} = exprs([N,K], State),
    {ID, State2} = new_value({op, {make, array}, [N1, K1]}, State1),
    State3 = unify(N1, 'Int', State2),
    State4 = unify(ID, {array, K1}, State3),
    {ID, State4};
expr({op, {Kind, Op}, V}, State) ->
    {V1, State1} = expr(V, State),
    {ID, State2} = new_value({op, {Kind, Op}, [V1]}, State1),
    {ID, op(Kind, ID, V1, State2)};
expr({op, {Kind, Op}, LHS, RHS}, State) ->
    {[LHS1, RHS1], State1} = exprs([LHS, RHS], State),
    {ID, State2} = new_value({op, {Kind, Op}, [LHS1, RHS1]}, State1),
    {ID, op(Kind, ID, LHS1, RHS1, State2)};
expr({call, Closure, Args}, State) ->
    {[Closure1|Args1], State1} = exprs([Closure|Args], State),
    {Closure2, State2} = access_value(Closure1, State1),
    {Fun, State3} = new_value({op, {load, tag}, [Closure1]}, State2),
    {ID, State4} = new_value({call, Fun, [Closure2|Args1]}, State3),
    State5 = unify(Fun, {fn, [Closure2|Args1], ID}, State4),
    {ID, unify(Closure1, {closure, Args1, ID}, State5)};
expr({match, Expr, Arms}, State) ->
    {Expr1, State1} = expr(Expr, State),
    {Arms1, State2} = arms(Arms, Expr1, State1),
    {ID, State3} = new_value({match, Expr1, Arms1}, State2),
    {ID, unify_each(ID, [E || {_, E} <- Arms1], State3)};
expr({'if', Cond, True, False}, State) ->
    {[Cond1, True1, False1], State1} = exprs([Cond, True, False], State),
    {ID, State2} = new_value({'if', Cond1, True1, False1}, State1),
    State3 = unify(Cond1, 'Bool', State2),
    State4 = unify_each(ID, [True1, False1], State3),
    {ID, State4};
expr({block, _, _}=Block, State = #s{vnames = Vars}) ->
    {{block, Stmts, Expr}, State1} = block(Block, State),
    {ID, State2} = new_value({block, Stmts, Expr}, State1),
    State3 = unify(ID, Expr, State2),
    {ID, State3#s{vnames = Vars}};
expr({fn, Name, Params, Return, Body}, State = #s{level=Level, access=OutAccess, gen=Gen}) ->
    {{fn, ID, Gen, Params1=[Closure|_], Return1}, State1} = declare_fn(Gen, Name, Params, Return, State),
    State2 = unify(ID, Closure, State1),
    {Fun, State3} = access_fn(ID, Gen, Params1, Return1, State2),

    {Body1, State4 = #s{access = Access, values=Values, fns=Fns}} =
        make_body([], [], [Name|[N||{N,_}<-Params]], Params1, Return1, Body,
                  State3#s{level=Level+1, access=#{}}),

    Acc = maps:to_list(Access),
    Free = [K || {K, _} <- Acc],
    Access1 = maps:merge(OutAccess, maps:from_list([{K, L} || {K, L} <- Acc, L < Level])),

    Fn = {fn, ID, Free, Gen, Params1, Return1, Body1},
    {ID,
     State4#s{
       values = Values#{ID => {closure, Fun, ID}},
       fns = [Fn|Fns],
       level = Level,
       access = Access1}}.

setelements(_, [], _, State) ->
    {[], State};
setelements(Index, [Expr|T], Array, State) ->
    {Index1, State1} = expr({literal, 'Int', Index}, State),
    State2 = unify(Array, {array, Expr}, State1),
    {H1, State3} = new_stmt({assign, Array, Index1, Expr}, State2),
    {T1, State4} = setelements(Index+1, T, Array, State3),
    {[H1|T1], State4}.


arms([], _Match, State) ->
    {[], State};
arms([H|T], Match, State) ->
    {H1, State1} = arm(H, Match, State),
    {T1, State2} = arms(T, Match, State1),
    {[H1|T1], State2}.

arm({Pattern, Expr}, Match, State=#s{vnames = Vars}) ->
    {Pattern1, State1} = pattern(Pattern, [], Match, State),
    {Expr1, State2} = expr(Expr, State1),
    {{Pattern1, Expr1}, State2#s{vnames = Vars}}.

pattern({literal, _, _}=Expr, Acc, Match, State) ->
    {Expr1, State1} = expr(Expr, State),
    {Match1, State2} = access_value(Match, State1),
    {Cond, State3} = new_value({op, {cmp, '=='}, [Expr1, Match1]}, State2),
    {[{'if', Cond}|Acc], op(cmp, Cond, Expr1, Match1, State3)};
pattern('_', Acc, _, State) ->
    {Acc, State};
pattern({var, Name}, Acc, Match, State = #s{level=Level, vnames=Names}) ->
    false = maps:is_key(Name, Names),
    Names1 = Names#{Name => {Level, Match}},
    {Acc, State#s{vnames=Names1}};
pattern({tuple, List}, Acc, Match, State) ->
    {Match1, State1} = access_value(Match, State),
    {Vars, Acc1, State2} = patterns(List, Acc, State1),
    State3 = unify({tuple, Vars}, Match, State2),
    {[{destruct, 0, Vars, Match1}|Acc1], State3};
pattern({enum, Name, Variant, ['_']}, Acc, Match, State) ->
    {_, Cond, _, State1} = pattern_enum(Name, Variant, Match, State),
    {[{'if', Cond}|Acc], State1};
pattern({enum, Name, Variant, Args}, Acc, Match, State) ->
    {Index, Cond, Params, State1} = pattern_enum(Name, Variant, Match, State),
    {Match1, State2} = access_value(Match, State1),
    {Match2, State3} = new_value({op, {cast, down, Index}, [Match1]}, State2),
    {Vars, Acc1, State4} = patterns(Args, Acc, State3),
    State5 = unify_each({tuple, ['Int'|Vars]}, [Match2, Params], State4),
    {[{'if', Cond}, {destruct, 1, Vars, Match2}|Acc1], State5}.

patterns([], Acc, State) ->
    {[], Acc, State};
patterns([H|T], Acc, State) ->
    {ID, State1} = new_id(State),
    {Acc1, State2} = pattern(H, Acc, ID, State1),
    {Tail, Acc2, State3} = patterns(T, Acc1, State2),
    {[ID|Tail], Acc2, State3}.

pattern_enum(Name, Variant, Match, State) ->
    {ID, Gen, Index, Params, State1} = variant(Name, Variant, State),
    State2 = unify(Match, {typedef, ID, Gen}, State1),
    {Match1, State3} = access_value(Match, State2),
    {Dis, State4} = new_value({op, {load, tag}, [Match1]}, State3),
    State5 = unify(Dis, 'Int', State4),
    {Expr1, State6} = expr({literal, 'Int', Index}, State5),
    {Cond, State7} = new_value({op, {cmp, '=='}, [Expr1, Dis]}, State6),
    {Index, Cond, Params, op(cmp, Cond, Expr1, Dis, State7)}.

variant('_', Variant, State = #s{dnames = Names}) ->
    #{Variant := {ID, Gen, Index, Params}} = Names,
    variant(ID, Gen, Index, Params, State);
variant(Name, Variant, State = #s{tnames = Names, typedefs = Defines}) ->
    #{Name := {typedef, ID, _}} = Names,
    #{ID := {enum, Gen, Variants}} = Defines,
    {Index, Params} = lookup_index(0, Variant, Variants),
    variant(ID, Gen, Index, Params, State).

variant(ID, Gen, Index, Params, State) ->
    {Gen1, Map, State1 = #s{types = Types}} = new_instance(Gen, State),
    Params1 = mmb_type:bind({tuple, ['Int'|Params]}, Map, Types),
    {ID, Gen1, Index, Params1, State1}.

lookup_index(Index, Name, [{Name, Value}|_Rest]) ->
    {Index, Value};
lookup_index(Index, Name, [_|Rest]) ->
    lookup_index(Index + 1, Name, Rest).

fields([], _, _, State) ->
    {[], State};
fields([H|T], Map, Body, State) ->
    {H1, State1} = field(H, Map, Body, State),
    {T1, State2} = fields(T, Map, Body, State1),
    {[H1|T1], State2}.

field({Name, Type}, Map, Body, State = #s{types = Types}) ->
    Type1 = mmb_type:bind(Type, Map, Types),
    #{Name := Expr} = Body,
    {Expr1, State1} = expr(Expr, State),
    {Expr1, unify(Expr1, Type1, State1)}.

closure(FunID, Gen, Params, Return, State) ->
    {Gen1, Map, State1 = #s{types = Types}} = new_instance(Gen, State),
    Type = {closure, Params1, Return1} =
        mmb_type:bind({closure, Params, Return}, Map, Types),
    {Fun, State2} = access_fn(FunID, Gen1, [Type|Params1], Return1, State1),
    {Type, {closure, Fun, FunID}, State2}.

access_fn(FunID, Gen, Params, Return, State) ->
    expr({literal, {fn, Params, Return}, {fn, FunID, Gen}}, State).

new_instance(Gen, State) ->
    {Gen1, State1} = new_vars(Gen, State),
    {Gen1, mmb_type:gen_map(Gen, Gen1), State1}.

new_id(State = #s{count = Count}) ->
    {Count, State#s{count = Count + 1}}.

new_var(Name, State) ->
    {ID, State1 = #s{level = Level, vnames = Names}} = new_id(State),
    {ID, State1#s{vnames = Names#{Name => {Level, ID}}}}.

new_vars([], State) ->
    {[], State};
new_vars(['_'|T], State) ->
    {ID, State1} = new_id(State),
    {T1, State2} = new_vars(T, State1),
    {[ID|T1], State2};
new_vars([H|T], State) ->
    {H1, State1} = new_var(H, State),
    {T1, State2} = new_vars(T, State1),
    {[H1|T1], State2}.

new_value(Value, State) ->
    {ID, State1 = #s{values = Values}} = new_id(State),
    {ID, State1#s{values = Values#{ID => Value}}}.

new_stmt(Value, State) ->
    {ID, State1} = new_value(Value, State),
    {ID, unify(ID, 'Unit', State1)}.

access_var(Name, State = #s{vnames = Names, level = Current, access = Access}) ->
    case Names of
        #{Name := Var} ->
            case Var of
                {Level, ID} when Level < Current ->
                    {ID, State#s{access = Access#{ID => Level}}};
                {_, ID} ->
                    {ID, State}
            end;
        _ ->
            error
    end.

unify_each(E, List, State=#s{types=Types}) ->
    State#s{types=unify_each_(E, List, Types)}.

unify_each_(_, [], Types) ->
    Types;
unify_each_(E, [H|T], Types) ->
    unify_each_(E, T, mmb_type:unify(E, H, Types)).

op(cmp, ID, LHS, RHS, State) ->
    unify(ID, 'Bool', unify(LHS, RHS, State));
op(arith, ID, LHS, RHS, State) ->
    unify_each(ID, [LHS, RHS], State);
op(bool, ID, LHS, RHS, State) ->
    unify_each('Bool', [LHS, RHS, ID], State).

op(arith, ID, V, State) ->
    unify(ID, V, State);
op(bool, ID, V, State) ->
    unify('Bool', ID, unify('Bool', V, State)).

unify(X, Y, State = #s{types = Types}) ->
    State#s{types = mmb_type:unify(X, Y, Types)}.

collect(State) ->
    {ID, State1} =
        expr(
          {'let', '_', 'Unit', {call, {var, <<"main">>}, []}},
          State#s{access=#{}, level=1}),
    {FunID,
     #s{count=Count, fns=Fns, values=Values, types=Types, typedefs=Typedefs,
        access=Access, depends=Depends}} =
        new_id(State1),

    List = maps:keys(Access),
    #{ID := {'let', Expr}} = Values,
    {Acc, _} = collect_list(List, [], #{}, Depends),
    Acc1 = filter(Acc, [], Values),
    Fn = {fn, FunID, none, [], [], ID, {block, Acc1, Expr}},
    {Count, [Fn|[expand_fn(F, Depends, Values) || F <- Fns]], Values, Types, Typedefs}.

collect_list([], Acc, Done, _Depends) ->
    {Acc, Done};
collect_list([H|T], Acc, Done, Depends) ->
    {Acc1, Done1} = collect(H, Acc, Done, Depends),
    collect_list(T, Acc1, Done1, Depends).

collect(ID, Acc, Done, Depends) ->
    #{ID := List} = Depends,
    case Done of
        #{ID := _} ->
            {Acc, Done};
        _ ->
            {Acc1, Done1} = collect_list(List, Acc, Done, Depends),
            {[ID|Acc1], Done1#{ID => []}}
    end.

filter([], Acc, _) ->
    Acc;
filter([H|T], Acc, Values) ->
    #{H := Value} = Values,
    case Value of
        {alias, _} ->
            filter(T, [H|Acc], Values);
        _ ->
            filter(T, Acc, Values)
    end.

expand_fn({fn, ID, Free, Gen, Params, Return, Body}, Depends, Values) ->
    Free1 = expand_free(Free, #{}, Depends, Values),
    {fn, ID, Free1, Gen, Params, Return, Body}.

expand_free([], _, _, _) ->
    [];
expand_free([H|T], Done, Depends, Values) ->
    case Done of
        #{H := _} ->
            expand_free(T, Done, Depends, Values);
        _ ->
            case Depends of
                #{H := List} ->
                    T1 = expand_free(append(List, T), Done#{H => []}, Depends, Values),
                    #{H := Value} = Values,
                    case Value of
                        {alias, _} ->
                            [H|T1];
                        _ ->
                            T1
                    end;
                _ ->
                    [H|expand_free(T, Done#{H => []}, Depends, Values)]
            end
    end.


append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].
