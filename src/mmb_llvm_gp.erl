%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_llvm_gp).

-export([convert/1]).

-include("mmb_ssa.hrl").

-record(info, {srcs, dsts, doms, inputs, phis, locals, antics=#{}, avails=#{}, antics_back=#{}}).

convert(SSA) ->
    Fns = mmb_ssa:collect_fns(SSA),
    convert(maps:to_list(Fns), SSA).

convert([], SSA) ->
    SSA;
convert([H|T], SSA) ->
    convert(T, convert_fn(H, SSA)).

convert_fn({ID, []}, SSA) when is_atom(ID) ->
    SSA;
convert_fn({ID, Blocks}, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    #{ID := {fn, Free, Params, ReturnType, Entry, _}} = Nodes,
    SrcMap = mmb_ssa:collect_src(Blocks, Nodes),
    PhiMap = mmb_ssa:collect_phi(Blocks, Nodes),
    case Free of
        none ->
            Queue = mmb_queue:init(),
            Context = mmb_llvm_compute:init(),
            {_, Queue1, Context3} = create_vars(Params, Entry, Queue, Context, Nodes),
            SSA1 = SSA;
        _ ->
            {_, Queue, Context} = create_vars(Free, Entry, mmb_queue:init(), mmb_llvm_compute:init(), Nodes),
            {[Closure|_], Queue1, Context1} = create_vars(Params, Entry, Queue, Context, Nodes),
            ParamTypes = mmb_ssa:types(Params, Nodes),
            {FnType, SSA1} = mmb_ssa:typeid({fn, ParamTypes, ReturnType}, SSA),
            {FnID, Context2} = mmb_llvm_compute:add_value({const, FnType, {fn, ID}}, Context1),
            Context3 = mmb_llvm_compute:bind_value({eval, FnType, {op, {load, tag}, [Closure]}}, FnID, Context2)
    end,

    DomMap = collect_doms(
               [{Y, X} || {X, L} <- mmb_ssa_dom:doms(Blocks, Nodes),
                          Y <- L], #{}),
    {List, Queue2, Context4} = collect_blocks(Blocks, SrcMap, DomMap, PhiMap, Nodes, Queue1, Context3),
    BlockMap = maps:from_list(List),
    {BlockMap1, Context5} = resolve_blocks_phis(Blocks, BlockMap, Nodes, Context4),
    {BlockMap2, Context6} = propagate(Queue2, BlockMap1, Context5),
    ValuePhis = maps:from_list(resolve_value_phis(Blocks, BlockMap2, Nodes, Context6)),
    ValueMap =
        case Free of
            none ->
                #{};
            _ ->
                bind_vars(Free, Context6, Nodes, #{})
        end,
    ValueMap1 = bind_vars(Params, Context6, Nodes, ValueMap),

    {_, SSA2} = rebuild_blocks(Blocks, ValuePhis, BlockMap2, Context6, ValueMap1, #{}, SSA1),
    SSA2.

collect_doms([], Map) ->
    Map;
collect_doms([{X, Y}|T], Map) ->
    M = maps:get(X, Map, #{}),
    M1 = M#{Y => []},
    collect_doms(T, Map#{X => M1}).


collect_blocks([], _, _, _, _, Queue, Context) ->
    {[], Queue, Context};
collect_blocks([H|T], SrcMap, DomMap, PhiMap, Nodes, Queue, Context) ->
    {H1, Queue1, Context1} = collect_block(H, SrcMap, DomMap, PhiMap, Nodes, Queue, Context),
    {T1, Queue2, Context2} = collect_blocks(T, SrcMap, DomMap, PhiMap, Nodes, Queue1, Context1),
    {[{H, H1}|T1], Queue2, Context2}.


collect_block(ID, SrcMap, DomMap, PhiMap, Nodes, Queue, Context) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Srcs = maps:get(ID, SrcMap, []),
    Dsts = collect_dsts(Output),
    case Input of
        [] ->
            Phis = [];
        _ ->
            #{ID := Phis} = PhiMap
    end,
    {Input1, Queue1, Context1} = create_vars(Input, ID, Queue, Context, Nodes),
    {Locals, Queue2, Context2} = collect_values(Stmts, ID, Nodes, #{}, Queue1, Context1),
    {#info{srcs=Srcs,
           dsts=Dsts,
           doms=maps:get(ID, DomMap, #{}),
           inputs=Input1,
           phis=maps:from_list(Phis),
           locals=Locals}, Queue2, Context2}.

collect_dsts(none) ->
    [];
collect_dsts({ExitID, _}) ->
    [ExitID];
collect_dsts({'if', _, {True, _}, {False, _}}) ->
    [True, False].

collect_values([], _, _, Locals, Queue, Context) ->
    {Locals, Queue, Context};
collect_values([H|T], BlockID, Nodes, Locals, Queue, Context) ->
    {Locals1, Queue1, Context1} = collect_value(H, BlockID, Nodes, Locals, Queue, Context),
    collect_values(T, BlockID, Nodes, Locals1, Queue1, Context1).

collect_value({'let', Var}, BlockID, Nodes, Locals, Queue, Context) ->
    #{Var := {var, Type, Expr}} = Nodes,
    Locals1 =
        case mmb_llvm_compute:eval(Type, Expr, Nodes, Context) of
            none ->
                {ValueID, Context1} = mmb_llvm_compute:add_value({var, Type, Var}, Context),
                Queue2 = mmb_queue:push({avail, BlockID, ValueID}, Queue),
                Locals#{ValueID => []};
            {ValueID, Context1} ->
                case mmb_llvm_compute:is_eval(ValueID, Context1) of
                    false ->
                        Queue2 = Queue,
                        Locals;
                    true ->
                        List = mmb_llvm_compute:uses(ValueID, Context1),
                        Queue1 = mmb_queue:push({avail, BlockID, ValueID}, Queue),
                        case has_locals(List, Locals) of
                            true ->
                                Queue2 = Queue1,
                                Locals#{ValueID => []};
                            _ ->
                                Queue2 = mmb_queue:push({antic, BlockID, ValueID}, Queue1),
                                Locals
                        end
                end
        end,
    Context3 = mmb_llvm_compute:set_var(Var, ValueID, Context1),
    {Locals1, Queue2, Context3};
collect_value(_, _, _, Locals, Queue, Context) ->
    {Locals, Queue, Context}.


has_locals([], _) ->
    false;
has_locals([H|T], Locals) ->
    maps:is_key(H, Locals) orelse has_locals(T, Locals).

create_vars([], _, Queue, Context, _) ->
    {[], Queue, Context};
create_vars([H|T], BlockID, Queue, Context, Nodes) ->
    {H1, Queue1, Context1} = create_var(H, BlockID, Queue, Context, Nodes),
    {T1, Queue2, Context2} = create_vars(T, BlockID, Queue1, Context1, Nodes),
    {[H1|T1], Queue2, Context2}.

create_var(Var, BlockID, Queue, Context, Nodes) ->
    #{Var := {var, Type, _}} = Nodes,
    {ValueID, Context1} = mmb_llvm_compute:add_value({var, Type, Var}, Context),
    {ValueID,
     mmb_queue:push({avail, BlockID, ValueID}, Queue),
     mmb_llvm_compute:set_var(Var, ValueID, Context1)}.

resolve_blocks_phis([], BlockMap, _Nodes, Context) ->
    {BlockMap, Context};
resolve_blocks_phis([H|T], BlockMap, Nodes, Context) ->
    {BlockMap1, Context1} = resolve_block_phis(H, BlockMap, Nodes, Context),
    resolve_blocks_phis(T, BlockMap1, Nodes, Context1).

resolve_block_phis(ID, BlockMap, Nodes, Context) ->
    #{ID := Info = #info{srcs=Srcs, inputs=Input, phis=Phis}} = BlockMap,
    case Input of
        [] ->
            {BlockMap, Context};
        _ ->
            {Phis1, Context1} = resolve_block_phis(Srcs, #{}, Input, Phis, Nodes, Context),
            BlockMap1 = BlockMap#{ID => Info#info{phis = Phis1}},
            {BlockMap1, Context1}
    end.


resolve_block_phis([], Acc, _, _, _, Context) ->
    {Acc, Context};
resolve_block_phis([H|T], Acc, Input, Phis, Nodes, Context) ->
    {Acc1, Context1} = resolve_block_phi(H, Acc, Input, Phis, Nodes, Context),
    resolve_block_phis(T, Acc1, Input, Phis, Nodes, Context1).

resolve_block_phi(Src, Acc, Input, Phis, Nodes, Context) ->
    #{Src := List} = Phis,
    {List1, Context1}= mmb_llvm_compute:resolve_vars(List, Nodes, Context),
    {Acc#{Src => build_phi_map(Input, List1, #{})}, Context1}.

build_phi_map([], [], Acc) ->
    Acc;
build_phi_map([H1|T1], [H2|T2], Acc) ->
    build_phi_map(T1, T2, Acc#{H1 => H2}).


propagate(Queue, BlockMap, Context) ->
    case mmb_queue:pop(Queue) of
        none ->
            {BlockMap, Context};
        {Entry, Queue1} ->
            {Queue2, BlockMap1, Context1} = propagate(Entry, Queue1, BlockMap, Context),
            propagate(Queue2, BlockMap1, Context1)
    end.

propagate({avail, BlockID, ValueID}, Queue, BlockMap, Context) ->
    #{BlockID := Info = #info{avails = Avails, dsts=Dsts, doms=Doms}} = BlockMap,
    if is_map_key(ValueID, Avails) ->
            {Queue, BlockMap, Context};
        true ->
            Avails1 = Avails#{ValueID => []},
            BlockMap1 = BlockMap#{BlockID => Info#info{avails = Avails1}},
            Queue1 = propagate_avail(maps:keys(Doms), ValueID, Queue),
            Queue2 = propagate_avail(Dsts, ValueID, Queue1, BlockMap1),
            {Queue2, BlockMap1, Context}
    end;
propagate({antic, BlockID, ValueID}, Queue, BlockMap, Context) ->
    #{BlockID := #info{dsts=Dsts, antics = Antics, locals=Locals}} = BlockMap,
    if is_map_key(ValueID, Locals);
       is_map_key(ValueID, Antics) ->
            {Queue, BlockMap, Context};
       true ->
            {Queue1, BlockMap1, Context1} =
                case Dsts of
                    [_] ->
                        {Queue, BlockMap, Context};
                    _ ->
                        propagate({avail, BlockID, ValueID}, Queue, BlockMap, Context)
                end,
            #{BlockID := Info = #info{srcs = Srcs, phis=Phis}} = BlockMap1,
            Antics1 = Antics#{ValueID => []},
            List = mmb_llvm_compute:uses(ValueID, Context1),
            case has_locals(List, Locals) of
                true ->
                    Locals1 =
                        case Dsts of
                            [_] ->
                                Locals;
                            _ ->
                                Locals#{ValueID => []}
                        end,
                    Info1 = Info#info{locals=Locals1, antics=Antics},
                    BlockMap2 = BlockMap1#{BlockID => Info1},
                    {Queue1, BlockMap2, Context1};
                false ->
                    {Backs, Phis1, Context2} = phi_backs(Srcs, ValueID, Phis, Context1),
                    Info1 = Info#info{phis=Phis1, antics=Antics1},
                    BlockMap2 = BlockMap1#{BlockID => Info1},
                    {Queue2, BlockMap3} = propagate_antics(Backs, BlockID, Queue1, BlockMap2),
                    {Queue2, BlockMap3, Context2}
            end
    end.


propagate_avail([], _, Queue) ->
    Queue;
propagate_avail([H|T], ValueID, Queue) ->
    Queue1 = mmb_queue:push({avail, H, ValueID}, Queue),
    propagate_avail(T, ValueID, Queue1).

propagate_avail([], _, Queue, _) ->
    Queue;
propagate_avail([H|T], ValueID, Queue, BlockMap) ->
    #{H := #info{srcs=Srcs, doms=Doms}} = BlockMap,
    List = [ID|| ID <- Srcs, not maps:is_key(ID, Doms)],
    Queue1 =
        case is_all_avails(List, ValueID, BlockMap) of
            true ->
                mmb_queue:push({avail, H, ValueID}, Queue);
            false ->
                Queue
        end,
    propagate_avail(T, ValueID, Queue1, BlockMap).


is_all_avails([], _, _) ->
    true;
is_all_avails([H|T], ValueID, BlockMap) ->
    #{H := #info{avails=Avails}} = BlockMap,
    maps:is_key(ValueID, Avails) andalso is_all_avails(T, ValueID, BlockMap).

phi_backs([], _, Phis, Context) ->
    {[], Phis, Context};
phi_backs([H|T], ValueID, Phis, Context) ->
    {H1, Phis1, Context1} = phi_back(H, ValueID, Phis, Context),
    {T1, Phis2, Context2} = phi_backs(T, ValueID, Phis1, Context1),
    {[{H, H1}|T1], Phis2, Context2}.

phi_back(BlockID, ValueID, Phis, Context) ->
    Phi = maps:get(BlockID, Phis, #{}),
    {ValueID1, Phi1, Context1} = mmb_llvm_compute:phi_back(ValueID, Phi, Context),
    {ValueID1, Phis#{BlockID => Phi1}, Context1}.

propagate_antics([], _, Queue, BlockMap) ->
    {Queue, BlockMap};
propagate_antics([H|T], BlockID, Queue, BlockMap) ->
    {Queue1, BlockMap1} = propagate_antic(H, BlockID, Queue, BlockMap),
    propagate_antics(T, BlockID, Queue1, BlockMap1).

propagate_antic({SrcID, ValueID}, DstID, Queue, BlockMap) ->
    #{SrcID := Info = #info{dsts=Dsts, antics_back=Backs}} = BlockMap,
    Back = maps:get(DstID, Backs, #{}),
    Backs1 = Backs#{DstID => Back#{ValueID => []}},
    BlockMap1 = BlockMap#{SrcID => Info#info{antics_back=Backs1}},
    Queue1 =
        case is_all_antics(Dsts, ValueID, Backs1) of
            true ->
                mmb_queue:push({antic, SrcID, ValueID}, Queue);
            false ->
                Queue
        end,
    {Queue1, BlockMap1}.

is_all_antics([], _, _) ->
    true;
is_all_antics([H|T], ValueID, Backs) ->
    maps:is_key(ValueID, maps:get(H, Backs, #{})) andalso is_all_antics(T, ValueID, Backs).

resolve_value_phis([], _BlockMap, _, _) ->
    [];
resolve_value_phis([H|T], BlockMap, Nodes, Context) ->
    H1 = resolve_value_phi(H, BlockMap, Nodes, Context),
    T1 = resolve_value_phis(T, BlockMap, Nodes, Context),
    [{H, H1}|T1].

resolve_value_phi(BlockID, BlockMap, Nodes, Context) ->
    #{BlockID := {bb, Input, _, _}} = Nodes,
    #{BlockID := #info{srcs=Srcs, phis=Phis, avails=Avails, locals=Locals}} = BlockMap,
    case Srcs of
        [] ->
            [];
        _ ->
            ValueMap = bind_vars(Input, Context, Nodes, #{}),
            Avails1 = maps:without(maps:keys(Locals), Avails),
            Avails2 = maps:without(maps:keys(ValueMap), Avails1),

            List = maps:keys(Avails2),
            tsort([ ID || ID <- List,
                          has_any_phis(Srcs, ID, Phis),
                          has_any_avail(Srcs, ID, Phis, BlockMap)
                  ],
                  #{},
                  Avails2,
                  Context)
    end.

has_any_phis([], _, _) ->
    false;
has_any_phis([H|T], ID, Phis) ->
    maps:is_key(ID, maps:get(H, Phis, #{})) orelse has_any_phis(T, ID, Phis).

has_any_avail([], _, _, _) ->
    false;
has_any_avail([H|T], ID, Phis, BlockMap) ->
    has_avail(H, maps:get(ID, maps:get(H, Phis, #{}), ID), BlockMap) orelse has_any_avail(T, ID, Phis, BlockMap).

has_avail(BlockID, ValueID, BlockMap) ->
    #{BlockID := #info{avails=Avails}} = BlockMap,
    maps:is_key(ValueID, Avails).

rebuild_blocks([], _ValuePhis, _BlockMap, _Context, _ValueMap, Done, SSA) ->
    {Done, SSA};
rebuild_blocks([H|T], ValuePhis, BlockMap, Context, ValueMap, Done, SSA) when is_map_key(H, Done) ->
    rebuild_blocks(T, ValuePhis, BlockMap, Context, ValueMap, Done, SSA);
rebuild_blocks([H|T], ValuePhis, BlockMap, Context, ValueMap, Done, SSA) ->
    {Done1, SSA1} = rebuild_block(H, ValuePhis, BlockMap, Context, ValueMap, Done, SSA),
    rebuild_blocks(T, ValuePhis, BlockMap, Context, ValueMap, Done1, SSA1).

rebuild_block(BlockID, ValuePhis, BlockMap, Context, ValueMap, Done, SSA = #ssa{nodes=Nodes}) ->
    #{BlockID := ValuePhi} = ValuePhis,
    #{BlockID := #info{srcs=Srcs, dsts=Dsts, locals=Locals, avails=Avails}} = BlockMap,
    #{BlockID := {bb, Input, Output, Stmts}} = Nodes,

    Avails1 = maps:without(maps:keys(Locals), Avails),
    ValueMap1 = maps:with(maps:keys(Avails1), ValueMap),

    {Input1, ValueMap2, SSA1} = add_value_phis(ValuePhi, Input, Context, Nodes, ValueMap1, SSA),


    Avails2 = maps:keys(maps:without(maps:keys(ValueMap2), Avails1)),
    Avails3 =
        case Srcs of
            [] ->
                [X || X <- Avails2, not mmb_llvm_compute:is_var(X, Context)];
            _ ->
                Avails2
        end,


    Avails4 = tsort(Avails3, #{}, maps:from_list([{X, []} || X <- Avails3]), Context),

    {Stmts1, ValueMap3, SSA2} = rebuild_stmts(Avails4, Stmts, Locals, Context, ValueMap2, SSA1),
    {Output1, ValueMap4, SSA3} = rebuild_output(Output, ValuePhis, BlockID, BlockMap, Context, ValueMap3, SSA2),
    #ssa{nodes=Nodes1} = SSA3,
    Nodes2 = Nodes1#{BlockID => {bb, Input1, Output1, Stmts1}},
    SSA4 = SSA3#ssa{nodes=Nodes2},
    Done1 = Done#{BlockID => []},
    rebuild_blocks(Dsts, ValuePhis, BlockMap, Context, ValueMap4, Done1, SSA4).


rebuild_output(none, _, _, _, _, ValueMap, SSA) ->
    {none, ValueMap, SSA};
rebuild_output({ExitID, Vars}, ValuePhis, BlockID, BlockMap, Context, ValueMap, SSA) ->
    {Vars1, ValueMap1, SSA1} = rebuild_var_list(Vars, Context, ValueMap, SSA),
    #{ExitID := ValuePhi} = ValuePhis,
    #{ExitID := #info{phis = Phis}} = BlockMap,
    Phi = maps:get(BlockID, Phis, #{}),
    ValuePhi1 = [maps:get(ID, Phi, ID) || ID <- ValuePhi],
    case [ID || ID <- ValuePhi1, not has_avail(BlockID, ID, BlockMap) ] of
        [] ->
            {ValuePhi2, ValueMap2, SSA2} = rebuild_ref_list(ValuePhi1, Context, ValueMap1, SSA1),
            Vars2 = append(ValuePhi2, Vars1),
            {{ExitID, Vars2}, ValueMap2, SSA2};
        NotAvail ->
            NotAvail1 = tsort(NotAvail, #{}, maps:from_list([{ID, []} || ID <- NotAvail]), Context),
            {Stmts, ValueMap2, SSA2} = rebuild_values(NotAvail1, Context, ValueMap1, SSA1),
            {ValuePhi2, _ValueMap3, SSA3} = rebuild_ref_list(ValuePhi1, Context, ValueMap2, SSA2),
            Vars2 = append(ValuePhi2, Vars1),
            {NewBlockID, SSA4} = mmb_ssa:add_node({bb, [], {ExitID, Vars2}, Stmts}, SSA3),
            {{NewBlockID, []}, ValueMap1, SSA4}
    end;
rebuild_output({'if', Cond, True, False}, ValuePhis, BlockID, BlockMap, Context, ValueMap, SSA) ->
    {Cond1, ValueMap1, SSA1} = rebuild_var(Cond, Context, ValueMap, SSA),
    {True1, ValueMap2, SSA2} = rebuild_output(True, ValuePhis, BlockID, BlockMap, Context, ValueMap1, SSA1),
    {False1, ValueMap3, SSA3} = rebuild_output(False, ValuePhis, BlockID, BlockMap, Context, ValueMap2, SSA2),
    {{'if', Cond1, True1, False1}, ValueMap3, SSA3}.


rebuild_stmts([], Stmts, Locals, Context, ValueMap, SSA) ->
    rebuild_stmts(Stmts, Locals, Context, ValueMap, SSA);
rebuild_stmts([H|T], Stmts, Locals, Context, ValueMap, SSA) ->
    {H1, ValueMap1, SSA1} = rebuild_value(H, Context, ValueMap, SSA),
    {T1, ValueMap2, SSA2} = rebuild_stmts(T, Stmts, Locals, Context, ValueMap1, SSA1),
    {[H1|T1], ValueMap2, SSA2}.

rebuild_stmts([], Locals, Context, ValueMap, SSA) ->
    Locals1 = tsort(maps:keys(Locals), #{}, Locals, Context),
    rebuild_values(Locals1, Context, ValueMap, SSA);
rebuild_stmts([{'let', Var}|T], Locals, Context, ValueMap, SSA = #ssa{nodes=Nodes}) ->
    ValueID = mmb_llvm_compute:get_var(Var, Context),
    case ValueMap of
        #{ValueID := _} ->
            rebuild_stmts(T, Locals, Context, ValueMap, SSA);
        _ ->
            case mmb_llvm_compute:get_value(ValueID, Context) of
                {const, _, _} ->
                    rebuild_stmts(T, Locals, Context, ValueMap, SSA);
                _ ->
                    #{Var := {var, Type, Expr}} = Nodes,
                    {[Expr1|T1], ValueMap1, SSA1} = rebuild_stmts([Expr|T], maps:remove(ValueID, Locals), Context, ValueMap#{ValueID => Var}, SSA),
                    SSA2 = mmb_ssa:set_node(Var, {var, Type, Expr1}, SSA1),
                    {[{'let', Var}|T1], ValueMap1, SSA2}
            end
    end;
rebuild_stmts([{op, Op, List}|T], Locals, Context, ValueMap, SSA) ->
    {List1, ValueMap1, SSA1} = rebuild_var_list(List, Context, ValueMap, SSA),
    {T1, ValueMap2, SSA2} = rebuild_stmts(T, Locals, Context, ValueMap1, SSA1),
    {[{op, Op, List1}|T1], ValueMap2, SSA2};
rebuild_stmts([{call, Fun, Args}|T], Locals, Context, ValueMap, SSA) ->
    {[Fun1|Args1], ValueMap1, SSA1} = rebuild_var_list([Fun|Args], Context, ValueMap, SSA),
    {T1, ValueMap2, SSA2} = rebuild_stmts(T, Locals, Context, ValueMap1, SSA1),
    {[{call, Fun1, Args1}|T1], ValueMap2, SSA2};
rebuild_stmts([{return, Expr}|T], Locals, Context, ValueMap, SSA) ->
    {ID, ValueMap1, SSA1} = rebuild_var(Expr, Context, ValueMap, SSA),
    {T1, ValueMap2, SSA2} = rebuild_stmts(T, Locals, Context, ValueMap1, SSA1),
    {[{return, ID}|T1], ValueMap2, SSA2};
rebuild_stmts([return|T], Locals, Context, ValueMap, SSA) ->
    {T1, ValueMap1, SSA1} = rebuild_stmts(T, Locals, Context, ValueMap, SSA),
    {[return|T1], ValueMap1, SSA1};
rebuild_stmts([fail|T], Locals, Context, ValueMap, SSA) ->
    {T1, ValueMap1, SSA1} = rebuild_stmts(T, Locals, Context, ValueMap, SSA),
    {[fail|T1], ValueMap1, SSA1}.


rebuild_var_list([], _, ValueMap, SSA) ->
    {[], ValueMap, SSA};
rebuild_var_list([H|T], Context, ValueMap, SSA) ->
    {H1, ValueMap1, SSA1} = rebuild_var(H, Context, ValueMap, SSA),
    {T1, ValueMap2, SSA2} = rebuild_var_list(T, Context, ValueMap1, SSA1),
    {[H1|T1], ValueMap2, SSA2}.

rebuild_var(Var, Context, ValueMap, SSA = #ssa{nodes=Nodes}) ->
    case Nodes of
        #{Var := {const, _, _}} ->
            {Var, ValueMap, SSA};
        _ ->
            ValueID = mmb_llvm_compute:get_var(Var, Context),
            rebuild_ref(ValueID, Context, ValueMap, SSA)
    end.

rebuild_values([], _, ValueMap, SSA) ->
    {[], ValueMap, SSA};
rebuild_values([H|T], Context, ValueMap, SSA) ->
    {H1, ValueMap1, SSA1} = rebuild_value(H, Context, ValueMap, SSA),
    {T1, ValueMap2, SSA2} = rebuild_values(T, Context, ValueMap1, SSA1),
    {[H1|T1], ValueMap2, SSA2}.

rebuild_value(ValueID, Context, ValueMap, SSA) ->
    {eval, Type, Expr} = mmb_llvm_compute:get_value(ValueID, Context),
    {Expr1, ValueMap1, SSA1} = rebuild_expr(Expr, Context, ValueMap, SSA),
    {ID, SSA2} = mmb_ssa:add_node({var, Type, Expr1}, SSA1),
    {{'let', ID}, ValueMap1#{ValueID => ID}, SSA2}.

rebuild_expr({op, Op, List}, Context, ValueMap, SSA) ->
    {List1, ValueMap1, SSA1} = rebuild_ref_list(List, Context, ValueMap, SSA),
    {{op, Op, List1}, ValueMap1, SSA1};
rebuild_expr({call, Fun, Args}, Context, ValueMap, SSA) ->
    {[Fun|Args], ValueMap1, SSA1} = rebuild_ref_list([Fun|Args], Context, ValueMap, SSA),
    {{call, Fun, Args}, ValueMap1, SSA1}.

rebuild_ref_list([], _, ValueMap, SSA) ->
    {[], ValueMap, SSA};
rebuild_ref_list([H|T], Context, ValueMap, SSA) ->
    {H1, ValueMap1, SSA1} = rebuild_ref(H, Context, ValueMap, SSA),
    {T1, ValueMap2, SSA2} = rebuild_ref_list(T, Context, ValueMap1, SSA1),
    {[H1|T1], ValueMap2, SSA2}.

rebuild_ref(ValueID, Context, ValueMap, SSA) ->
    case ValueMap of
        #{ValueID := ID} ->
            {ID, ValueMap, SSA};
        _ ->
            case mmb_llvm_compute:get_value(ValueID, Context) of
                {const, Type, Expr} ->
                    case Expr of
                        {op, Op, List} ->
                            {List1, ValueMap1, SSA1} = rebuild_ref_list(List, Context, ValueMap, SSA),
                            {ID, SSA2} = add_const({const, Type, {op, Op, List1}}, SSA1),
                            {ID, ValueMap1#{ValueID => ID}, SSA2};
                        _ ->
                            {ID, SSA1} = add_const({const, Type, Expr}, SSA),
                            {ID, ValueMap#{ValueID => ID}, SSA1}
                    end;
                {var, _, ID} ->
                    {ID, ValueMap#{ValueID => ID}, SSA}
            end
    end.

add_const(Const, SSA = #ssa{values=Values}) ->
    case Values of
        #{Const := ID} ->
            {ID, SSA};
        _ ->
            {ID, SSA1} = mmb_ssa:add_node(Const, SSA),
            Values1 = Values#{Const => ID},
            {ID, SSA1#ssa{values=Values1}}
    end.

tsort([], _, _, _) ->
    [];
tsort([H|T], Done, All, Context) ->
    case Done of
        #{H := _} ->
            tsort(T, Done, All, Context);
        _ ->
            List = mmb_llvm_compute:uses(H, Context),
            case [ID || ID <- List, maps:is_key(ID, All), not maps:is_key(ID, Done)] of
                [] ->
                    [H|tsort(T, Done#{H => []}, All, Context)];
                List1 ->
                    tsort(append(List1, [H|T]), Done, All, Context)
            end
    end.

append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].


add_value_phis([], Input, Context, Nodes, ValueMap, SSA) ->
    ValueMap1 = bind_vars(Input, Context, Nodes, ValueMap),
    {Input, ValueMap1, SSA};
add_value_phis([H|T], Input, Context, Nodes, ValueMap, SSA) ->
    {H1, ValueMap1, SSA1} = add_value_phi(H, Context, ValueMap, SSA),
    {T1, ValueMap2, SSA2} = add_value_phis(T, Input, Context, Nodes, ValueMap1, SSA1),
    {[H1|T1], ValueMap2, SSA2}.

add_value_phi(ValueID, Context, ValueMap, SSA) ->
    Type = mmb_llvm_compute:get_type(ValueID, Context),
    {ID, SSA1} = mmb_ssa:add_node({var, Type, phi}, SSA),
    {ID, ValueMap#{ValueID => ID}, SSA1}.

bind_vars([], _, _, ValueMap) ->
    ValueMap;
bind_vars([H|T], Context, Nodes, ValueMap) ->
    bind_vars(T, Context, Nodes, bind_var(H, Context, Nodes, ValueMap)).

bind_var(Var, Context, Nodes, ValueMap) ->
    #{Var := {var, Type, _}} = Nodes,
    ID = mmb_llvm_compute:get_value_id({var, Type, Var}, Context),
    ValueMap#{ID => Var}.
