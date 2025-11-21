%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_allphis).

-export([convert/1]).

-include("mmb_ssa.hrl").

convert(SSA) ->
    Fns = mmb_ssa:collect_fns(SSA),
    convert_fns(maps:to_list(Fns), SSA).

convert_fns([], SSA) ->
    SSA;
convert_fns([H|T], SSA) ->
    convert_fns(T, convert_fn(H, SSA)).

convert_fn({ID, []}, SSA) when is_atom(ID) ->
    SSA;
convert_fn({ID, Blocks}, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    #{ID := {fn, Free, Params, ReturnType, Entry, Exit}} = Nodes,
    Args =
        case Free of
            none ->
                Params;
            _ ->
                append(Free, Params)
        end,
    SrcMap = mmb_ssa:collect_src(Blocks, Nodes),
    Defined = collect_inputs(Args, #{}, fn, Nodes),

    {Defined1, Uses} = collect_blocks(Blocks, Defined, #{}, Nodes),
    List =
        [ {Var, BlockID}
          || {Var, M} <- maps:to_list(Uses),
             maps:is_key(Var, Defined1),
             BlockID <- maps:keys(M)],
    Uses1 = propagate({List, []}, #{}, Defined1, SrcMap),

    Vars = maps:keys(Defined1),
    SSA1 = convert_blocks(Blocks, Vars, Uses1, SSA),
    Usage = maps:get(Entry, Uses1, #{}),
    case maps:size(Usage) of
        0 ->
            SSA1;
        _ ->
            {Entry1, SSA2} = mmb_ssa:add_node({bb, [], {Entry, [V || V <- Vars, maps:is_key(V, Usage)]}, []}, SSA1),
            mmb_ssa:set_node(ID, {fn, Free, Params, ReturnType, Entry1, Exit}, SSA2)
    end.

collect_blocks([], Defined, Uses, _) ->
    {Defined, Uses};
collect_blocks([H|T], Defined, Uses, Nodes) ->
    {Defined1, Uses1} = collect_block(H, Defined, Uses, Nodes),
    collect_blocks(T, Defined1, Uses1, Nodes).

collect_block(ID, Defined, Uses, Nodes) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Defined1 = collect_inputs(Input, Defined, ID, Nodes),
    {Defined2, Uses1} = collect_stmts(Stmts, Defined1, Uses, ID, Nodes),
    Uses2 = collect_output(Output, Uses1, ID),
    {Defined2, Uses2}.

collect_output(none, Uses, _) ->
    Uses;
collect_output({_, Values}, Uses, BlockID) ->
    mark_uses(Values, BlockID, Uses);
collect_output({'if', Cond, True, False}, Uses, BlockID) ->
    Uses1 = mark_use(Cond, BlockID, Uses),
    Uses2 = collect_output(True, Uses1, BlockID),
    collect_output(False, Uses2, BlockID).

collect_inputs([], Defined, _, _) ->
    Defined;
collect_inputs([H|T], Defined, BlockID, Nodes) ->
    Defined1 = collect_input(H, Defined, BlockID, Nodes),
    collect_inputs(T, Defined1, BlockID, Nodes).

collect_input(ID, Defined, BlockID, Nodes) ->
    #{ID := {var, _, _}} = Nodes,
    Defined#{ID => BlockID}.

collect_stmts([], Defined, Uses, _, _) ->
    {Defined, Uses};
collect_stmts([H|T], Defined, Uses, BlockID, Nodes) ->
    {Defined1, Uses1} = collect_stmt(H, Defined, Uses, BlockID, Nodes),
    collect_stmts(T, Defined1, Uses1, BlockID, Nodes).

collect_stmt({'let', ID}, Defined, Uses, BlockID, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    Defined1 = Defined#{ID => BlockID},
    collect_stmt(Expr, Defined1, Uses, BlockID, Nodes);
collect_stmt(fail, Defined, Uses, _, _) ->
    {Defined, Uses};
collect_stmt(return, Defined, Uses, _, _) ->
    {Defined, Uses};
collect_stmt({return, Expr}, Defined, Uses, BlockID, _) ->
    {Defined, mark_use(Expr, BlockID, Uses)};
collect_stmt({op, _, List}, Defined, Uses, BlockID, _) ->
    {Defined, mark_uses(List, BlockID, Uses)};
collect_stmt({call, Fun, Args}, Defined, Uses, BlockID, _) ->
    {Defined, mark_uses([Fun|Args], BlockID, Uses)}.

mark_uses([], _, Uses) ->
    Uses;
mark_uses([H|T], BlockID, Uses) ->
    Uses1 = mark_use(H, BlockID, Uses),
    mark_uses(T, BlockID, Uses1).

mark_use(ID, BlockID, Uses) ->
    U = maps:get(ID, Uses, #{}),
    U1 = U#{BlockID => []},
    Uses#{ID => U1}.


propagate(Queue, Uses, Defined, SrcMap) ->
    case mmb_queue:pop(Queue) of
        none ->
            Uses;
        {{Var, BlockID}, Queue1} ->
            case Defined of
                #{Var := BlockID} ->
                    propagate(Queue1, Uses, Defined, SrcMap);
                _ ->
                    case maps:get(BlockID, Uses, #{}) of
                        #{Var := _} ->
                            propagate(Queue1, Uses, Defined, SrcMap);
                        U ->
                            U1 = U#{Var => []},
                            Uses1 = Uses#{BlockID => U1},
                            Queue2 = queue_srcs(maps:get(BlockID, SrcMap, []), Var, Queue1),
                            propagate(Queue2, Uses1, Defined, SrcMap)
                    end
            end
    end.

queue_srcs([], _, Queue) ->
    Queue;
queue_srcs([H|T], Var, Queue) ->
    queue_srcs(T, Var, mmb_queue:push({Var, H}, Queue)).


convert_blocks([], _Vars, _Uses, SSA) ->
    SSA;
convert_blocks([H|T], Vars, Uses, SSA) ->
    SSA1 = convert_block(H, Vars, Uses, SSA),
    convert_blocks(T, Vars, Uses, SSA1).

convert_block(ID, Vars, Uses, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Usage = maps:get(ID, Uses, #{}),
    {Phi, VarMap, SSA1} = create_phis(Vars, ID, Usage, SSA),
    VarMap1 = gather_inputs(Input, VarMap, Nodes),

    {Stmts1, VarMap2, SSA2} = convert_stmts(Stmts, VarMap1, SSA1),
    Output1 = convert_output(Output, Vars, VarMap2, Uses),
    mmb_ssa:set_node(ID, {bb, append(Phi, Input), Output1, Stmts1}, SSA2).


gather_inputs([], VarMap, _) ->
    VarMap;
gather_inputs([H|T], VarMap, Nodes) ->
    VarMap1 = gather_input(H, VarMap, Nodes),
    gather_inputs(T, VarMap1, Nodes).

gather_input(ID, VarMap, Nodes) ->
    #{ID := {var, _, _}} = Nodes,
    VarMap#{ID => ID}.

create_phis([], _, _, SSA) ->
    {[], #{}, SSA};
create_phis([H|T], BlockID, Usage, SSA = #ssa{nodes=Nodes}) when is_map_key(H, Usage) ->
    #{H := {var, Type, _}} = Nodes,
    {H1, SSA1} = mmb_ssa:add_node({var, Type, phi}, SSA),
    {T1, VarMap, SSA2} = create_phis(T, BlockID, Usage, SSA1),
    {[H1|T1], VarMap#{H => H1}, SSA2};
create_phis([_|T], BlockID, Usage, SSA) ->
    create_phis(T, BlockID, Usage, SSA).


convert_stmts([], VarMap, SSA) ->
    {[], VarMap, SSA};
convert_stmts([H|T], VarMap, SSA) ->
    {H1, VarMap1, SSA1} = convert_stmt(H, VarMap, SSA),
    {T1, VarMap2, SSA2} = convert_stmts(T, VarMap1, SSA1),
    {[H1|T1], VarMap2, SSA2}.

convert_stmt({'let', ID}, VarMap, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, Expr}} = Nodes,
    {Expr1, VarMap1, SSA1} = convert_stmt(Expr, VarMap, SSA),
    SSA2 = mmb_ssa:set_node(ID, {var, Type, Expr1}, SSA1),
    {{'let', ID}, VarMap1#{ID => ID}, SSA2};
convert_stmt(fail, VarMap, SSA) ->
    {fail, VarMap, SSA};
convert_stmt(return, VarMap, SSA) ->
    {return, VarMap, SSA};
convert_stmt({return, Expr}, VarMap, SSA) ->
    {{return, maps:get(Expr, VarMap, Expr)}, VarMap, SSA};
convert_stmt({op, Op, List}, VarMap, SSA) ->
    {{op, Op, [maps:get(X, VarMap, X) || X <- List]}, VarMap, SSA};
convert_stmt({call, Fun, Args}, VarMap, SSA) ->
    {{call, maps:get(Fun, VarMap, Fun), [maps:get(X, VarMap, X) || X <- Args]}, VarMap, SSA}.

convert_output(none, _, _, _) ->
    none;
convert_output({ExitID, Values}, Vars, VarMap, Uses) ->
    Usage = maps:get(ExitID, Uses, #{}),
    Values1 = [maps:get(X, VarMap, X) || X <- Values],
    {ExitID, append(convert_phis(Vars, Usage, VarMap), Values1)};
convert_output({'if', Cond, True, False}, Vars, VarMap, Uses) ->
    True1 = convert_output(True, Vars, VarMap, Uses),
    False1 = convert_output(False, Vars, VarMap, Uses),
    {'if', maps:get(Cond, VarMap, Cond), True1, False1}.

convert_phis([], _, _) ->
    [];
convert_phis([H|T], Usage, VarMap) when is_map_key(H, Usage) ->
    #{H := H1} = VarMap,
    [H1|convert_phis(T, Usage, VarMap)];
convert_phis([_|T], Usage, VarMap) ->
    convert_phis(T, Usage, VarMap).


append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].
