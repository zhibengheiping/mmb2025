%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimref).

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
    SrcMap = mmb_ssa:collect_src(Blocks, Nodes),
    {Unsafe, Defined, Uses} = collect_blocks(Blocks, #{}, #{}, #{}, Nodes),
    List = [{Ref, BlockID}
            || {Ref, M} <- maps:to_list(Uses),
               not maps:is_key(Ref, Unsafe),
               BlockID <- maps:keys(M)],

    Defined1 =
        maps:from_list(
          [{Ref, BlockID}
           || {Ref, BlockID} <- maps:to_list(Defined),
              not maps:is_key(Ref, Unsafe)]),

    Uses1 = propagate({List, []}, #{}, Defined1, SrcMap),
    Refs = maps:keys(Defined1),

    {Rename, SSA1} = convert_blocks(Blocks, #{}, Refs, Defined1, Uses1, SSA),
    mmb_ssa:rename_blocks(Blocks, Rename, SSA1).

collect_blocks([], Unsafe, Defined, Uses, _) ->
    {Unsafe, Defined, Uses};
collect_blocks([H|T], Unsafe, Defined, Uses, Nodes) ->
    {Unsafe1, Defined1, Uses1} = collect_block(H, Unsafe, Defined, Uses, Nodes),
    collect_blocks(T, Unsafe1, Defined1, Uses1, Nodes).

collect_block(ID, Unsafe, Defined, Uses, Nodes) ->
    #{ID := {bb, _Input, _Output, Stmts}} = Nodes,
    collect_stmts(Stmts, Unsafe, Defined, Uses, ID, Nodes).

collect_stmts([], Unsafe, Defined, Uses, _, _) ->
    {Unsafe, Defined, Uses};
collect_stmts([H|T], Unsafe, Defined, Uses, BlockID, Nodes) ->
    {Unsafe1, Defined1, Uses1} = collect_stmt(H, Unsafe, Defined, Uses, BlockID, Nodes),
    collect_stmts(T, Unsafe1, Defined1, Uses1, BlockID, Nodes).

collect_stmt({'let', ID}, Unsafe, Defined, Uses, BlockID, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    case Expr of
        {op, {make, ref}, _} ->
            {Unsafe, Defined#{ID => BlockID}, Uses};
        _ ->
            collect_stmt(Expr, Unsafe, Defined, Uses, BlockID, Nodes)
    end;
collect_stmt({op, {load, ref}, [ID]}, Unsafe, Defined, Uses, BlockID, _Nodes) ->
    {Unsafe, Defined, mark_use(ID, BlockID, Uses)};
collect_stmt({op, {store, ref}, [_, ID]}, Unsafe, Defined, Uses, BlockID, _Nodes) ->
    {Unsafe, Defined, mark_use(ID, BlockID, Uses)};
collect_stmt(Stmt, Unsafe, Defined, Uses, _, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    Unsafe1 = mark_unsafe(List, Unsafe, Nodes),
    {Unsafe1, Defined, Uses}.

mark_use(ID, BlockID, Uses) ->
    U = maps:get(ID, Uses, #{}),
    U1 = U#{BlockID => []},
    Uses#{ID => U1}.

mark_unsafe([], Unsafe, _) ->
    Unsafe;
mark_unsafe([H|T], Unsafe, Nodes) ->
    case Nodes of
        #{H := {var, _, {op, {make, ref}, _}}} ->
            mark_unsafe(T, Unsafe#{H => []}, Nodes);
        _ ->
            mark_unsafe(T, Unsafe, Nodes)
    end.


propagate(Queue, Uses, Defined, SrcMap) ->
    case mmb_queue:pop(Queue) of
        none ->
            Uses;
        {{Ref, BlockID}, Queue1} ->
            case Defined of
                #{Ref := BlockID} ->
                    propagate(Queue1, Uses, Defined, SrcMap);
                _ ->
                    case maps:get(BlockID, Uses, #{}) of
                        #{Ref := _} ->
                            propagate(Queue1, Uses, Defined, SrcMap);
                        U ->
                            U1 = U#{Ref => []},
                            Uses1 = Uses#{BlockID => U1},
                            Queue2 = queue_srcs(maps:get(BlockID, SrcMap, []), Ref, Queue1),
                            propagate(Queue2, Uses1, Defined, SrcMap)
                    end
            end
    end.

queue_srcs([], _, Queue) ->
    Queue;
queue_srcs([H|T], Ref, Queue) ->
    queue_srcs(T, Ref, mmb_queue:push({Ref, H}, Queue)).


convert_blocks([], Rename, _Refs, _Defined, _Uses, SSA) ->
    {Rename, SSA};
convert_blocks([H|T], Rename, Refs, Defined, Uses, SSA) ->
    {Rename1, SSA1} = convert_block(H, Rename, Refs, Defined, Uses, SSA),
    convert_blocks(T, Rename1, Refs, Defined, Uses, SSA1).

convert_block(ID, Rename, Refs, Defined, Uses, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Usage = maps:get(ID, Uses, #{}),
    {Phi, RefMap, SSA1} = create_phis(Refs, Usage, SSA),
    {Stmts1, RefMap1, Rename1} = convert_stmts(Stmts, RefMap, Rename, Defined, Nodes),
    Output1 = convert_output(Output, Refs, RefMap1, Uses),
    {Rename1, mmb_ssa:set_node(ID, {bb, append(Phi, Input), Output1, Stmts1}, SSA1)}.

create_phis([], _, SSA) ->
    {[], #{}, SSA};
create_phis([H|T], Usage, SSA = #ssa{nodes=Nodes}) when is_map_key(H, Usage) ->
    #{H := {var, TypeID, _}} = Nodes,
    #{TypeID := {type, {ref, Type}}} = Nodes,
    {H1, SSA1} = mmb_ssa:add_node({var, Type, phi}, SSA),
    {T1, RefMap, SSA2} = create_phis(T, Usage, SSA1),
    {[H1|T1], RefMap#{H => H1}, SSA2};
create_phis([_|T], Usage, SSA) ->
    create_phis(T, Usage, SSA).


convert_stmts([], RefMap, Rename, _Defined, _Nodes) ->
    {[], RefMap, Rename};
convert_stmts([{'let', ID}=H|T], RefMap, Rename, Defined, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    case Expr of
        {op, {make, ref}, [Value]} when is_map_key(ID, Defined) ->
            convert_stmts(T, RefMap#{ID => Value}, Rename, Defined, Nodes);
        {op, {load, ref}, [Ref]} when is_map_key(Ref, RefMap) ->
            convert_stmts(T, RefMap, Rename#{ID => maps:get(Ref, RefMap)}, Defined, Nodes);
        _ ->
            {T1, RefMap1, Rename1} = convert_stmts(T, RefMap, Rename, Defined, Nodes),
            {[H|T1], RefMap1, Rename1}
    end;
convert_stmts([{op, {store, ref}, [Value, Ref]}|T], RefMap, Rename, Defined, Nodes) when is_map_key(Ref, RefMap) ->
    convert_stmts(T, RefMap#{Ref => Value}, Rename, Defined, Nodes);
convert_stmts([H|T], RefMap, Rename, Defined, Nodes) ->
    {T1, RefMap1, Rename1} = convert_stmts(T, RefMap, Rename, Defined, Nodes),
    {[H|T1], RefMap1, Rename1}.

convert_output(none, _, _, _) ->
    none;
convert_output({ExitID, Values}, Refs, RefMap, Uses) ->
    Usage = maps:get(ExitID, Uses, #{}),
    {ExitID, append(convert_phis(Refs, Usage, RefMap), Values)};
convert_output({'if', Cond, True, False}, Refs, RefMap, Uses) ->
    True1 = convert_output(True, Refs, RefMap, Uses),
    False1 = convert_output(False, Refs, RefMap, Uses),
    {'if', Cond, True1, False1}.

convert_phis([], _, _) ->
    [];
convert_phis([H|T], Usage, RefMap) when is_map_key(H, Usage) ->
    #{H := H1} = RefMap,
    [H1|convert_phis(T, Usage, RefMap)];
convert_phis([_|T], Usage, RefMap) ->
    convert_phis(T, Usage, RefMap).


append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].
