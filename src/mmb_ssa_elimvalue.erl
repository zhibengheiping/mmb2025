%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimvalue).

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
    PhiMap = mmb_ssa:collect_phi(Blocks, Nodes),
    {Counts, Consumers} = collect_blocks(Blocks, #{}, #{}, PhiMap, Nodes),

    Uses = collect_uses(
             [{Src, Dst}
              || {Src, M} <- maps:to_list(Consumers),
                 Dst <- maps:keys(M)
             ], #{}),

    Consumers1 =
        maps:from_list(
          [{Var, M}
           || {Var, M} <- maps:to_list(Consumers),
              maps:get(Var, Counts, 0) =:= 0]),

    Unused =
        [Var
         || {Var, M} <- maps:to_list(Consumers1),
            maps:size(M) =:= 0],

    Consumers2 = propagate({Unused, []}, Consumers1, Uses),
    Unused2 =
        maps:from_list(
          [{Var, []}
           || {Var, M} <- maps:to_list(Consumers2),
              maps:size(M) =:= 0
          ]),

    {PhiMap1, SSA1} = convert_blocks(Blocks, Unused2, PhiMap, SSA),
    convert_outputs(Blocks, PhiMap1, SSA1).

collect_uses([], Uses) ->
    Uses;
collect_uses([{Src, Dst}|T], Uses) ->
    U = maps:get(Dst, Uses, #{}),
    U1 = U#{Src => []},
    collect_uses(T, Uses#{Dst => U1}).

collect_blocks([], Counts, Consumers, _, _) ->
    {Counts, Consumers};
collect_blocks([H|T], Counts, Consumers, PhiMap, Nodes) ->
    {Counts1, Consumers1} = collect_block(H, Counts, Consumers, PhiMap, Nodes),
    collect_blocks(T, Counts1, Consumers1, PhiMap, Nodes).

collect_block(ID, Counts, Consumers, PhiMap, Nodes) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Consumers1 =
        case Input of
            [] ->
                Consumers;
            _ ->
                #{ID := Phi} = PhiMap,
                collect_phis(Input, [Values || {_, Values} <- Phi], Consumers, Nodes)
        end,
    {Counts1, Consumers2} = collect_stmts(Stmts, Counts, Consumers1, Nodes),
    {collect_output(Output, Counts1, Nodes), Consumers2}.

collect_output(none, Counts, _) ->
    Counts;
collect_output({_, _}, Counts, _) ->
    Counts;
collect_output({'if', Cond, _, _}, Counts, Nodes) when is_integer(Cond) ->
    increase_count(Cond, Counts, Nodes);
collect_output({'if', {_, List}, _, _}, Counts, Nodes) ->
    increase_counts(List, Counts, Nodes).

collect_phis([], _, Consumers, _) ->
    Consumers;
collect_phis([H|T], Phi, Consumers, Nodes) ->
    {Phi1, Consumers1} = collect_phi(H, Phi, Consumers, Nodes),
    collect_phis(T, Phi1, Consumers1, Nodes).

collect_phi(ID, Values, Consumers, Nodes) ->
    collect_phi_values(ID, Values, new_var(ID, Consumers), Nodes).

new_var(ID, Consumers) when is_map_key(ID, Consumers) ->
    Consumers;
new_var(ID, Consumers) ->
    Consumers#{ID => #{}}.

collect_phi_values(_ID, [], Consumers, _Nodes) ->
    {[], Consumers};
collect_phi_values(ID, [[H|T]|Rest], Consumers, Nodes) ->
    Consumers1 = add_consumer(H, ID, Consumers, Nodes),
    {Rest1, Consumers2} = collect_phi_values(ID, Rest, Consumers1, Nodes),
    {[T|Rest1], Consumers2}.

collect_stmts([], Counts, Consumers, _Nodes) ->
    {Counts, Consumers};
collect_stmts([H|T], Counts, Consumers, Nodes) ->
    {Counts1, Consumers1} = collect_stmt(H, Counts, Consumers, Nodes),
    collect_stmts(T, Counts1, Consumers1, Nodes).

collect_stmt({'let', ID}, Counts, Consumers, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    Counts1 =
        case mmb_compute:is_pure(Expr, Nodes) of
            true ->
                Counts;
            false ->
                increase_count(ID, Counts, Nodes)
        end,
    List = mmb_ssa:uses(Expr, Nodes),
    {Counts1, add_consumers(List, ID, new_var(ID, Consumers), Nodes)};
collect_stmt({op, {store, ref}, [Value, Ref]=List}, Counts, Consumers, Nodes) ->
    case Nodes of
        #{Ref := {var, _, {op, {make, _}, _}}} ->
            {Counts, add_consumers([Value], Ref, Consumers, Nodes)};
        _ ->
            {increase_counts(List, Counts, Nodes), Consumers}
    end;
collect_stmt({op, {store, array}, [Value, Array, Index]=List}, Counts, Consumers, Nodes) ->
    case Nodes of
        #{Array := {var, _, {op, {make, _}, _}}} ->
            {Counts, add_consumers([Value, Index], Array, Consumers, Nodes)};
        _ ->
            {increase_counts(List, Counts, Nodes), Consumers}
    end;
collect_stmt(Stmt, Counts, Consumers, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    {increase_counts(List, Counts, Nodes), Consumers}.

increase_counts([], Counts, _) ->
    Counts;
increase_counts([H|T], Counts, Nodes) ->
    increase_counts(T, increase_count(H, Counts, Nodes), Nodes).

increase_count(ID, Counts, Nodes) ->
    case Nodes of
        #{ID := {const, _, _}} ->
            Counts;
        _ ->
            Count = maps:get(ID, Counts, 0),
            Counts#{ID => Count + 1}
    end.


add_consumers([], _, Consumers, _) ->
    Consumers;
add_consumers([H|T], Consumer, Consumers, Nodes) ->
    Consumers1 = add_consumer(H, Consumer, Consumers, Nodes),
    add_consumers(T, Consumer, Consumers1, Nodes).

add_consumer(Var, Consumer, Consumers, Nodes) ->
    case Nodes of
        #{Var := {const, _, _}} ->
            Consumers;
        _ ->
            C = maps:get(Var, Consumers, #{}),
            C1 = C#{Consumer => []},
            Consumers#{Var => C1}
    end.


propagate(Queue, Consumers, Uses) ->
    case mmb_queue:pop(Queue) of
        none ->
            Consumers;
        {ID, Queue1} ->
            List = maps:keys(maps:get(ID, Uses, #{})),
            {Queue2, Consumers1} = queue_vars(List, ID, Queue1, Consumers),
            propagate(Queue2, Consumers1, Uses)
    end.


queue_vars([], _, Queue, Consumers) ->
    {Queue, Consumers};
queue_vars([H|T], Consumer, Queue, Consumers) ->
    {Queue1, Consumers1} = queue_var(H, Consumer, Queue, Consumers),
    queue_vars(T, Consumer, Queue1, Consumers1).

queue_var(ID, Consumer, Queue, Consumers) ->
    case Consumers of
        #{ID := C} ->
            C1 = maps:remove(Consumer, C),
            Consumers1 = Consumers#{ID => C1},
            Queue1 =
                case maps:size(C1) of
                    0 ->
                        mmb_queue:push(ID, Queue);
                    _ ->
                        Queue
                end,
            {Queue1, Consumers1};
        _ ->
            {Queue, Consumers}
    end.


convert_blocks([], _, PhiMap, SSA) ->
    {PhiMap, SSA};
convert_blocks([H|T], Unused, PhiMap, SSA) ->
    {PhiMap1, SSA1} = convert_block(H, Unused, PhiMap, SSA),
    convert_blocks(T, Unused, PhiMap1, SSA1).

convert_block(ID, Unused, PhiMap, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    PhiMap1 =
        case Input of
            [] ->
                PhiMap;
            _ ->
                #{ID := Phi} = PhiMap,
                Phi1 = convert_phis(Phi, Input, Unused),
                PhiMap#{ID => maps:from_list(Phi1)}
        end,
    Stmts1 = convert_stmts(Stmts, Unused),
    Input1 = [X || X <- Input, not maps:is_key(X, Unused)],
    {PhiMap1, mmb_ssa:set_node(ID, {bb, Input1, Output, Stmts1}, SSA)}.

convert_stmts([], _) ->
    [];
convert_stmts([{'let', ID}|T], Unused) when is_map_key(ID, Unused) ->
    convert_stmts(T, Unused);
convert_stmts([{op, {store, array}, [_, Array, _]}|T], Unused) when is_map_key(Array, Unused) ->
    convert_stmts(T, Unused);
convert_stmts([{op, {store, ref}, [_, Ref]}|T], Unused) when is_map_key(Ref, Unused) ->
    convert_stmts(T, Unused);
convert_stmts([H|T], Unused) ->
    [H|convert_stmts(T, Unused)].


convert_phis([], _, _) ->
    [];
convert_phis([{ID, Values}|T], Input, Unused) ->
    Values1 = convert_phi(Values, Input, Unused),
    [{ID, Values1}|convert_phis(T, Input, Unused)].

convert_phi([], [], _) ->
    [];
convert_phi([_|T1], [H2|T2], Unused) when is_map_key(H2, Unused) ->
    convert_phi(T1, T2, Unused);
convert_phi([H1|T1], [_|T2], Unused) ->
    [H1|convert_phi(T1, T2, Unused)].


convert_outputs([], _PhiMap, SSA) ->
    SSA;
convert_outputs([H|T], PhiMap, SSA) ->
    SSA1 = convert_output(H, PhiMap, SSA),
    convert_outputs(T, PhiMap, SSA1).

convert_output(ID, PhiMap, SSA=#ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Output1 = convert_output_(ID, Output, PhiMap),
    mmb_ssa:set_node(ID, {bb, Input, Output1, Stmts}, SSA).


convert_output_(_, none, _) ->
    none;
convert_output_(_, {ExitID, []}, _) ->
    {ExitID, []};
convert_output_(ID, {ExitID, _}, PhiMap) ->
    {ExitID, maps:get(ID, maps:get(ExitID, PhiMap))};
convert_output_(ID, {'if', Cond, True, False}, PhiMap) ->
    True1 = convert_output_(ID, True, PhiMap),
    False1 = convert_output_(ID, False, PhiMap),
    {'if', Cond, True1, False1}.
