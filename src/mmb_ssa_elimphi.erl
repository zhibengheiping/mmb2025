%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimphi).

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
    {SrcMap, DstMap, ValueMap} = collect_blocks(Blocks, #{}, #{}, #{}, PhiMap, Nodes),
    SingleSrc = [Var || {Var, Srcs} <- maps:to_list(SrcMap), map_size(Srcs) =:= 1, not is_map_key(Var, ValueMap)],
    {SrcMap1, DstMap1} = propagate_src({SingleSrc, []}, SrcMap, DstMap, ValueMap),

    Total = maps:size(maps:merge(SrcMap1, ValueMap)),
    BoundMap =
        maps:from_list(
          [{K, case V of bad -> K; _ -> V end}
           || {K, V} <- maps:to_list(ValueMap),
              V =:= bad orelse not maps:is_key(K, SrcMap1)
          ]),

    BoundMap1 = resolve_all(Total, BoundMap, SrcMap1, DstMap1, ValueMap),
    Rename = maps:from_list([{K, V} || {K, V} <- maps:to_list(BoundMap1), K =/= V]),
    mmb_ssa:rename_blocks(Blocks, Rename, SSA).

resolve_all(Total, BoundMap, _, _, _) when map_size(BoundMap) =:= Total ->
    BoundMap;
resolve_all(Total, BoundMap, SrcMap, DstMap, ValueMap) ->
    Queue = mmb_queue:init(),
    List = maps:keys(BoundMap),
    Queue1 = queue_bound(List, BoundMap, DstMap, Queue),
    Queue2 = queue_values(maps:to_list(maps:without(List, ValueMap)), Queue1),

    NewMap = propagate_value(Queue2, #{}, BoundMap, DstMap),
    {NewBoundList, UnboundList} = split(maps:to_list(NewMap), ValueMap),
    BoundMap1 = maps:merge(BoundMap, maps:from_list(NewBoundList)),

    NewBoundMap2 =
        maps:from_list(
          [{K, V}
           || K <- UnboundList,
              V <- case maps:keys(maps:get(K, SrcMap, #{})) of
                       [Src] ->
                           if is_map_key(Src, BoundMap1) ->
                                   [maps:get(Src, BoundMap1)];
                              true ->
                                   []
                           end;
                       Srcs ->
                           case is_all_bound(Srcs, BoundMap1) of
                               true ->
                                   [K];
                               false ->
                                   []
                           end
                   end]),
    BoundMap2 = maps:merge(BoundMap1, NewBoundMap2),

    if map_size(BoundMap2) > map_size(BoundMap) ->
            resolve_all(Total, BoundMap2, SrcMap, DstMap, ValueMap);
       true ->
            NewBoundMap3 =
                maps:from_list(
                  [{K, K}
                   || K <- UnboundList,
                      is_any_bound(maps:keys(maps:get(K, SrcMap, #{})), BoundMap1)]),
            BoundMap3 = maps:merge(BoundMap2, NewBoundMap3),
            true = map_size(BoundMap3) > map_size(BoundMap),
            resolve_all(Total, BoundMap3, SrcMap, DstMap, ValueMap)
    end.

split([], _ValueMap) ->
    {[], []};
split([{K, V}|T], ValueMap) ->
    {Bound, Unbound} = split(T, ValueMap),
    case V of
        bad when is_map_key(K, ValueMap) ->
            {[{K, K}|Bound], Unbound};
        bad ->
            {Bound, [K|Unbound]};
        _ ->
            {[{K, V}|Bound], Unbound}
    end.


is_any_bound([], _) ->
    false;
is_any_bound([H|T], BoundMap) ->
    maps:is_key(H, BoundMap) orelse is_any_bound(T, BoundMap).

is_all_bound([], _) ->
    true;
is_all_bound([H|T], BoundMap) ->
    maps:is_key(H, BoundMap) andalso is_all_bound(T, BoundMap).

propagate_value(Queue, Acc, BoundMap, DstMap) ->
    case mmb_queue:pop(Queue) of
        none ->
            Acc;
        {{Var, Var}, Queue1} ->
            propagate_value(Queue1, Acc, BoundMap, DstMap);
        {{Var, Value}, Queue1} ->
            case Acc of
                #{Var := Value} ->
                    propagate_value(Queue1, Acc, BoundMap, DstMap);
                #{Var := bad} ->
                    propagate_value(Queue1, Acc, BoundMap, DstMap);
                #{Var := _} ->
                    Queue2 = queue_dst(maps:keys(maps:get(Var, DstMap, #{})), bad, BoundMap, Queue1),
                    propagate_value(Queue2, Acc#{Var => bad}, BoundMap, DstMap);
                _ ->
                    Queue2 = queue_dst(maps:keys(maps:get(Var, DstMap, #{})), Value, BoundMap, Queue1),
                    propagate_value(Queue2, Acc#{Var => Value}, BoundMap, DstMap)
            end
    end.


queue_values([], Queue) ->
    Queue;
queue_values([H|T], Queue) ->
    queue_values(T, mmb_queue:push(H, Queue)).

queue_bound([], _, _, Queue) ->
    Queue;
queue_bound([H|T], BoundMap, DstMap, Queue) ->
    Value = maps:get(H, BoundMap),
    Dsts = maps:keys(maps:get(H, DstMap, #{})),
    Queue1 = queue_dst(Dsts, Value, BoundMap, Queue),
    queue_bound(T, BoundMap, DstMap, Queue1).

queue_dst([], _Value, _BoundMap, Queue) ->
    Queue;
queue_dst([H|T], Value, BoundMap, Queue) when is_map_key(H, BoundMap) ->
    queue_dst(T, Value, BoundMap, Queue);
queue_dst([H|T], Value, BoundMap, Queue) ->
    queue_dst(T, Value, BoundMap, mmb_queue:push({H, Value}, Queue)).


collect_blocks([], SrcMap, DstMap, ValueMap, _, _) ->
    {SrcMap, DstMap, ValueMap};
collect_blocks([H|T], SrcMap, DstMap, ValueMap, PhiMap, Nodes) ->
    {SrcMap1, DstMap1, ValueMap1} = collect_block(H, SrcMap, DstMap, ValueMap, PhiMap, Nodes),
    collect_blocks(T, SrcMap1, DstMap1, ValueMap1, PhiMap, Nodes).

collect_block(ID, SrcMap, DstMap, ValueMap, PhiMap, Nodes) ->
    #{ID := {bb, Input, _, _}} = Nodes,
    case Input of
        [] ->
            {SrcMap, DstMap, ValueMap};
        _ ->
            #{ID := Phis} = PhiMap,
            collect_phis(Phis, Input, SrcMap, DstMap, ValueMap, Nodes)
    end.

collect_phis([], _, SrcMap, DstMap, ValueMap, _) ->
    {SrcMap, DstMap, ValueMap};
collect_phis([{_, Values}|T], Input, SrcMap, DstMap, ValueMap, Nodes) ->
    {SrcMap1, DstMap1, ValueMap1} = collect_pairs(Values, Input, SrcMap, DstMap, ValueMap, Nodes),
    collect_phis(T, Input, SrcMap1, DstMap1, ValueMap1, Nodes).

collect_pairs([], [], SrcMap, DstMap, ValueMap, _Nodes) ->
    {SrcMap, DstMap, ValueMap};
collect_pairs([H1|T1], [H2|T2], SrcMap, DstMap, ValueMap, Nodes) ->
    {SrcMap1, DstMap1, ValueMap1} = collect_pair(H1, H2, SrcMap, DstMap, ValueMap, Nodes),
    collect_pairs(T1, T2, SrcMap1, DstMap1, ValueMap1, Nodes).


collect_pair(Value, Value, SrcMap, DstMap, ValueMap, _Nodes) ->
    {SrcMap, DstMap, ValueMap};
collect_pair(Value, Phi, SrcMap, DstMap, ValueMap, Nodes) ->
    case Nodes of
        #{Value := {_, _, phi}} ->
            S = maps:get(Phi, SrcMap, #{}),
            S1 = S#{Value => []},
            SrcMap1 = SrcMap#{Phi => S1},

            D = maps:get(Value, DstMap, #{}),
            D1 = D#{Phi => []},
            DstMap1 = DstMap#{Value => D1},
            {SrcMap1, DstMap1, ValueMap};
        _ ->
            case ValueMap of
                #{Phi := Value} ->
                    {SrcMap, DstMap, ValueMap};
                #{Phi := _} ->
                    {SrcMap, DstMap, ValueMap#{Phi => bad}};
                _ ->
                    {SrcMap, DstMap, ValueMap#{Phi => Value}}
            end
    end.


propagate_src(Queue, SrcMap, DstMap, ValueMap) ->
    case mmb_queue:pop(Queue) of
        none ->
            {SrcMap, DstMap};
        {Var, Queue1} ->
            #{Var := Srcs} = SrcMap,
            [Src] = maps:keys(Srcs),
            Dsts = maps:get(Var, DstMap, #{}),
            Dsts1 = maps:merge(maps:get(Src, DstMap), maps:remove(Src, Dsts)),
            DstMap1 = DstMap#{Src => Dsts1, Var => #{}},
            {SrcMap1, Queue2} = update_srcs(maps:keys(Dsts), Var, Src, SrcMap, ValueMap, Queue1),
            propagate_src(Queue2, SrcMap1, DstMap1, ValueMap)
    end.


update_srcs([], _, _, SrcMap, _ValueMap, Queue) ->
    {SrcMap, Queue};
update_srcs([H|T], Var, Src, SrcMap, ValueMap, Queue) ->
    {SrcMap1, Queue1} = update_src(H, Var, Src, SrcMap, ValueMap, Queue),
    update_srcs(T, Var, Src, SrcMap1, ValueMap, Queue1).

update_src(Dst, Var, Src, SrcMap, ValueMap, Queue) ->
    #{Dst := S} = SrcMap,
    S1 = maps:remove(Var, S),
    S2 =
        case Src of
            Dst ->
                S1;
            _ ->
                S1#{Src => []}
        end,
    SrcMap1 = SrcMap#{Dst => S2},
    Queue1 =
        case maps:size(S2) of
            1 when not is_map_key(Dst, ValueMap) ->
                mmb_queue:push(Dst, Queue);
            _ ->
                Queue
        end,
    {SrcMap1, Queue1}.
