%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_dom).

-export([doms/2]).

-include("mmb_ssa.hrl").

doms(Blocks, Nodes) ->
    [Entry|_] = Blocks,
    Dsts = collect_dsts(Blocks, #{}, Nodes),
    Ndom = propagate({[{Entry,ID}|| ID <- Blocks], []}, #{}, Dsts),
    doms(Blocks, Blocks, Ndom).

collect_dsts([], Dsts, _Nodes) ->
    Dsts;
collect_dsts([H|T], Dsts, Nodes) ->
    collect_dsts(T, collect_dst(H, Dsts, Nodes), Nodes).

collect_dst(ID, Dsts, Nodes) ->
    #{ID := {bb, _, Output, _}} = Nodes,
    Dsts#{ID => collect_dst(Output)}.

collect_dst(none) ->
    [];
collect_dst({ExitID, _}) ->
    [ExitID];
collect_dst({'if', _, {True, _}, {False, _}}) ->
    [True, False].

propagate(Queue, Ndom, Dsts) ->
    case mmb_queue:pop(Queue) of
        none ->
            Ndom;
        {{Src, Src}, Queue1} ->
            propagate(Queue1, Ndom, Dsts);
        {{Src, ID}, Queue1} ->
            case maps:get(Src, Ndom, #{}) of
                #{ID := _} ->
                    propagate(Queue1, Ndom, Dsts);
                N ->
                    N1 = N#{ID => []},
                    Queue2 = queue_dsts(maps:get(Src, Dsts, []), ID, Queue1),
                    propagate(Queue2, Ndom#{Src => N1}, Dsts)
            end
    end.

queue_dsts([], _, Queue) ->
    Queue;
queue_dsts([H|T], ID, Queue) ->
    queue_dsts(T, ID, mmb_queue:push({H, ID}, Queue)).


doms([], _, _) ->
    [];
doms([H|T], Blocks, Ndom) ->
    [{H, dom(Blocks, maps:get(H, Ndom, #{}))}|doms(T, Blocks, Ndom)].

dom(Blocks, Ndom) ->
    [ID || ID <- Blocks, not maps:is_key(ID, Ndom)].
