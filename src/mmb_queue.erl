%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_queue).

-export([init/0, push/2, pop/1]).

init() ->
    {[], []}.

push(Elem, {[], []}) ->
    {[Elem], []};
push(Elem, {Out, In}) ->
    {Out, [Elem|In]}.

pop({[], []}) ->
    none;
pop({[Elem|Out], In}) ->
    {Elem, {Out, In}};
pop({[], In}) ->
    [Elem|Out] = reverse(In, []),
    {Elem, {Out, []}}.

reverse([], Acc) ->
    Acc;
reverse([H|T], Acc) ->
    reverse(T, [H|Acc]).
