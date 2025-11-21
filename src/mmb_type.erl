%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_type).

-export([get/2, bind/3, unify/3, gen_map/2]).

lookup(V, Map) ->
    case Map of
        #{V := T} ->
            if is_reference(T)
               ; is_integer(T)
               ->
                    true = V =/= T,
                    lookup(T, Map);
               true ->
                    T
            end;
        _ ->
            V
    end.

occurs(X, V, Map)
  when is_reference(V)
       ; is_integer(V)
       ->
    case lookup(V, Map) of
        Y when is_reference(Y)
               ; is_integer(Y)
               ->
            X =:= Y;
        Other ->
            occurs(X, Other, Map)
    end;
occurs(_, Type, _) when is_atom(Type) ->
    false;
occurs(_, {param, _}, _) ->
    false;
occurs(X, {typedef, _, Gen}, Map) ->
    occurs_list(X, Gen, Map);
occurs(X, {fn, Args, ReturnType}, Map) ->
    occurs_list(X, [ReturnType|Args], Map);
occurs(X, {closure, Args, ReturnType}, Map) ->
    occurs_list(X, [ReturnType|Args], Map);
occurs(X, {array, V}, Map) ->
    occurs(X, V, Map);
occurs(X, {tuple, List}, Map) ->
    occurs_list(X, List, Map);
occurs(X, {ref, V}, Map) ->
    occurs(X, V, Map).


occurs_list(_, [], _) ->
    false;
occurs_list(X, [H|T], Map) ->
    occurs(X, H, Map) or occurs_list(X, T, Map).

unify(X, X, Map) ->
    Map;
unify(X, Y, Map)
  when is_reference(X)
       ; is_integer(X)
       ->
    case lookup(X, Map) of
        T when is_reference(T)
               ; is_integer(T)
               ->
            case occurs(T, Y, Map) of
                true when is_reference(Y)
                          ; is_integer(Y)
                          ->
                    T = lookup(Y, Map),
                    Map;
                false ->
                    Map#{T => Y}
            end;
        T ->
            unify(T, Y, Map)
    end;
unify(X, Y, Map)
  when is_reference(Y)
       ; is_integer(Y)
       ->
    unify(Y, X, Map);
unify({fn, Args1, Return1}, {fn, Args2, Return2}, Map) ->
    unify_list([Return1|Args1], [Return2|Args2], Map);
unify({closure, Args1, Return1}, {closure, Args2, Return2}, Map) ->
    unify_list([Return1|Args1], [Return2|Args2], Map);
unify({array, X}, {array, Y}, Map) ->
    unify(X, Y, Map);
unify({tuple, X}, {tuple, Y}, Map) ->
    unify_list(X,Y,Map);
unify({typedef, N, X}, {typedef, N, Y}, Map) ->
    unify_list(X, Y, Map);
unify({ref, X}, {ref, Y}, Map) ->
    unify(X, Y, Map).


unify_list([], [], Map) ->
    Map;
unify_list([H1|T1], [H2|T2], Map) ->
    unify_list(T1, T2, unify(H1, H2, Map)).

find(X, Map) ->
    case Map of
        #{X := Y} ->
            Y
    end.

bind(X, _, _) when is_atom(X) ->
    X;
bind(X, Binding, Map)
  when is_reference(X)
       ; is_integer(X)
       ->
    Y = find(X, Map),
    true = X =/= Y,
    bind(Y, Binding, Map);
bind({fn, Args, Return}, Binding, Map) ->
    [Return1|Args1] = bind_list([Return|Args], Binding, Map),
    {fn, Args1, Return1};
bind({closure, Args, Return}, Binding, Map) ->
    [Return1|Args1] = bind_list([Return|Args], Binding, Map),
    {closure, Args1, Return1};
bind({array, X}, Binding, Map) ->
    {array, bind(X, Binding, Map)};
bind({tuple, X}, Binding, Map) ->
    {tuple, bind_list(X, Binding, Map)};
bind({ref, X}, Binding, Map) ->
    {ref, bind(X, Binding, Map)};
bind({typedef, N, List}, Binding, Map) ->
    {typedef, N, bind_list(List, Binding, Map)};
bind({param, X}, Binding, _Map) ->
    #{X := X1} = Binding,
    X1.

bind_list([], _, _) ->
    [];
bind_list([H|T], Binding, Map) ->
    H1 = bind(H, Binding, Map),
    T1 = bind_list(T, Binding, Map),
    [H1|T1].


get(X, _) when is_atom(X) ->
    X;
get(X, Map)
  when is_reference(X)
       ; is_integer(X)
       ->
    case Map of
        #{X := Y} ->
            true = X =/= Y,
            get(Y, Map);
        _ ->
            X
    end;
get({fn, Args, Return}, Map) ->
    [Return1|Args1] = get_list([Return|Args], Map),
    {fn, Args1, Return1};
get({closure, Args, Return}, Map) ->
    [Return1|Args1] = get_list([Return|Args], Map),
    {closure, Args1, Return1};
get({array, X}, Map) ->
    {array, get(X, Map)};
get({tuple, X}, Map) ->
    {tuple, get_list(X, Map)};
get({ref, X}, Map) ->
    {ref, get(X, Map)};
get({typedef, N, List}, Map) ->
    {typedef, N, get_list(List, Map)};
get({param, X}, _Map) ->
    {param, X}.


get_list([], _) ->
    [];
get_list([H|T], Map) ->
    H1 = get(H, Map),
    T1 = get_list(T, Map),
    [H1|T1].


gen_map(X, Y) ->
    maps:from_list(gen_zip(X, Y)).

gen_zip([], []) ->
    [];
gen_zip([{param, H1}|T1], [H2|T2]) ->
    [{H1, H2}|gen_zip(T1, T2)].
