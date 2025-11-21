%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_inlinesmall).

-export([convert/2]).

-include("mmb_ssa.hrl").

convert(SSA = #ssa{nodes=Nodes}, Threshold) ->
    Fns = mmb_ssa:collect_fns(SSA),
    {Unsafe, Depends} = collect_fns(maps:to_list(Fns), #{}, #{}, Nodes),
    Depends1 = maps:without(maps:keys(Unsafe), Depends),

    Callers =
        collect_callers(
          [{Y, X}
           || {X, M} <- maps:to_list(Depends),
              Y <- maps:keys(M)], #{}),

    Groups = scc([{X, false} || X <- maps:keys(Fns), is_integer(X)], [], [], #{}, #{}, Depends),
    List =
        [ID ||
            G <- Groups,
            maps:size(G) =:= 1,
            ID <- maps:keys(G),
            not maps:is_key(ID, Unsafe)],

    List1 = tsort(List, #{}, maps:from_list([{X, []} || X <- List]), Depends1),
    inline_fns(List1, Threshold, Callers, SSA).

collect_callers([], Acc) ->
    Acc;
collect_callers([{X, Y}|T], Acc) ->
    M = maps:get(X, Acc, #{}),
    M1 = M#{Y => []},
    collect_callers(T, Acc#{X => M1}).

tsort([], _, _, _) ->
    [];
tsort([H|T], Done, All, Depends) ->
    case Done of
        #{H := _} ->
            tsort(T, Done, All, Depends);
        _ ->
            List = maps:keys(maps:get(H, Depends, #{})),
            case [ID || ID <- List, maps:is_key(ID, All), not maps:is_key(ID, Done)] of
                [] ->
                    [H|tsort(T, Done#{H => []}, All, Depends)];
                List1 ->
                    tsort(append(List1, [H|T]), Done, All, Depends)
            end
    end.

append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].

collect_fns([], Unsafe, Depends, _) ->
    {Unsafe, Depends};
collect_fns([H|T], Unsafe, Depends, Nodes) ->
    {Unsafe1, Depends1} = collect_fn(H, Unsafe, Depends, Nodes),
    collect_fns(T, Unsafe1, Depends1, Nodes).

collect_fn({ID, []}, Unsafe, Depends, _) when is_atom(ID) ->
    {Unsafe, Depends};
collect_fn({ID, Blocks}, Unsafe, Depends, Nodes)  when is_integer(ID)->
    #{ID := {fn, Free, Params, _, _, _}} = Nodes,
    case Free of
        none ->
            Self = {none, none};
        _ ->
            [Closure|_] = Params,
            Self = {Closure, ID}
    end,
    {Unsafe1, Depends1} = collect_blocks(Blocks, Unsafe, #{}, Self, Nodes),
    {Unsafe1, Depends#{ID => Depends1}}.


collect_blocks([], Unsafe, Depends, _, _) ->
    {Unsafe, Depends};
collect_blocks([H|T], Unsafe, Depends, Self, Nodes) ->
    {Unsafe1, Depends1} = collect_block(H, Unsafe, Depends, Self, Nodes),
    collect_blocks(T, Unsafe1, Depends1, Self, Nodes).

collect_block(ID, Unsafe, Depends, Self, Nodes) ->
    #{ID := {bb, _, Output, Stmts}} = Nodes,
    {Unsafe1, Depends1} = collect_stmts(Stmts, Unsafe, Depends, Self, Nodes),
    Unsafe2 = collect_output(Output, Unsafe1, Self, Nodes),
    {Unsafe2, Depends1}.

collect_output(none, Unsafe, _, _) ->
    Unsafe;
collect_output({_, Values}, Unsafe, Self, Nodes) ->
    collect_values(Values, Unsafe, Self, Nodes);
collect_output({'if', Cond, True, False}, Unsafe, Self, Nodes) ->
    Unsafe1 = collect_value(Cond, Unsafe, Self, Nodes),
    Unsafe2 = collect_output(True, Unsafe1, Self, Nodes),
    collect_output(False, Unsafe2, Self, Nodes).

collect_stmts([], Unsafe, Depends, _, _) ->
    {Unsafe, Depends};
collect_stmts([H|T], Unsafe, Depends, Self, Nodes) ->
    {Unsafe1, Depends1} = collect_stmt(H, Unsafe, Depends, Self, Nodes),
    collect_stmts(T, Unsafe1, Depends1, Self, Nodes).

collect_stmt({'let', ID}, Unsafe, Depends, Self, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    collect_stmt(Expr, Unsafe, Depends, Self, Nodes);
collect_stmt({call, Fun, []}, Unsafe, Depends, Self, Nodes) ->
    Unsafe1 = collect_values([Fun], Unsafe, Self, Nodes),
    Depends1 =
        case Nodes of
            #{Fun := {const, _, {fn, ID}}} when is_integer(ID) ->
                Depends#{ID => []};
            _ ->
                Depends
        end,
    {Unsafe1, Depends1};
collect_stmt({call, Fun, [Closure|Args]}, Unsafe, Depends, Self, Nodes) ->
    case Nodes of
        #{Fun := {const, _, {fn, ID}}} when is_integer(ID) ->
            Unsafe2 =
                case Nodes of
                    #{Closure := {Kind, _, {op, {cast, up, {fn, ID}}, [TupleID]}}} ->
                        Unsafe1 =
                            case Kind of
                                const ->
                                    #{TupleID := {const, _, {op, {make, tuple}, [_|List]}}} = Nodes,
                                    collect_values(List, Unsafe, Self, Nodes);
                                _ ->
                                    Unsafe
                            end,
                        collect_values(Args, Unsafe1, Self, Nodes);
                    _ ->
                        collect_values([Fun, Closure|Args], Unsafe, Self, Nodes)
                end,
            Depends1 = Depends#{ID => []},
            {Unsafe2, Depends1};
        _ ->
            {collect_values([Fun, Closure|Args], Unsafe, Self, Nodes), Depends}
    end;
collect_stmt(Stmt, Unsafe, Depends, Self, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    {collect_values(List, Unsafe, Self, Nodes), Depends}.


collect_values([], Unsafe, _, _) ->
    Unsafe;
collect_values([H|T], Unsafe, Self, Nodes) ->
    Unsafe1 = collect_value(H, Unsafe, Self, Nodes),
    collect_values(T, Unsafe1, Self, Nodes).

collect_value(ID, Unsafe, {ID, FnID}, _) ->
    Unsafe#{FnID => []};
collect_value(ID, Unsafe, Self, Nodes) ->
    #{ID := Node} = Nodes,
    Unsafe1 =
        case Node of
            {_, _, {op, {cast, up, {fn, FnID}}, _}} ->
                Unsafe#{FnID => []};
            _ ->
                Unsafe
        end,
    case Node of
        {const, _, {op, {make, tuple}, List}} ->
            collect_values(List, Unsafe1, Self, Nodes);
        {const, _, {op, {cast, _, _}, List}} ->
            collect_values(List, Unsafe1, Self, Nodes);
        _ ->
            Unsafe1
    end.


scc([], _Stack, Groups, _Visited, _Done, _Depends) ->
    Groups;
scc([{V, true}|Queue], [{V, VS}|Stack], Groups, Visited, Done, Depends) ->
    scc(Queue, Stack, [VS|Groups], Visited, maps:merge(Done, VS), Depends);
scc([{V, false}|Queue], Stack, Groups, Visited, Done, Depends) when not is_map_key(V, Visited) ->
    Queue1 = queue_depends(maps:keys(maps:get(V, Depends, #{})), [{V, true}|Queue]),
    Stack1 = [{V, #{V => []}}|Stack],
    scc(Queue1, Stack1, Groups, Visited#{V => []}, Done, Depends);
scc([{V, false}|Queue], Stack, Groups, Visited, Done, Depends) when not is_map_key(V, Done)->
    Stack1 = pop_until(V, #{}, Stack),
    scc(Queue, Stack1 , Groups, Visited, Done, Depends);
scc([_|Queue], Stack, Groups, Visited, Done, Depends) ->
    scc(Queue, Stack, Groups, Visited, Done, Depends).

pop_until(_, _, []) ->
    [];
pop_until(V, Acc, [{W, VS}|Stack]) when is_map_key(V, VS) ->
    [{W, maps:merge(Acc, VS)}|Stack];
pop_until(V, Acc, [{_, VS}|Stack]) ->
    pop_until(V, maps:merge(Acc, VS), Stack).


queue_depends([], Queue) ->
    Queue;
queue_depends([H|T], Queue) ->
    queue_depends(T, [{H, false}|Queue]).

inline_fns([], _, _, SSA) ->
    SSA;
inline_fns([H|T], Threshold, Callers, SSA) ->
    inline_fns(T, Threshold, Callers, inline_fn(H, Threshold, Callers, SSA)).

inline_fn(ID, Threshold, Callers, SSA = #ssa{nodes=Nodes}) ->
    Blocks = mmb_ssa:collect_blocks(ID, Nodes),
    case is_small(Blocks, Threshold, Nodes) of
        0 ->
            SSA;
        X ->
            M = maps:get(ID, Callers, #{}),
            if (Threshold - X) * map_size(M) =< Threshold * Threshold div 4 ->
                    convert_fns(maps:keys(M), ID, SSA);
               true ->
                    SSA
            end
    end.

is_small([], Threshold, _Nodes) ->
    Threshold;
is_small(_, 0, _) ->
    0;
is_small([H|T], Threshold, Nodes) ->
    #{H := {bb, _, _, Stmts}} = Nodes,
    case is_small(Stmts, Threshold) of
        0 ->
            0;
        X ->
            is_small(T, X - 1, Nodes)
    end.

is_small([], Threshold) ->
    Threshold;
is_small(_, 0) ->
    0;
is_small([_|T], Threshold) ->
    is_small(T, Threshold - 1).


convert_fns([], _, SSA) ->
    SSA;
convert_fns([H|T], ID, SSA) ->
    convert_fns(T, ID, convert_fn(H, ID, SSA)).

convert_fn(ID, Inline, SSA = #ssa{nodes=Nodes})  ->
    Blocks = mmb_ssa:collect_blocks(ID, Nodes),
    convert_blocks(Blocks, Inline, SSA).

convert_blocks([], _, SSA) ->
    SSA;
convert_blocks([H|T], Inline, SSA) ->
    convert_blocks(T, Inline, convert_block(H, Inline, SSA)).

convert_block(ID, Inline, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    {Stmts1, Output1, SSA1} = convert_stmts(Stmts, Output, Inline, SSA),
    mmb_ssa:set_node(ID, {bb, Input, Output1, Stmts1}, SSA1).

convert_stmts([], Output, _, SSA) ->
    {[], Output, SSA};
convert_stmts([{'let', ID}=H|T], Output, Inline, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, _, Expr}} = Nodes,
    case Expr of
        {call, Fun, [Closure|Args]} ->
            case Nodes of
                #{Fun := {const, _, {fn, Inline}}} ->
                    #{Closure := {_, _, {op, {cast, up, {fn, Inline}}, [TupleID]}}} = Nodes,
                    #{TupleID := {_, _, {op, {make, tuple}, [_|List]}}} = Nodes,
                    {{fn, Free, [_|Params], _, Entry, Exit}, SSA1} = mmb_ssa:copy_fn(Inline, SSA),
                    Params1 = append(Free, Params),
                    SSA2 = set_phis([ID|Params1], SSA1),
                    SSA3 = convert_entry(Entry, Params1, SSA2),
                    {T1, Output1, SSA4} = convert_stmts(T, Output, Inline, SSA3),
                    {ExitID, SSA5} = mmb_ssa:add_node({bb, [ID], Output1, T1}, SSA4),
                    SSA6 = convert_exit(Exit, ExitID, SSA5),
                    {[], {Entry, append(List, Args)}, SSA6};
                _ ->
                    convert_stmts(H, T, Output, Inline, SSA)
            end;
        _ ->
            convert_stmts(H, T, Output, Inline, SSA)
    end;
convert_stmts([{call, Fun, [Closure|Args]}=H|T], Output, Inline, SSA = #ssa{nodes=Nodes}) ->
    case Nodes of
        #{Fun := {const, _, {fn, Inline}}} ->
            #{Closure := {_, _, {op, {cast, up, {fn, Inline}}, [TupleID]}}} = Nodes,
            #{TupleID := {_, _, {op, {make, tuple}, [_|List]}}} = Nodes,
            {{fn, Free, [_|Params], _, Entry, Exit}, SSA1} = mmb_ssa:copy_fn(Inline, SSA),
            Params1 = append(Free, Params),
            SSA2 = set_phis(Params1, SSA1),
            SSA3 = convert_entry(Entry, Params1, SSA2),
            {T1, Output1, SSA4} = convert_stmts(T, Output, Inline, SSA3),
            SSA5 = mmb_ssa:set_node(Exit, {bb, [], Output1, T1}, SSA4),
            {[], {Entry, append(List, Args)}, SSA5};
        _ ->
            convert_stmts(H, T, Output, Inline, SSA)
    end;
convert_stmts([H|T], Output, Inline, SSA) ->
    convert_stmts(H, T, Output, Inline, SSA).

convert_stmts(H, T, Output, Inline, SSA) ->
    {T1, Output1, SSA1} = convert_stmts(T, Output, Inline, SSA),
    {[H|T1], Output1, SSA1}.

convert_entry(Entry, Params, SSA = #ssa{nodes=Nodes}) ->
    #{Entry := {bb, [], Output, Stmts}} = Nodes,
    mmb_ssa:set_node(Entry, {bb, Params, Output, Stmts}, SSA).

convert_exit(Exit, ExitID, SSA = #ssa{nodes=Nodes}) ->
    #{Exit := {bb, Input, none, [{return, Expr}]}} = Nodes,
    mmb_ssa:set_node(Exit, {bb, Input, {ExitID, [Expr]}, []}, SSA).

set_phis([], SSA) ->
    SSA;
set_phis([H|T], SSA) ->
    set_phis(T, set_phi(H, SSA)).

set_phi(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, _}} = Nodes,
    mmb_ssa:set_node(ID, {var, Type, phi}, SSA).
