%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimarg).

-export([convert/1]).

-include("mmb_ssa.hrl").

convert(SSA = #ssa{nodes=Nodes}) ->
    Fns = mmb_ssa:collect_fns(SSA),
    List = maps:to_list(Fns),
    {Unsafe, ArgMap} = collect_fns(List, #{}, #{}, Nodes),
    ArgMap1 = maps:without(maps:keys(Unsafe), ArgMap),
    ArgMap2 = maps:from_list([{ID, Args} || {ID, Args} <- maps:to_list(ArgMap1), has_any_const(Args)]),
    convert_fns(List, ArgMap2, SSA).

has_any_const([]) ->
    false;
has_any_const([H|_]) when is_integer(H) ->
    true;
has_any_const([_|T]) ->
    has_any_const(T).

collect_fns([], Unsafe, ArgMap, _) ->
    {Unsafe, ArgMap};
collect_fns([H|T], Unsafe, ArgMap, Nodes) ->
    {Unsafe1, ArgMap1} = collect_fn(H, Unsafe, ArgMap, Nodes),
    collect_fns(T, Unsafe1, ArgMap1, Nodes).

collect_fn({ID, []}, Unsafe, ArgMap, _) when is_atom(ID) ->
    {Unsafe, ArgMap};
collect_fn({ID, Blocks}, Unsafe, ArgMap, Nodes) when is_integer(ID) ->
    #{ID := {fn, Free, Params, _, _, _}} = Nodes,
    case Free of
        none ->
            Self = {none, none};
        _ ->
            [Closure|_] = Params,
            Self = {Closure, ID}
    end,
    collect_blocks(Blocks, Unsafe, ArgMap, Self, Params, Nodes).

collect_blocks([], Unsafe, ArgMap, _, _, _) ->
    {Unsafe, ArgMap};
collect_blocks([H|T], Unsafe, ArgMap, Self, Params, Nodes) ->
    {Unsafe1, ArgMap1} = collect_block(H, Unsafe, ArgMap, Self, Params, Nodes),
    collect_blocks(T, Unsafe1, ArgMap1, Self, Params, Nodes).

collect_block(ID, Unsafe, ArgMap, Self, Params, Nodes) ->
    #{ID := {bb, _, Output, Stmts}} = Nodes,
    {Unsafe1, ArgMap1} = collect_stmts(Stmts, Unsafe, ArgMap, Self, Params, Nodes),
    Unsafe2 = collect_output(Output, Unsafe1, Self, Nodes),
    {Unsafe2, ArgMap1}.

collect_stmts([], Unsafe, ArgMap, _, _, _) ->
    {Unsafe, ArgMap};
collect_stmts([H|T], Unsafe, ArgMap, Self, Params, Nodes) ->
    {Unsafe1, ArgMap1} = collect_stmt(H, Unsafe, ArgMap, Self, Params, Nodes),
    collect_stmts(T, Unsafe1, ArgMap1, Self, Params, Nodes).

collect_output(none, Unsafe, _, _) ->
    Unsafe;
collect_output({_, Values}, Unsafe, Self, Nodes) ->
    collect_values(Values, Unsafe, Self, Nodes);
collect_output({'if', Cond, True, False}, Unsafe, Self, Nodes) ->
    Unsafe1 = collect_value(Cond, Unsafe, Self, Nodes),
    Unsafe2 = collect_output(True, Unsafe1, Self, Nodes),
    collect_output(False, Unsafe2, Self, Nodes).

collect_stmt({'let', ID}, Unsafe, ArgMap, Self, Params, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    collect_stmt(Expr, Unsafe, ArgMap, Self, Params, Nodes);
collect_stmt({call, Fun, []}, Unsafe, ArgMap, Self, _Params, Nodes) ->
    Unsafe1 = collect_values([Fun], Unsafe, Self, Nodes),
    {Unsafe1, ArgMap};
collect_stmt({call, Fun, [Closure|Args]}, Unsafe, ArgMap, Self, Params, Nodes) ->
    case Nodes of
        #{Fun := {const, _, {fn, ID}}} ->
            Unsafe2 =
                case Self of
                    {Closure, ID} ->
                        [_|Params1] = Params,
                        Args1 = check_params(Params1, Args),
                        collect_values(Args, Unsafe, Self, Nodes);
                    _ ->
                        Args1 = check_args(Args, Nodes),
                        case Nodes of
                            #{Closure := {const, _, {op, {cast, up, {fn, ID}}, [TupleID]}}} ->
                                #{TupleID := {const, _, {op, {make, tuple}, [_|List]}}} = Nodes,
                                Unsafe1 = collect_values(List, Unsafe, Self, Nodes),
                                collect_values(Args, Unsafe1, Self, Nodes);
                            #{Closure := {_, _, {op, {cast, up, {fn, ID}}, _}}} ->
                                collect_values(Args, Unsafe, Self, Nodes);
                            _ ->
                                collect_values([Fun, Closure|Args], Unsafe, Self, Nodes)
                        end
                end,
            Args2 =
                case ArgMap of
                    #{ID := OldArgs} ->
                        merge(OldArgs, Args1);
                    _ ->
                        Args1
                end,

            {Unsafe2, ArgMap#{ID => Args2}};
        _ ->
            Unsafe1 = collect_values([Fun, Closure|Args], Unsafe, Self, Nodes),
            {Unsafe1, ArgMap}
    end;
collect_stmt(Stmt, Unsafe, ArgMap, Self, _Params, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    Unsafe1 = collect_values(List, Unsafe, Self, Nodes),
    {Unsafe1, ArgMap}.

check_params([], []) ->
    [];
check_params([H|T1], [H|T2]) ->
    [any|check_params(T1, T2)];
check_params([_|T1], [_|T2]) ->
    [bad|check_params(T1,T2)].

check_args([], _) ->
    [];
check_args([H|T], Nodes) ->
    H1 =
        case Nodes of
            #{H := {const, _, _}} ->
                H;
            _ ->
                bad
        end,
    [H1|check_args(T, Nodes)].

merge([], []) ->
    [];
merge([any|T1], [H|T2]) ->
    [H|merge(T1, T2)];
merge([H|T1], [any|T2]) ->
    [H|merge(T1, T2)];
merge([H|T1], [H|T2]) ->
    [H|merge(T1, T2)];
merge([_|T1], [_|T2]) ->
    [bad|merge(T1, T2)].


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


convert_fns([], _ArgMap, SSA) ->
    SSA;
convert_fns([H|T], ArgMap, SSA) ->
    SSA1 = convert_fn(H, ArgMap, SSA),
    convert_fns(T, ArgMap, SSA1).


convert_fn({ID, []}, _, SSA) when is_atom(ID) ->
    SSA;
convert_fn({ID, Blocks}, ArgMap, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    #{ID := {fn, Free, Params, ReturnType, Entry, Exit}} = Nodes,
    SSA2 =
        case ArgMap of
            #{ID := Args} ->
                {Params1, Rename} = filter_params(Params, [bad|Args], #{}),
                SSA1 = mmb_ssa:rename_blocks(Blocks, Rename, SSA),
                mmb_ssa:set_node(ID, {fn, Free, Params1, ReturnType, Entry, Exit}, SSA1);
            _ ->
                SSA
        end,
    convert_blocks(Blocks, ArgMap, SSA2).

filter_params([], [], Acc) ->
    {[], Acc};
filter_params([H1|T1], [H2|T2], Acc) when is_integer(H2) ->
    filter_params(T1, T2, Acc#{H1 => H2});
filter_params([H|T1], [_|T2], Acc) ->
    {Rest, Acc1} = filter_params(T1, T2, Acc),
    {[H|Rest], Acc1}.


convert_blocks([], _, SSA) ->
    SSA;
convert_blocks([H|T], ArgMap, SSA) ->
    SSA1 = convert_block(H, ArgMap, SSA),
    convert_blocks(T, ArgMap, SSA1).

convert_block(ID, ArgMap, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    {Stmts1, SSA1} = convert_stmts(Stmts, ArgMap, SSA),
    mmb_ssa:set_node(ID, {bb, Input, Output, Stmts1}, SSA1).

convert_stmts([], _, SSA) ->
    {[], SSA};
convert_stmts([H|T], ArgMap, SSA) ->
    {H1, SSA1} = convert_stmt(H, ArgMap, SSA),
    {T1, SSA2} = convert_stmts(T, ArgMap, SSA1),
    {[H1|T1], SSA2}.


convert_stmt({'let', ID}=Stmt, ArgMap, SSA = #ssa{nodes = Nodes}) ->
    #{ID := {var, Type, Expr}} = Nodes,
    {Expr1, SSA1} = convert_stmt(Expr, ArgMap, SSA),
    SSA2 = mmb_ssa:set_node(ID, {var, Type, Expr1}, SSA1),
    {Stmt, SSA2};
convert_stmt({call, _, []}=Stmt, _, SSA) ->
    {Stmt, SSA};
convert_stmt({call, Fun, [Closure|Args]}=Stmt, ArgMap, SSA=#ssa{nodes=Nodes}) ->
    Stmt1 =
        case Nodes of
            #{Fun := {const, _, {fn, ID}}} when is_map_key(ID, ArgMap) ->
                Args1 = filter_args(Args, maps:get(ID, ArgMap)),
                {call, Fun, [Closure|Args1]};
            _ ->
                Stmt
        end,
    {Stmt1, SSA};
convert_stmt(Stmt, _, SSA) ->
    {Stmt, SSA}.


filter_args([], []) ->
    [];
filter_args([_|T1], [H2|T2]) when is_integer(H2) ->
    filter_args(T1, T2);
filter_args([H|T1], [_|T2]) ->
    [H|filter_args(T1, T2)].
