%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimfree).

-export([convert/1]).

-include("mmb_ssa.hrl").

convert(SSA = #ssa{nodes=Nodes}) ->
    Fns = mmb_ssa:collect_fns(SSA),
    List = maps:to_list(Fns),
    Candidates = collect_candidates(List, Nodes),
    Unsafe = collect_fns(List, #{}, Nodes),
    Safe = maps:from_list([{ID, Empty} || {ID, Empty} <- Candidates, not maps:is_key(ID, Unsafe)]),
    {Closures, SSA1} = convert_fns(List, #{}, Safe, SSA),
    {Removed, SSA2} = convert_closures(maps:keys(Closures), #{}, SSA1),
    clean_fns(List, Removed, SSA2).

collect_candidates([], _) ->
    [];
collect_candidates([{ID, []}|T], Nodes) when is_atom(ID) ->
    collect_candidates(T, Nodes);
collect_candidates([{ID, _}|T], Nodes) when is_integer(ID) ->
    #{ID := {fn, Free, _, _, _, _}} = Nodes,
    case Free of
        none ->
            collect_candidates(T, Nodes);
        [] ->
            [{ID, true}|collect_candidates(T, Nodes)];
        _ ->
            [{ID, false}|collect_candidates(T, Nodes)]
    end.

collect_fns([], Acc, _) ->
    Acc;
collect_fns([H|T], Acc, Nodes) ->
    Acc1 = collect_fn(H, Acc, Nodes),
    collect_fns(T, Acc1, Nodes).

collect_fn({ID, []}, Acc, _) when is_atom(ID) ->
    Acc;
collect_fn({ID, Blocks}, Acc, Nodes) when is_integer(ID) ->
    #{ID := {fn, Free, Params, _, _, _}} = Nodes,
    case Free of
        none ->
            Self = {none, none};
        _ ->
            [Closure|_] = Params,
            Self = {Closure, ID}
    end,
    collect_blocks(Blocks, Acc, Self, Nodes).

collect_blocks([], Acc, _, _) ->
    Acc;
collect_blocks([H|T], Acc, Self, Nodes) ->
    Acc1 = collect_block(H, Acc, Self, Nodes),
    collect_blocks(T, Acc1, Self, Nodes).

collect_block(ID, Acc, Self, Nodes) ->
    #{ID := {bb, _, Output, Stmts}} = Nodes,
    Acc1 = collect_stmts(Stmts, Acc, Self, Nodes),
    collect_output(Output, Acc1, Self, Nodes).

collect_stmts([], Acc, _, _) ->
    Acc;
collect_stmts([H|T], Acc, Self, Nodes) ->
    Acc1 = collect_stmt(H, Acc, Self, Nodes),
    collect_stmts(T, Acc1, Self, Nodes).

collect_output(none, Acc, _, _) ->
    Acc;
collect_output({_, Values}, Acc, Self, Nodes) ->
    collect_values(Values, Acc, Self, Nodes);
collect_output({'if', Cond, True, False}, Acc, Self, Nodes) ->
    Acc1 = collect_value(Cond, Acc, Self, Nodes),
    Acc2 = collect_output(True, Acc1, Self, Nodes),
    collect_output(False, Acc2, Self, Nodes).

collect_stmt({'let', ID}, Acc, Self, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    collect_stmt(Expr, Acc, Self, Nodes);
collect_stmt({call, Fun, []}, Acc, Self, Nodes) ->
    collect_values([Fun], Acc, Self, Nodes);
collect_stmt({call, Fun, [Closure|Args]}, Acc, Self, Nodes) ->
    case Nodes of
        #{Fun := {const, _, {fn, ID}}} ->
            case Self of
                {Closure, ID} ->
                    collect_values(Args, Acc, Self, Nodes);
                _ ->
                    case Nodes of
                        #{Closure := {const, _, {op, {cast, up, {fn, ID}}, [TupleID]}}} ->
                            #{TupleID := {const, _, {op, {make, tuple}, [_|List]}}} = Nodes,
                            Acc1 = collect_values(List, Acc, Self, Nodes),
                            collect_values(Args, Acc1, Self, Nodes);
                        #{Closure := {_, _, {op, {cast, up, {fn, ID}}, _}}} ->
                            collect_values(Args, Acc, Self, Nodes);
                        _ ->
                            collect_values([Fun, Closure|Args], Acc, Self, Nodes)
                    end
            end;
        _ ->
            collect_values([Fun, Closure|Args], Acc, Self, Nodes)
    end;
collect_stmt(Stmt, Acc, Self, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    collect_values(List, Acc, Self, Nodes).


collect_values([], Acc, _, _) ->
    Acc;
collect_values([H|T], Acc, Self, Nodes) ->
    Acc1 = collect_value(H, Acc, Self, Nodes),
    collect_values(T, Acc1, Self, Nodes).

collect_value(ID, Acc, {ID, FnID}, _) ->
    Acc#{FnID => []};
collect_value(ID, Acc, Self, Nodes) ->
    #{ID := Node} = Nodes,
    Acc1 =
        case Node of
            {_, _, {op, {cast, up, {fn, FnID}}, _}} ->
                Acc#{FnID => []};
            _ ->
                Acc
        end,
    case Node of
        {const, _, {op, {make, tuple}, List}} ->
            collect_values(List, Acc1, Self, Nodes);
        {const, _, {op, {cast, _, _}, List}} ->
            collect_values(List, Acc1, Self, Nodes);
        _ ->
            Acc1
    end.


convert_fns([], Closures, _, SSA) ->
    {Closures, SSA};
convert_fns([H|T], Closures, Safe, SSA) ->
    {Closures1, SSA1} = convert_fn(H, Closures, Safe, SSA),
    convert_fns(T, Closures1, Safe, SSA1).


convert_fn({ID, []}, Closures, _, SSA) when is_atom(ID) ->
    {Closures, SSA};
convert_fn({ID, Blocks}, Closures, Safe, SSA) when is_integer(ID) ->
    SSA1 =
        if is_map_key(ID, Safe) ->
                destruct_tuple(ID, SSA);
           true ->
                SSA
        end,
    convert_blocks(Blocks, Closures, Safe, SSA1).

destruct_tuple(ID, SSA=#ssa{nodes=Nodes}) ->
    #{ID := {fn, Free, [TupleID|Params], ReturnType, Entry, Exit}} = Nodes,
    case Free of
        [] ->
            mmb_ssa:set_node(ID, {fn, none, Params, ReturnType, Entry, Exit}, SSA);
        _ ->
            #{Entry := {bb, Input, Output, Body}} = Nodes,
            FreeTypes = mmb_ssa:types(Free, Nodes),
            {TupleType, SSA1} = mmb_ssa:typeid({tuple, FreeTypes}, SSA),
            SSA2 = mmb_ssa:set_node(TupleID, {var, TupleType, arg}, SSA1),
            {Body1, SSA3} = destruct(0, Free, FreeTypes, TupleID, Body, SSA2),
            SSA4 = mmb_ssa:set_node(Entry, {bb, Input, Output, Body1}, SSA3),
            mmb_ssa:set_node(ID, {fn, none, [TupleID|Params], ReturnType, Entry, Exit}, SSA4)
    end.

destruct(_, [], [], _, Rest, SSA) ->
    {Rest, SSA};
destruct(Index, [ID|T1], [Type|T2], Expr, Rest, SSA) ->
    SSA1 = mmb_ssa:set_node(ID, {var, Type, {op, {load, tuple, Index}, [Expr]}}, SSA),
    {Rest1, SSA2} = destruct(Index + 1, T1, T2, Expr, Rest, SSA1),
    {[{'let', ID}|Rest1], SSA2}.

convert_blocks([], Closures, _Safe, SSA) ->
    {Closures, SSA};
convert_blocks([H|T], Closures, Safe, SSA) ->
    {Closures1, SSA1} = convert_block(H, Closures, Safe, SSA),
    convert_blocks(T, Closures1, Safe, SSA1).

convert_block(ID, Closures, Safe, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    {Stmts1, Closures1, SSA1} = convert_stmts(Stmts, Closures, Safe, SSA),
    {Closures1, mmb_ssa:set_node(ID, {bb, Input, Output, Stmts1}, SSA1)}.

convert_stmts([], Closures, _Safe, SSA) ->
    {[], Closures, SSA};
convert_stmts([H|T], Closures, Safe, SSA) ->
    {H1, Closures1, SSA1} = convert_stmt(H, Closures, Safe, SSA),
    {T1, Closures2, SSA2} = convert_stmts(T, Closures1, Safe, SSA1),
    {[H1|T1], Closures2, SSA2}.


convert_stmt({'let', ID}=Stmt, Closures, Safe, SSA = #ssa{nodes = Nodes}) ->
    #{ID := {var, Type, Expr}} = Nodes,
    {Expr1, Closures1, SSA1} = convert_stmt(Expr, Closures, Safe, SSA),
    SSA2 = mmb_ssa:set_node(ID, {var, Type, Expr1}, SSA1),
    {Stmt, Closures1, SSA2};
convert_stmt({call, _, []}=Stmt, Closures, _Safe, SSA) ->
    {Stmt, Closures, SSA};
convert_stmt({call, Fun, [ClosureID|Args]}=Stmt, Closures, Safe, SSA=#ssa{nodes=Nodes}) ->
    #{ClosureID := Closure} = Nodes,
    Stmt1 =
        case Nodes of
            #{Fun := {const, _, {fn, ID}}} when is_map_key(ID, Safe) ->
                #{ID := Empty} = Safe,
                case Empty of
                    true ->
                        Closures1 = Closures,
                        {call, Fun, Args};
                    _ ->
                        case Closure of
                            {_, _, {op, {cast, up, {fn, ID}}, [TupleID]}} ->
                                Closures1 = Closures#{ClosureID => []},
                                {call, Fun, [TupleID|Args]};
                            {var, _, arg}->
                                Closures1 = Closures,
                                {call, Fun, [ClosureID|Args]}
                        end
                end;
            _ ->
                Closures1 = Closures,
                Stmt
        end,
    {Stmt1, Closures1, SSA};
convert_stmt(Stmt, Closures, _Safe, SSA) ->
    {Stmt, Closures, SSA}.


convert_closures([], Removed, SSA) ->
    {Removed, SSA};
convert_closures([H|T], Removed, SSA) ->
    {Removed1, SSA1} = convert_closure(H, Removed, SSA),
    convert_closures(T, Removed1, SSA1).

convert_closure(ID, Removed, SSA = #ssa{nodes=Nodes}) ->
    #{ID := Closure = {Kind, _, {op, {cast, up, {fn, _}}, [TupleID]}}} = Nodes,
    #{TupleID := Tuple = {_, _, {op, {make, tuple}, [_|List]}}} = Nodes,
    {Removed1, SSA1} = remove_value(ID, Closure, Removed, SSA),
    {Removed2, SSA2} = remove_value(TupleID, Tuple, Removed1, SSA1),
    case List of
        [] ->
            {Removed2, SSA2};
        _ ->
            Types = mmb_ssa:types(List, Nodes),
            {Type, SSA3} = mmb_ssa:typeid({tuple, Types}, SSA2),
            {maps:remove(TupleID, Removed2), set_value(TupleID, {Kind, Type, {op, {make, tuple}, List}}, SSA3)}
    end.

remove_value(ID, {const, _, _}=Const, Removed, SSA=#ssa{values=Values, nodes=Nodes}) ->
    {Removed, SSA#ssa{nodes=maps:remove(ID, Nodes), values=maps:remove(Const, Values)}};
remove_value(ID, _Value, Removed, SSA=#ssa{nodes=Nodes}) ->
    {Removed#{ID => []}, SSA#ssa{nodes=maps:remove(ID, Nodes)}}.

set_value(ID, {const, _, _}=Const, SSA=#ssa{values=Values}) ->
    Values1 = Values#{Const => ID},
    mmb_ssa:set_node(ID, Const, SSA#ssa{values=Values1});
set_value(ID, Value, SSA) ->
    mmb_ssa:set_node(ID, Value, SSA).


clean_fns([], _Removed, SSA) ->
    SSA;
clean_fns([H|T], Removed, SSA) ->
    SSA1 = clean_fn(H, Removed, SSA),
    clean_fns(T, Removed, SSA1).


clean_fn({ID, []}, _, SSA) when is_atom(ID) ->
    SSA;
clean_fn({ID, Blocks}, Removed, SSA) when is_integer(ID) ->
    clean_blocks(Blocks, Removed, SSA).


clean_blocks([], _, SSA) ->
    SSA;
clean_blocks([H|T], Removed, SSA) ->
    SSA1 = clean_block(H, Removed, SSA),
    clean_blocks(T, Removed, SSA1).

clean_block(ID, Removed, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Stmts1 = clean_stmts(Stmts, Removed),
    mmb_ssa:set_node(ID, {bb, Input, Output, Stmts1}, SSA).


clean_stmts([], _) ->
    [];
clean_stmts([{'let', ID}|Rest], Removed) when is_map_key(ID, Removed) ->
    clean_stmts(Rest, Removed);
clean_stmts([H|T], Removed) ->
    [H|clean_stmts(T, Removed)].
