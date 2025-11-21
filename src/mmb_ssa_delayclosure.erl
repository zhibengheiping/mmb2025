%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_delayclosure).

-export([convert/1]).

-include("mmb_ssa.hrl").

convert(SSA = #ssa{root=Root}) ->
    Fns = mmb_ssa:collect_fns(SSA),
    convert(maps:to_list(maps:remove(Root, Fns)), SSA).

convert([], SSA) ->
    SSA;
convert([H|T], SSA) ->
    convert(T, convert_fn(H, SSA)).

convert_fn({ID, []}, SSA) when is_atom(ID) ->
    SSA;
convert_fn({ID, [Entry|Blocks]}, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    #{ID := {fn, Free, Params, _, _, _}} = Nodes,
    case Free of
        none ->
            case Params of
                [Closure|_] ->
                    case Nodes of
                        #{Entry := {bb, Input, Output, [{'let', Tuple}|Stmts]}} ->
                            case Nodes of
                                #{Tuple := {var, _, {op, {cast, down, {fn, ID}}, [Closure]}}} ->
                                    {Stmts1, Globals} = collect_closure(Stmts, #{}, Tuple, Nodes),
                                    if map_size(Globals) =:= 0 ->
                                            SSA;
                                       true ->
                                            Uses = collect_stmts(Stmts1, #{}, Nodes),
                                            Uses1 = collect_output(Output, Uses),
                                            Uses2 = maps:with(maps:keys(Globals), Uses1),
                                            Stmts2 = [{'let', Tuple}|append([{'let', X} || X <- maps:keys(Uses2)], Stmts1)],
                                            SSA1 = mmb_ssa:set_node(Entry, {bb, Input, Output, Stmts2}, SSA),
                                            convert_blocks(Blocks, Globals, SSA1)
                                    end;
                                _ ->
                                    SSA
                            end;
                        _ ->
                            SSA
                    end;
                _ ->
                    SSA
            end;
        _ ->
            SSA
    end.


convert_blocks([], _, SSA) ->
    SSA;
convert_blocks([H|T], Globals, SSA) ->
    SSA1 = convert_block(H, Globals, SSA),
    convert_blocks(T, Globals, SSA1).

convert_block(ID, Globals, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Uses = collect_stmts(Stmts, #{}, Nodes),
    Uses1 = collect_output(Output, Uses),
    Uses2 = maps:with(maps:keys(Globals), Uses1),
    {Rename, SSA1} = copy_globals(maps:to_list(maps:with(maps:keys(Uses2), Globals)), #{}, SSA),
    {Stmts1, SSA2} = mmb_ssa:rename_stmts(Stmts, Rename, SSA1),
    Output1 = mmb_ssa:rename_output(Output, Rename),
    Stmts2 = append([{'let', X} || X <- maps:values(Rename)], Stmts1),
    mmb_ssa:set_node(ID, {bb, Input, Output1, Stmts2}, SSA2).

copy_globals([], Acc, SSA) ->
    {Acc, SSA};
copy_globals([{ID, Node}|T], Acc, SSA) ->
    {ID1, SSA1} = mmb_ssa:add_node(Node, SSA),
    copy_globals(T, Acc#{ID => ID1}, SSA1).

collect_closure([{'let', ID}|T]=Stmts, Acc, Tuple, Nodes) ->
    #{ID := Node} = Nodes,
    case Node of
        {var, _, {op, {load, tuple, _}, [Tuple]}} ->
            collect_closure(T, Acc#{ID => Node}, Tuple, Nodes);
        _ ->
            {Stmts, Acc}
    end;
collect_closure(Stmts, Acc, _, _Nodes) ->
    {Stmts, Acc}.


collect_stmts([], Acc, _) ->
    Acc;
collect_stmts([H|T], Acc, Nodes) ->
    Acc1 = collect_stmt(H, Acc, Nodes),
    collect_stmts(T, Acc1, Nodes).

collect_stmt(Stmt, Acc, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    collect_values(List, Acc).

collect_values([], Acc) ->
    Acc;
collect_values([H|T], Acc) ->
    collect_values(T, Acc#{H => []}).

collect_output(none, Acc) ->
    Acc;
collect_output({_, Values}, Acc) ->
    collect_values(Values, Acc);
collect_output({'if', Cond, True, False}, Acc) ->
    Acc1 = Acc#{Cond => []},
    Acc2 = collect_output(True, Acc1),
    collect_output(False, Acc2).


append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].
