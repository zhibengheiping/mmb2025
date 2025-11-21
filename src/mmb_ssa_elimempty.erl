%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimempty).

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
convert_fn({ID, Blocks}, SSA) when is_integer(ID) ->
    SSA1 = #ssa{nodes=Nodes} = convert_blocks(Blocks, SSA),
    #{ID := {fn, Free, Params, ReturnType, Entry, Exit}} = Nodes,
    case Nodes of
        #{Entry := {bb, [], {Entry1, Values}, []}} when Entry1 =/= Exit->
            #{Entry1 := {bb, Input, _, _}} = Nodes,
            case maps:get(Entry1, mmb_ssa:collect_src(Blocks, Nodes), []) of
                [Entry] ->
                    Rename = rename(Input, Values, #{}),
                    SSA2 = #ssa{nodes=Nodes1} = mmb_ssa:rename_blocks(Blocks, Rename, SSA1),
                    #{Entry1 := {bb, _, Output, Stmts}} = Nodes1,
                    SSA3 = mmb_ssa:set_node(Entry1, {bb, [], Output, Stmts}, SSA2),
                    mmb_ssa:set_node(ID, {fn, Free, Params, ReturnType, Entry1, Exit}, SSA3);
                _ ->
                    SSA1
            end;
        _ ->
            SSA1
    end.

convert_blocks([], SSA) ->
    SSA;
convert_blocks([H|T], SSA) ->
    convert_blocks(T, convert_block(H, SSA)).

convert_block(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    case convert_output(Output, Nodes) of
        {'if', Cond, {Label, True}, {Label, False}} ->
            {Output1, Stmts1, SSA1} = combine(Cond, True, False, SSA),
            Stmts2 = append(Stmts, Stmts1),
            mmb_ssa:set_node(ID, {bb, Input, {Label, Output1}, Stmts2}, SSA1);
        Output1 ->
            mmb_ssa:set_node(ID, {bb, Input, Output1, Stmts}, SSA)
    end.

convert_output(none, _) ->
    none;
convert_output({ExitID, List}, Nodes) ->
    #{ExitID := {bb, Input, Output, Stmts}} = Nodes,
    case Stmts of
        [] ->
            Rename = rename(Input, List, #{}),
            case convert_output(Output, Nodes) of
                {'if', Cond, {True, ListT}, {False, ListF}} ->
                    {'if', maps:get(Cond, Rename, Cond), {True, rename(ListT, Rename)}, {False, rename(ListF, Rename)}};
                {Exit1, List1} ->
                    {Exit1, rename(List1, Rename)};
                _ ->
                    {ExitID, List}
            end;
        _ ->
            {ExitID, List}
    end;
convert_output({'if', Cond, True, False}, Nodes) ->
    True1 = convert_single_output(True, Nodes),
    False1 = convert_single_output(False, Nodes),
    {'if', Cond, True1, False1}.

convert_single_output({ExitID, List}, Nodes) ->
    #{ExitID := {bb, Input, Output, Stmts}} = Nodes,
    case Stmts of
        [] ->
            case Output of
                {_, _} ->
                    Rename = rename(Input, List, #{}),
                    {Exit2, List2} = convert_single_output(Output, Nodes),
                    {Exit2, rename(List2, Rename)};
                _ ->
                    {ExitID, List}
            end;
        _ ->
            {ExitID, List}
    end.

combine(_Cond, [], [], SSA) ->
    {[], [], SSA};
combine(Cond, [H|T1], [H|T2], SSA) ->
    {Output, Stmts, SSA1} = combine(Cond, T1, T2, SSA),
    {[H|Output], Stmts, SSA1};
combine(Cond, [H1|T1], [H2|T2], SSA = #ssa{nodes=Nodes}) ->
    #{H1 := {_, Type, _}} = Nodes,
    {ID, SSA1} = mmb_ssa:add_node({var, Type, {op, select, [Cond, H1, H2]}}, SSA),
    {Output, Stmts, SSA2} = combine(Cond, T1, T2, SSA1),
    {[ID|Output], [{'let', ID}|Stmts], SSA2}.

append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].

rename(List, Rename) ->
    [maps:get(ID, Rename, ID) || ID <- List].

rename([], [], Rename) ->
    Rename;
rename([H1|T1], [H2|T2], Rename) ->
    rename(T1, T2, Rename#{H1 => H2}).
