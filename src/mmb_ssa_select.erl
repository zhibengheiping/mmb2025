%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_select).

-export([convert/1]).

-include("mmb_ssa.hrl").

convert(SSA) ->
    Fns = mmb_ssa:collect_fns(SSA),
    convert(maps:to_list(Fns), SSA).

convert([], SSA) ->
    SSA;
convert([H|T], SSA) ->
    convert(T, convert_fn(H, SSA)).

convert_fn({ID, []}, SSA) when is_atom(ID) ->
    SSA;
convert_fn({ID, Blocks}, SSA) when is_integer(ID) ->
    convert_blocks(Blocks, SSA).


convert_blocks([], SSA) ->
    SSA;
convert_blocks([H|T], SSA) ->
    SSA1 = convert_block(H, SSA),
    convert_blocks(T, SSA1).

convert_block(BlockID, SSA = #ssa{nodes=Nodes}) ->
    #{BlockID := {bb, Input, Output, Stmts}} = Nodes,
    case Output of
        none ->
            SSA;
        {_, _} ->
            SSA;
        {'if', Cond, {LabelT, ValuesT}, {LabelF, ValuesF}} ->
            case Nodes of
                #{LabelT := {bb, InputT, {LabelF, OutputT}, [{'let', ID}]}} ->
                    #{ID := {var, Type, Expr}} = Nodes,
                    case is_simple(Expr) of
                        false ->
                            SSA;
                        true ->
                            {ID1, SSA1} = mmb_ssa:add_node({var, Type, Expr}, SSA),
                            RenameT = rename(InputT, ValuesT, #{ID => ID1}),
                            OutputT1 = rename(OutputT, RenameT),
                            {Output1, Stmts1, SSA2} = combine(Cond, OutputT1, ValuesF, SSA1),
                            {Stmt, SSA3} = mmb_ssa:rename_stmt({'let', ID1}, RenameT, SSA2),
                            Stmts2 = append(Stmts, [Stmt|Stmts1]),
                            mmb_ssa:set_node(BlockID, {bb, Input, {LabelF, Output1}, Stmts2}, SSA3)
                    end;
                #{LabelF := {bb, InputF, {LabelT, OutputF}, [{'let', ID}]}} ->
                    #{ID := {var, Type, Expr}} = Nodes,
                    case is_simple(Expr) of
                        false ->
                            SSA;
                        true ->
                            {ID1, SSA1} = mmb_ssa:add_node({var, Type, Expr}, SSA),
                            RenameF = rename(InputF, ValuesF, #{ID => ID1}),
                            OutputF1 = rename(OutputF, RenameF),
                            {Output1, Stmts1, SSA2} = combine(Cond, ValuesT, OutputF1, SSA1),
                            {Stmt, SSA3} = mmb_ssa:rename_stmt({'let', ID1}, RenameF, SSA2),
                            Stmts2 = append(Stmts, [Stmt|Stmts1]),
                            mmb_ssa:set_node(BlockID, {bb, Input, {LabelT, Output1}, Stmts2}, SSA3)
                    end;
                _ ->
                    SSA
            end
    end.

is_simple({op, Op, _}) ->
    case Op of
        {cmp, _, _} ->
            true;
        {arith, 'Double', '+'} ->
            true;
        {arith, 'Double', neg} ->
            true;
        {arith, 'Double', _} ->
            false;
        {arith, _, _} ->
            true;
        {bool, _} ->
            true;
        select ->
            true;
        is_same_ptr ->
            true;
        _ ->
            false
    end;
is_simple(_) ->
    false.


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
