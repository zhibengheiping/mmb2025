%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_cbc).

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

convert_block(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    case convert_output(Output, Nodes) of
        none ->
            SSA;
        {ok, Output1} ->
            mmb_ssa:set_node(ID, {bb, Input, Output1, Stmts}, SSA)
    end.

convert_output(none, _) ->
    none;
convert_output({_, _}, _) ->
    none;
convert_output({'if', Cond, True, False}, Nodes) ->
    case Nodes of
        #{Cond := {const, 'Bool', Value}} ->
            case Value of
                true ->
                    {ok, True};
                false ->
                    {ok, False}
            end;
        _ ->
            none
    end.
