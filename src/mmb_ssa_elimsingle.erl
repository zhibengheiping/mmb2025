%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimsingle).

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
convert_fn({FnID, Blocks}, SSA = #ssa{nodes=Nodes}) when is_integer(FnID) ->
    #{FnID := {fn, _, _, _, _, Exit}} = Nodes,
    SrcMap =
        maps:from_list(
          [{Dst, Src}
           || {Dst, [Src]} <- maps:to_list(mmb_ssa:collect_src(Blocks, Nodes)),
              Dst =/= Exit]),
    DstMap =
        maps:from_list(
          [{Src, Dst}
           || Src <- Blocks,
              Dst <- collect_dsts(Src, Nodes),
              maps:is_key(Dst, SrcMap)
             ]),
    List = [{Src, maps:get(Src, DstMap)}
            || Src <- tsort(maps:keys(DstMap), #{}, DstMap)],
    {Rename, SSA1} = connect_blocks(List, #{}, SSA),
    Removed = maps:from_list([{Dst, []} || {_, Dst} <- List]),
    Blocks1 = [ID || ID <- Blocks, not maps:is_key(ID, Removed)],
    mmb_ssa:rename_blocks(Blocks1, Rename, SSA1).

collect_dsts(ID, Nodes) ->
    #{ID := {bb, _, Output, _}} = Nodes,
    collect_dsts(Output).

collect_dsts(none) ->
    [];
collect_dsts({ExitID, _}) ->
    [ExitID];
collect_dsts({'if', _, _, _}) ->
    [].

tsort([], _, _) ->
    [];
tsort([H|T], Done, DstMap) ->
    case Done of
        #{H := _} ->
            tsort(T, Done, DstMap);
        _ ->
            #{H := Dst} = DstMap,
            if is_map_key(Dst, DstMap), not is_map_key(Dst, Done) ->
                    tsort([Dst,H|T], Done, DstMap);
                true ->
                    [H|tsort(T, Done#{H => []}, DstMap)]
            end
    end.


connect_blocks([], Rename, SSA) ->
    {Rename, SSA};
connect_blocks([H|T], Rename, SSA) ->
    {Rename1, SSA1} = connect_block(H, Rename, SSA),
    connect_blocks(T, Rename1, SSA1).

connect_block({Src, Dst}, Rename, SSA = #ssa{nodes=Nodes}) ->
    #{Src := {bb, Input, {Dst, Values}, Stmts1}} = Nodes,
    #{Dst := {bb, Input2, Output, Stmts2}} = Nodes,

    Nodes1 = maps:remove(Dst, Nodes),
    Node = {bb, Input, Output, append(Stmts1, Stmts2)},
    SSA1 = mmb_ssa:set_node(Src, Node, SSA#ssa{nodes=Nodes1}),
    {rename(Input2, Values, Rename), SSA1}.

append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].

rename([], [], Rename) ->
    Rename;
rename([H1|T1], [H2|T2], Rename) ->
    rename(T1, T2, Rename#{H1 => H2}).
