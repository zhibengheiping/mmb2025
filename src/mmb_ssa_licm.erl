%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_licm).

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
convert_fn({ID, Blocks}, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    SrcMap = mmb_ssa:collect_src(Blocks, Nodes),
    DomMap = collect_doms(
               [{Y, X} || {X, L} <- mmb_ssa_dom:doms(Blocks, Nodes),
                          Y <- L], #{}),
    convert_blocks(Blocks, SrcMap, DomMap, SSA).


collect_doms([], Map) ->
    Map;
collect_doms([{X, Y}|T], Map) ->
    M = maps:get(X, Map, #{}),
    M1 = M#{Y => []},
    collect_doms(T, Map#{X => M1}).


convert_blocks([], _, _, SSA) ->
    SSA;
convert_blocks([H|T], SrcMap, DomMap, SSA) ->
    SSA1 = convert_block(H, SrcMap, DomMap, SSA),
    convert_blocks(T, SrcMap, DomMap, SSA1).

convert_block(ID, SrcMap, DomMap, SSA) ->
    Doms = maps:get(ID, DomMap, #{}),
    case maps:get(ID, SrcMap, []) of
        [] ->
            SSA;
        [_] ->
            SSA;
        Srcs ->
            case [S || S <- Srcs, not maps:is_key(S, Doms)] of
                [Pred] ->
                    convert_block(ID, Pred, SSA);
                _ ->
                    SSA
            end
    end.

convert_block(ID, Pred, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Unsafe = maps:from_list([{I, []} || I <- Input]),
    case split(Stmts, Unsafe, Nodes) of
        {[], _} ->
            SSA;
        {Invariant, Stmts1} ->
            SSA1 = mmb_ssa:set_node(ID, {bb, Input, Output, Stmts1}, SSA),
            build_preheader(ID, Pred, Invariant, SSA1)
    end.

split([], _Unsafe, _) ->
    {[], []};
split([{'let', ID}=H|T], Unsafe, Nodes) ->
    #{ID := {var, _Type, Expr}} = Nodes,
    Safe =
        case Expr of
            {call, Fun, Args} ->
                mmb_compute:is_pure(Expr, Nodes) andalso is_all_safe([Fun|Args], Unsafe);
            {op, _Op, List} ->
                mmb_compute:is_pure(Expr, Nodes) andalso is_all_safe(List, Unsafe)
        end,

    Unsafe1 =
        if Safe ->
                Unsafe;
           true ->
                Unsafe#{ID => []}
        end,

    {Invariant, Variant} = split(T, Unsafe1, Nodes),
    if Safe ->
            {[H|Invariant], Variant};
       true ->
            {Invariant, [H|Variant]}
    end;
split([H|T], Unsafe, Nodes) ->
    {Invariant, Variant} = split(T, Unsafe, Nodes),
    {Invariant, [H|Variant]}.


is_all_safe([], _Unsafe) ->
    true;
is_all_safe([H|T], Unsafe) ->
    (not maps:is_key(H, Unsafe)) andalso is_all_safe(T, Unsafe).


build_preheader(ID, Pred, Invariant, SSA=#ssa{nodes=Nodes}) ->
    #{Pred := {bb, Input, Output, Stmts}} = Nodes,
    {Preheader, SSA1} = mmb_ssa:add_node({bb, [], {ID, []}, Invariant}, SSA),
    Output1 =
        case Output of
            {ID, Values} ->
                {Preheader, []};
            {'if', Cond, {ID, Values}, False}->
                {'if', Cond, {Preheader, []}, False};
            {'if', Cond, True, {ID, Values}} ->
                {'if', Cond, True, {Preheader, []}}
        end,
    SSA2 = mmb_ssa:set_node(Pred, {bb, Input, Output1, Stmts}, SSA1),
    mmb_ssa:set_node(Preheader, {bb, [], {ID, Values}, Invariant}, SSA2).
