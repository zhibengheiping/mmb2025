%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_desfree).

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
convert_fn({ID, _Blocks}, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    #{ID := {fn, Free, Params, ReturnType, Entry, Exit}} = Nodes,
    case Free of
        none ->
            SSA;
        _ ->
            [Closure|_]= Params,
            #{Entry := {bb, Input, Output, Body}} = Nodes,
            ParamTypes = mmb_ssa:types(Params, Nodes),
            FreeTypes = mmb_ssa:types(Free, Nodes),
            {FnType, SSA1} = mmb_ssa:typeid({fn, ParamTypes, ReturnType}, SSA),
            {TupleType, SSA2} = mmb_ssa:typeid({tuple, [FnType|FreeTypes]}, SSA1),
            {TupleID, SSA3} = mmb_ssa:add_node({var, TupleType, {op, {cast, down, {fn, ID}}, [Closure]}}, SSA2),
            {Body1, SSA4} = destruct(1, Free, FreeTypes, TupleID, Body, SSA3),
            Body2 = [{'let', TupleID}|Body1],
            SSA5 = mmb_ssa:set_node(Entry, {bb, Input, Output, Body2}, SSA4),
            mmb_ssa:set_node(ID, {fn, none, Params, ReturnType, Entry, Exit}, SSA5)
    end.

destruct(_, [], [], _, Rest, SSA) ->
    {Rest, SSA};
destruct(Index, [ID|T1], [Type|T2], Expr, Rest, SSA) ->
    SSA1 = mmb_ssa:set_node(ID, {var, Type, {op, {load, tuple, Index}, [Expr]}}, SSA),
    {Rest1, SSA2} = destruct(Index + 1, T1, T2, Expr, Rest, SSA1),
    {[{'let', ID}|Rest1], SSA2}.
