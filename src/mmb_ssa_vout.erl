%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_vout).

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
    {Rename, SSA1} = convert_blocks(Blocks, #{}, SSA),
    mmb_ssa:rename_blocks(Blocks, Rename, SSA1).

convert_blocks([], Rename, SSA) ->
    {Rename, SSA};
convert_blocks([H|T], Rename, SSA) ->
    {Rename1, SSA1} = convert_block(H, Rename, SSA),
    convert_blocks(T, Rename1, SSA1).

convert_block(ID, Rename, SSA= #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    {Stmts1, Rename1, SSA1} = convert_stmts(Stmts, Rename, SSA),
    SSA2 = mmb_ssa:set_node(ID, {bb, Input, Output, Stmts1}, SSA1),
    {Rename1, SSA2}.

convert_stmts([], Rename, SSA) ->
    {[], Rename, SSA};
convert_stmts([{'let', ID}|T], Rename, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, Expr}} = Nodes,
    case Expr of
        {op, {store, vref}, [_, Value, Ref]} ->
            {T1, Rename1, SSA1} = convert_stmts(T, Rename#{ID => Ref}, SSA),
            {[{op, {store, ref}, [Value, Ref]}|T1], Rename1, SSA1};
        {op, {make, vref}, [_|List]} ->
            SSA1 = mmb_ssa:set_node(ID, {var, Type, {op, {make, ref}, List}}, SSA),
            {T1, Rename1, SSA2} = convert_stmts(T, Rename, SSA1),
            {[{'let', ID}|T1], Rename1, SSA2};
        {op, {load, vref}, [_|List]} ->
            SSA1 = mmb_ssa:set_node(ID, {var, Type, {op, {load, ref}, List}}, SSA),
            {T1, Rename1, SSA2} = convert_stmts(T, Rename, SSA1),
            {[{'let', ID}|T1], Rename1, SSA2};
        {op, {store, varray}, [_, Value, Array, Index]} ->
            {T1, Rename1, SSA1} = convert_stmts(T, Rename#{ID => Array}, SSA),
            {[{op, {store, array}, [Value, Array, Index]}|T1], Rename1, SSA1};
        {op, {make, varray}, [_|List]} ->
            SSA1 = mmb_ssa:set_node(ID, {var, Type, {op, {make, array}, List}}, SSA),
            {T1, Rename1, SSA2} = convert_stmts(T, Rename, SSA1),
            {[{'let', ID}|T1], Rename1, SSA2};
        {op, {load, varray}, [_|List]} ->
            SSA1 = mmb_ssa:set_node(ID, {var, Type, {op, {load, array}, List}}, SSA),
            {T1, Rename1, SSA2} = convert_stmts(T, Rename, SSA1),
            {[{'let', ID}|T1], Rename1, SSA2};

        {op, poison, [Old]} ->
            convert_stmts(T, Rename#{ID => Old}, SSA);
        _ ->
            {T1, Rename1, SSA1} = convert_stmts(T, Rename, SSA),
            {[{'let',ID}|T1], Rename1, SSA1}
    end;
convert_stmts([H|T], Rename, SSA) ->
    {T1, Rename1, SSA1} = convert_stmts(T, Rename, SSA),
    {[H|T1], Rename1, SSA1}.
