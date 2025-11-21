%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_llvm_return).

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
    #{ID := {fn, none, Params, ReturnType, Entry, Exit}} = Nodes,
    #{Exit := {bb, Input, none, [Stmt]}} = Nodes,
    SrcMap = mmb_ssa:collect_src(Blocks, Nodes),
    Srcs = maps:get(Exit, SrcMap, []),

    case [X || X <- Srcs, is_single_exit(X, Nodes)] of
        [] ->
            SSA;
        List ->
            SSA1 =
                case Stmt of
                    return ->
                        convert_void_blocks(List, SSA);
                    {return, Expr} ->
                        case Input of
                            [Expr] ->
                                convert_blocks(List, SSA);
                            [] ->
                                convert_blocks(List, Expr, SSA)
                        end
                end,
            mmb_ssa:set_node(ID, {fn, none, Params, ReturnType, Entry, none}, SSA1)
    end.

is_single_exit(ID, Nodes) ->
    #{ID := {bb, _, Output, _}} = Nodes,
    case Output of
        {_, _} ->
            true;
        _ ->
            false
    end.


convert_void_blocks([], SSA) ->
    SSA;
convert_void_blocks([H|T], SSA) ->
    SSA1 = convert_void_block(H, SSA),
    convert_void_blocks(T, SSA1).

convert_void_block(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, _, Stmts}} = Nodes,
    Stmts1 = append(Stmts, [return]),
    mmb_ssa:set_node(ID, {bb, Input, none, Stmts1}, SSA).


convert_blocks([], SSA) ->
    SSA;
convert_blocks([H|T], SSA) ->
    SSA1 = convert_block(H, SSA),
    convert_blocks(T, SSA1).

convert_block(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, {_, [X]}, Stmts}} = Nodes,
    Stmts1 = append(Stmts, [{return, X}]),
    mmb_ssa:set_node(ID, {bb, Input, none, Stmts1}, SSA).


convert_blocks([], _, SSA) ->
    SSA;
convert_blocks([H|T], Expr, SSA) ->
    SSA1 = convert_block(H, Expr, SSA),
    convert_blocks(T, Expr, SSA1).

convert_block(ID, Expr, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, _, Stmts}} = Nodes,
    Stmts1 = append(Stmts, [{return, Expr}]),
    mmb_ssa:set_node(ID, {bb, Input, none, Stmts1}, SSA).


append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].
