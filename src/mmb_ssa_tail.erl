%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_tail).

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
    #{ID := {fn, Free, Params, ReturnType, Entry, Exit}} = Nodes,
    case Free of
        none ->
            #{Exit := {bb, Input, none, [Stmt]}} = Nodes,
            SrcMap = mmb_ssa:collect_src(Blocks, Nodes),
            Srcs = maps:get(Exit, SrcMap, []),
            TailCalls =
                case Stmt of
                    return ->
                        [X || X <- Srcs, has_tail_stmt(X, Exit, ID, Nodes)];
                    {return, Expr} ->
                        case Input of
                            [Expr] ->
                                [X || X <- Srcs, has_tail_expr(X, Exit, ID, Nodes)];
                            _ ->
                                []
                        end
                end,
            case TailCalls of
                [] ->
                    SSA;
                _ ->
                    {Params1, SSA1} = copy_params(Params, SSA),
                    {Entry1, SSA2} = mmb_ssa:add_node({bb, Params, {Entry, []}, []}, SSA1),
                    {Entry2, SSA3} = mmb_ssa:add_node({bb, [], {Entry1, Params1}, []}, SSA2),
                    SSA4 = convert_blocks(TailCalls, Entry1, SSA3),
                    mmb_ssa:set_node(ID, {fn, none, Params1, ReturnType, Entry2, Exit}, SSA4)
            end;
        _ ->
            SSA
    end.

copy_params([], SSA) ->
    {[], SSA};
copy_params([H|T], SSA) ->
    {H1, SSA1} = copy_param(H, SSA),
    {T1, SSA2} = copy_params(T, SSA1),
    {[H1|T1], SSA2}.

copy_param(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, arg}} = Nodes,
    SSA1 = mmb_ssa:set_node(ID, {var, Type, phi}, SSA),
    mmb_ssa:add_node({var, Type, arg}, SSA1).


has_tail_stmt(BlockID, Exit, FnID, Nodes) ->
    #{BlockID := {bb, _, Output, Stmts}} = Nodes,
    case Output of
        {Exit, _} ->
            case tail_stmt(Stmts) of
                {call, Fun, _} ->
                    case Nodes of
                        #{Fun := {const, _, {fn, FnID}}} ->
                            true;
                        _ ->
                            false
                    end;
                _ ->
                    false
            end;
        _ ->
            false
    end.

tail_stmt([]) ->
    none;
tail_stmt([E]) ->
    E;
tail_stmt([_|T]) ->
    tail_stmt(T).

has_tail_expr(BlockID, Exit, FnID, Nodes) ->
    #{BlockID := {bb, _, Output, Stmts}} = Nodes,
    case Output of
        {Exit, [ID]} ->
            case tail_stmt(Stmts) of
                {'let', ID} ->
                    #{ID := {var, _, Expr}} = Nodes,
                    case Expr of
                        {call, Fun, _} ->
                            case Nodes of
                                #{Fun := {const, _, {fn, FnID}}} ->
                                    true;
                                _ ->
                                    false
                            end;
                        _ ->
                            false
                    end;
                _ ->
                    false
            end;
        _ ->
            false
    end.


convert_blocks([], _, SSA) ->
    SSA;
convert_blocks([H|T], Entry, SSA) ->
    SSA1 = convert_block(H, Entry, SSA),
    convert_blocks(T, Entry, SSA1).

convert_block(ID, Entry, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, _, Stmts}} = Nodes,
    {Stmts1, Values} = split(Stmts, Nodes),
    mmb_ssa:set_node(ID, {bb, Input, {Entry, Values}, Stmts1}, SSA).

split([{call, _, Args}], _Nodes) ->
    {[], Args};
split([{'let', ID}], Nodes) ->
    #{ID := {var, _, {call, _, Args}}} = Nodes,
    {[], Args};
split([H|T], Nodes) ->
    {T1, Values} = split(T, Nodes),
    {[H|T1], Values}.
