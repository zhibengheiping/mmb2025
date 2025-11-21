%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_inlineonce).

-export([convert/1]).

-include("mmb_ssa.hrl").

convert(SSA = #ssa{nodes=Nodes}) ->
    Fns = mmb_ssa:collect_fns(SSA),
    List = maps:to_list(Fns),
    Usage = collect_fns(List, #{}, Nodes),
    Usage1 =
        [{ID, BlockID}
         || {ID, BlockID} <- maps:to_list(Usage),
            BlockID =/= unsafe],

    inline_fns(Usage1, #{}, Fns, SSA).

collect_fns([], Acc, _) ->
    Acc;
collect_fns([H|T], Acc, Nodes) ->
    Acc1 = collect_fn(H, Acc, Nodes),
    collect_fns(T, Acc1, Nodes).

collect_fn({ID, []}, Acc, _) when is_atom(ID) ->
    Acc;
collect_fn({ID, Blocks}, Acc, Nodes) when is_integer(ID) ->
    #{ID := {fn, Free, Params, _, _, _}} = Nodes,
    case Free of
        none ->
            Self = {none, none};
        _ ->
            [Closure|_] = Params,
            Self = {Closure, ID}
    end,
    collect_blocks(Blocks, Acc, ID, Self, Nodes).

collect_blocks([], Acc, _, _, _) ->
    Acc;
collect_blocks([H|T], Acc, ID, Self, Nodes) ->
    Acc1 = collect_block(H, Acc, ID, Self, Nodes),
    collect_blocks(T, Acc1, ID, Self, Nodes).

collect_block(ID, Acc, FnID, Self, Nodes) ->
    #{ID := {bb, _, Output, Stmts}} = Nodes,
    Acc1 = collect_stmts(Stmts, Acc, {FnID, ID}, Self, Nodes),
    collect_output(Output, Acc1, Self, Nodes).

collect_stmts([], Acc, _, _, _) ->
    Acc;
collect_stmts([H|T], Acc, BlockID, Self, Nodes) ->
    Acc1 = collect_stmt(H, Acc, BlockID, Self, Nodes),
    collect_stmts(T, Acc1, BlockID, Self, Nodes).

collect_output(none, Acc, _, _) ->
    Acc;
collect_output({_, Values}, Acc, Self, Nodes) ->
    collect_values(Values, Acc, Self, Nodes);
collect_output({'if', Cond, True, False}, Acc, Self, Nodes) ->
    Acc1 = collect_value(Cond, Acc, Self, Nodes),
    Acc2 = collect_output(True, Acc1, Self, Nodes),
    collect_output(False, Acc2, Self, Nodes).

collect_stmt({'let', ID}, Acc, BlockID, Self, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    collect_stmt(Expr, Acc, BlockID, Self, Nodes);
collect_stmt({call, Fun, []}, Acc, _, Self, Nodes) ->
    collect_values([Fun], Acc, Self, Nodes);
collect_stmt({call, Fun, [Closure|Args]}, Acc, BlockID, Self, Nodes) ->
    case Nodes of
        #{Fun := {const, _, {fn, ID}}} ->
            case Nodes of
                #{Closure := {Kind, _, {op, {cast, up, {fn, ID}}, [TupleID]}}} ->
                    Acc1 =
                        case Acc of
                            #{ID := _} ->
                                Acc#{ID => unsafe};
                            _ ->
                                Acc#{ID => BlockID}
                        end,
                    Acc2 =
                        case Kind of
                            const ->
                                #{TupleID := {const, _, {op, {make, tuple}, [_|List]}}} = Nodes,
                                collect_values(List, Acc1, Self, Nodes);
                            _ ->
                                Acc1
                        end,
                    collect_values(Args, Acc2, Self, Nodes);
                _ ->
                    collect_values([Fun, Closure|Args], Acc, Self, Nodes)
            end;
        _ ->
            collect_values([Fun, Closure|Args], Acc, Self, Nodes)
    end;
collect_stmt(Stmt, Acc, _, Self, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    collect_values(List, Acc, Self, Nodes).


collect_values([], Acc, _, _) ->
    Acc;
collect_values([H|T], Acc, Self, Nodes) ->
    Acc1 = collect_value(H, Acc, Self, Nodes),
    collect_values(T, Acc1, Self, Nodes).

collect_value(ID, Acc, {ID, FnID}, _) ->
    Acc#{FnID => unsafe};
collect_value(ID, Acc, Self, Nodes) ->
    #{ID := Node} = Nodes,
    Acc1 =
        case Node of
            {_, _, {op, {cast, up, {fn, FnID}}, _}} ->
                Acc#{FnID => unsafe};
            _ ->
                Acc
        end,
    case Node of
        {const, _, {op, {make, tuple}, List}} ->
            collect_values(List, Acc1, Self, Nodes);
        {const, _, {op, {cast, _, _}, List}} ->
            collect_values(List, Acc1, Self, Nodes);
        _ ->
            Acc1
    end.


inline_fns([], _, _, SSA) ->
    SSA;
inline_fns([H|T], Split, Fns, SSA) ->
    {Split1, Fns1, SSA1} = inline_fn(H, Split, Fns, SSA),
    inline_fns(T, Split1, Fns1, SSA1).

inline_fn({FnID, {SrcID, BlockID}}, Split, Fns, SSA) ->
    List = maps:get(BlockID, Split, []),
    {ExitID, Closure, TupleID, SSA1} = inline_blocks([BlockID|List], FnID, SSA),
    #{SrcID := Blocks} = Fns,
    SSA2 = elim_blocks(Blocks, #{Closure => [], TupleID => []}, SSA1),
    Fns1 = Fns#{SrcID => [ExitID|Blocks]},
    {Split#{BlockID => [ExitID|List]}, Fns1, SSA2}.

inline_blocks([H|T], FnID, SSA) ->
    case inline_block(H, FnID, SSA) of
        none ->
            inline_blocks(T, FnID, SSA);
        {ExitID, Closure, TupleID, SSA1} ->
            {ExitID, Closure, TupleID, SSA1}
    end.

inline_block(BlockID, FnID, SSA = #ssa{nodes=Nodes}) ->
    #{BlockID := {bb, Input, Output, Stmts}} = Nodes,
    #{FnID := {fn, Free, [_|Params], _ReturnType, Entry, Exit}} = Nodes,
    #{Entry := {bb, [], Output1, Stmts1}} = Nodes,

    case split(Stmts, FnID, Nodes) of
        none ->
            none;
        {Before, Args, Return, After, Closure, TupleID} ->
            Params1 = append(Free, Params),
            Nodes1 = maps:remove(FnID, Nodes),
            SSA1 = set_phis(append(Return, Params1), SSA#ssa{nodes=Nodes1}),
            SSA2 = mmb_ssa:set_node(BlockID, {bb, Input, {Entry, Args}, Before}, SSA1),
            SSA3 = mmb_ssa:set_node(Entry, {bb, Params1, Output1, Stmts1}, SSA2),
            {ExitID, SSA4} = mmb_ssa:add_node({bb, Return, Output, After}, SSA3),
            SSA5 = convert_exit(Exit, ExitID, SSA4),
            {ExitID, Closure, TupleID, SSA5}
    end.

convert_exit(Exit, ExitID, SSA = #ssa{nodes=Nodes}) ->
    #{Exit := {bb, Input, none, [Stmt]}} = Nodes,
    Values =
        case Stmt of
            return ->
                [];
            {return, Expr} ->
                [Expr]
        end,
    mmb_ssa:set_node(Exit, {bb, Input, {ExitID, Values}, []}, SSA).

set_phis([], SSA) ->
    SSA;
set_phis([H|T], SSA) ->
    set_phis(T, set_phi(H, SSA)).

set_phi(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, _}} = Nodes,
    mmb_ssa:set_node(ID, {var, Type, phi}, SSA).


split([], _, _) ->
    none;
split([{'let', ID}=H|T], FnID, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    case Expr of
        {call, Fun, [Closure|Args]} ->
            case Nodes of
                #{Fun := {const, _, {fn, FnID}}} ->
                    #{Closure := {_, _, {op, {cast, up, {fn, FnID}}, [TupleID]}}} = Nodes,
                    #{TupleID := {_, _, {op, {make, tuple}, [_|List]}}} = Nodes,
                    {[], append(List, Args), [ID], T, Closure, TupleID};
                _ ->
                    split(H, T, FnID, Nodes)
            end;
        _ ->
            split(H, T, FnID, Nodes)
    end;
split([{call, Fun, [Closure|Args]}=H|T], FnID, Nodes) ->
    case Nodes of
        #{Fun := {const, _, {fn, FnID}}} ->
            #{Closure := {_, _, {op, {cast, up, {fn, FnID}}, [TupleID]}}} = Nodes,
            #{TupleID := {_, _, {op, {make, tuple}, [_|List]}}} = Nodes,
            {[], append(List, Args), [], T, Closure, TupleID};
        _ ->
            split(H, T, FnID, Nodes)
    end;
split([H|T], FnID, Nodes) ->
    split(H, T, FnID, Nodes).

split(H, T, FnID, Nodes) ->
    case split(T, FnID, Nodes) of
        none ->
            none;
        {Before, Args, Return, After, Closure, TupleID} ->
            {[H|Before], Args, Return, After, Closure, TupleID}
    end.


append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].


elim_blocks([], _, SSA) ->
    SSA;
elim_blocks([H|T], Values, SSA) ->
    elim_blocks(T, Values, elim_block(H, Values, SSA)).

elim_block(ID, Values, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Stmts1 = elim_stmts(Stmts, Values),
    mmb_ssa:set_node(ID, {bb, Input, Output, Stmts1}, SSA).

elim_stmts([], _) ->
    [];
elim_stmts([{'let', ID}|T], Values) when is_map_key(ID, Values) ->
    elim_stmts(T, Values);
elim_stmts([H|T], Values) ->
    [H|elim_stmts(T, Values)].
