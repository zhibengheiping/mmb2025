%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_vin).

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
convert_fn({ID, Blocks}, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    #{ID := {fn, Free, Params, ReturnType, Entry, Exit}} = Nodes,
    Args =
        case Free of
            none ->
                Params;
            _ ->
                append(Free, Params)
        end,
    SrcMap = mmb_ssa:collect_src(Blocks, Nodes),
    Defined = collect_inputs(Args, #{}, fn, Nodes),

    {Defined1, Uses} = collect_blocks(Blocks, Defined, #{}, Nodes),

    Alias = mmb_ssa_alias:analysis(ID, Blocks, Nodes),
    Versions = maps:keys(maps:from_list([{mmb_alias:get_group(Key, Alias), []} || Key <- maps:keys(Defined1)])),

    List =
        [ {Var, BlockID}
          || {Var, M} <- maps:to_list(Uses),
             maps:is_key(Var, Defined1),
             BlockID <- maps:keys(M)],

    Uses1 = propagate({List, []}, #{}, Defined1, SrcMap),
    Containers = maps:keys(Defined1),

    SSA1 = convert_blocks(Blocks, Containers, Defined1, Uses1, Versions, Alias, SSA),

    {Zero, SSA2} = add_const({const, 'Int', 0}, SSA1),

    Usage = maps:get(Entry, Uses1, #{}),
    Values = [X || X <- Containers, maps:is_key(X, Usage)],
    Versions1 = [ Zero || _ <- Versions],
    {Entry1, SSA3} = mmb_ssa:add_node({bb, [], {Entry, append(Versions1,Values)}, []}, SSA2),
    mmb_ssa:set_node(ID, {fn, Free, Params, ReturnType, Entry1, Exit}, SSA3).

add_const(Const, SSA = #ssa{values=Values}) ->
    case Values of
        #{Const := ID} ->
            {ID, SSA};
        _ ->
            {ID, SSA1} = mmb_ssa:add_node(Const, SSA),
            {ID, SSA1#ssa{values=Values#{Const => ID}}}
    end.


collect_blocks([], Defined, Uses, _) ->
    {Defined, Uses};
collect_blocks([H|T], Defined, Uses, Nodes) ->
    {Defined1, Uses1} = collect_block(H, Defined, Uses, Nodes),
    collect_blocks(T, Defined1, Uses1, Nodes).

collect_block(ID, Defined, Uses, Nodes) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Defined1 = collect_inputs(Input, Defined, ID, Nodes),
    {Defined2, Uses1} = collect_stmts(Stmts, Defined1, Uses, ID, Nodes),
    Uses2 = collect_output(Output, Uses1, ID),
    {Defined2, Uses2}.

collect_output(none, Uses, _) ->
    Uses;
collect_output({_, Values}, Uses, BlockID) ->
    mark_uses(Values, BlockID, Uses);
collect_output({'if', Cond, True, False}, Uses, BlockID) ->
    Uses1 = mark_use(Cond, BlockID, Uses),
    Uses2 = collect_output(True, Uses1, BlockID),
    collect_output(False, Uses2, BlockID).

collect_inputs([], Defined, _, _) ->
    Defined;
collect_inputs([H|T], Defined, BlockID, Nodes) ->
    Defined1 = collect_input(H, Defined, BlockID, Nodes),
    collect_inputs(T, Defined1, BlockID, Nodes).

collect_input(ID, Defined, BlockID, Nodes) ->
    #{ID := {var, TypeID, _}} = Nodes,
    if is_atom(TypeID) ->
            Defined;
       true ->
            #{TypeID := {type, Type}} = Nodes,
            case Type of
                {ref, _} ->
                    Defined#{ID => BlockID};
                {array, _} ->
                    Defined#{ID => BlockID};
                _ ->
                    Defined
            end
    end.


collect_stmts([], Defined, Uses, _, _) ->
    {Defined, Uses};
collect_stmts([H|T], Defined, Uses, BlockID, Nodes) ->
    {Defined1, Uses1} = collect_stmt(H, Defined, Uses, BlockID, Nodes),
    collect_stmts(T, Defined1, Uses1, BlockID, Nodes).

collect_stmt({'let', ID}, Defined, Uses, BlockID, Nodes) ->
    #{ID := {var, TypeID, Expr}} = Nodes,
    Defined1 =
        if is_atom(TypeID) ->
                Defined;
           true ->
                #{TypeID := {type, Type}} = Nodes,
                case Type of
                    {ref, _} ->
                        Defined#{ID => BlockID};
                    {array, _} ->
                        Defined#{ID => BlockID};
                    _ ->
                        Defined
                end
        end,
    collect_stmt(Expr, Defined1, Uses, BlockID, Nodes);
collect_stmt(fail, Defined, Uses, _, _) ->
    {Defined, Uses};
collect_stmt(return, Defined, Uses, _, _) ->
    {Defined, Uses};
collect_stmt({return, Expr}, Defined, Uses, BlockID, _) ->
    {Defined, mark_use(Expr, BlockID, Uses)};
collect_stmt({op, _, List}, Defined, Uses, BlockID, _) ->
    {Defined, mark_uses(List, BlockID, Uses)};
collect_stmt({call, Fun, Args}, Defined, Uses, BlockID, _) ->
    {Defined, mark_uses([Fun|Args], BlockID, Uses)}.

mark_uses([], _, Uses) ->
    Uses;
mark_uses([H|T], BlockID, Uses) ->
    Uses1 = mark_use(H, BlockID, Uses),
    mark_uses(T, BlockID, Uses1).

mark_use(ID, BlockID, Uses) ->
    U = maps:get(ID, Uses, #{}),
    U1 = U#{BlockID => []},
    Uses#{ID => U1}.


propagate(Queue, Uses, Defined, SrcMap) ->
    case mmb_queue:pop(Queue) of
        none ->
            Uses;
        {{Container, BlockID}, Queue1} ->
            case Defined of
                #{Container := BlockID} ->
                    propagate(Queue1, Uses, Defined, SrcMap);
                _ ->
                    case maps:get(BlockID, Uses, #{}) of
                        #{Container := _} ->
                            propagate(Queue1, Uses, Defined, SrcMap);
                        U ->
                            U1 = U#{Container => []},
                            Uses1 = Uses#{BlockID => U1},
                            Queue2 = queue_srcs(maps:get(BlockID, SrcMap, []), Container, Queue1),
                            propagate(Queue2, Uses1, Defined, SrcMap)
                    end
            end
    end.

queue_srcs([], _, Queue) ->
    Queue;
queue_srcs([H|T], Container, Queue) ->
    queue_srcs(T, Container, mmb_queue:push({Container, H}, Queue)).


convert_blocks([], _, _Defined, _Uses, _, _, SSA) ->
    SSA;
convert_blocks([H|T], Containers, Defined, Uses, Versions, Alias, SSA) ->
    SSA1 = convert_block(H, Containers, Defined, Uses, Versions, Alias, SSA),
    convert_blocks(T, Containers, Defined, Uses, Versions, Alias, SSA1).

convert_block(ID, Containers, Defined, Uses, Versions, Alias, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Usage = maps:get(ID, Uses, #{}),
    {Versions1, VersionMap, SSA1} = create_versions(Versions, #{}, SSA),
    {Phi, ContainerMap, SSA2} = create_phis(Containers, Defined, ID, Usage, SSA1),
    ContainerMap1 = gather_inputs(Input, ContainerMap, Nodes),
    {Stmts1, ContainerMap2, VersionMap1, SSA3} = convert_stmts(Stmts, ContainerMap1, VersionMap, Alias, SSA2),
    Output1 = convert_output(Output, Containers, ContainerMap2, Versions, VersionMap1, Uses),
    mmb_ssa:set_node(ID, {bb, append(Versions1, append(Phi, Input)), Output1, Stmts1}, SSA3).

create_versions([], VersionMap, SSA) ->
    {[], VersionMap, SSA};
create_versions([H|T], VersionMap, SSA) ->
    {ID, SSA1} = mmb_ssa:add_node({var, 'Int', phi}, SSA),
    {T1, VersionMap1, SSA2} = create_versions(T, VersionMap#{H => ID}, SSA1),
    {[ID|T1], VersionMap1, SSA2}.

gather_inputs([], ContainerMap, _) ->
    ContainerMap;
gather_inputs([H|T], ContainerMap, Nodes) ->
    ContainerMap1 = gather_input(H, ContainerMap, Nodes),
    gather_inputs(T, ContainerMap1, Nodes).

gather_input(ID, ContainerMap, Nodes) ->
    #{ID := {var, TypeID, _}} = Nodes,
    if is_atom(TypeID) ->
            ContainerMap;
       true ->
            #{TypeID := {type, Type}} = Nodes,
            case Type of
                {ref, _} ->
                    ContainerMap#{ID => ID};
                {array, _} ->
                    ContainerMap#{ID => ID};
                _ ->
                    ContainerMap
            end
    end.

create_phis([], _, _, _, SSA) ->
    {[], #{}, SSA};
create_phis([H|T], Defined, BlockID, Usage, SSA = #ssa{nodes=Nodes}) when map_get(H, Defined) =/= BlockID, is_map_key(H, Usage) ->
    #{H := {var, Type, _}} = Nodes,
    {H1, SSA1} = mmb_ssa:add_node({var, Type, phi}, SSA),
    {T1, ContainerMap, SSA2} = create_phis(T, Defined, BlockID, Usage, SSA1),
    {[H1|T1], ContainerMap#{H => H1}, SSA2};
create_phis([_|T], Defined, BlockID, Usage, SSA) ->
    create_phis(T, Defined, BlockID, Usage, SSA).


convert_stmts([], ContainerMap, VersionMap, _, SSA) ->
    {[], ContainerMap, VersionMap, SSA};
convert_stmts([{'let', ID}|T], ContainerMap, VersionMap, Alias, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, TypeID, Expr}} = Nodes,

    {Stmts, VersionMap1, SSA1} = convert_expr(ID, TypeID, Expr, ContainerMap, VersionMap, Alias, SSA),

    if is_atom(TypeID) ->
            ContainerMap1 = ContainerMap;
       true ->
            #{TypeID := {type, Type}} = Nodes,
            ContainerMap1 =
                case Type of
                    {ref, _} ->
                        ContainerMap#{ID => ID};
                    {array, _} ->
                        ContainerMap#{ID => ID};
                    _ ->
                        ContainerMap
                end
    end,
    {T1, ContainerMap2, VersionMap2, SSA2} = convert_stmts(T, ContainerMap1, VersionMap1, Alias, SSA1),
    {append(Stmts,T1), ContainerMap2, VersionMap2, SSA2};
convert_stmts([{op, {store, ref}, [Value, Ref]}|T], ContainerMap, VersionMap, Alias, SSA = #ssa{nodes=Nodes}) ->
    #{Ref := {var, Type, _}} = Nodes,
    Ref1 = maps:get(Ref, ContainerMap, Ref),
    Value1 = maps:get(Value, ContainerMap, Value),

    Group = mmb_alias:get_group(Ref, Alias),
    Version = maps:get(Group, VersionMap),

    {Version1, SSA1} = mmb_ssa:add_node({var, 'Int', {op, poison, [Version]}}, SSA),
    VersionMap1 = VersionMap#{Group => Version1},

    {ID, SSA2} = mmb_ssa:add_node({var, Type, {op, {store, vref}, [Version1, Value1, Ref1]}}, SSA1),
    ContainerMap1 = ContainerMap#{Ref => ID},

    {T1, ContainerMap2, VersionMap2, SSA3} = convert_stmts(T, ContainerMap1, VersionMap1, Alias, SSA2),
    {[{'let', Version1}, {'let', ID}|T1], ContainerMap2, VersionMap2, SSA3};
convert_stmts([{op, {store, array}, [Value, Array, Index]}|T], ContainerMap, VersionMap, Alias, SSA = #ssa{nodes=Nodes}) ->
    #{Array := {var, Type, _}} = Nodes,
    Array1 = maps:get(Array, ContainerMap, Array),
    Value1 = maps:get(Value, ContainerMap, Value),

    Group = mmb_alias:get_group(Array, Alias),
    Version = maps:get(Group, VersionMap),

    {Version1, SSA1} = mmb_ssa:add_node({var, 'Int', {op, poison, [Version]}}, SSA),
    VersionMap1 = VersionMap#{Group => Version1},

    {ID, SSA2} = mmb_ssa:add_node({var, Type, {op, {store, varray}, [Version1, Value1, Array1, Index]}}, SSA1),
    ContainerMap1 = ContainerMap#{Array => ID},

    {T1, ContainerMap2, VersionMap2, SSA3} = convert_stmts(T, ContainerMap1, VersionMap1, Alias, SSA2),
    {[{'let', Version1}, {'let', ID}|T1], ContainerMap2, VersionMap2, SSA3};
convert_stmts([{call, Fun, Args}|T], ContainerMap, VersionMap, Alias, SSA = #ssa{nodes=Nodes}) ->
    H = {call, Fun, [maps:get(X, ContainerMap, X) || X <- Args]},
    Groups = maps:keys(mmb_alias:get_members(filter_const(Args, Nodes), Alias)),
    Groups1 = [G || G <- Groups, maps:is_key(G, VersionMap)],
    {Poison, VersionMap1, SSA1} = poison_aliases(Groups1, VersionMap, SSA),
    {T1, ContainerMap1, VersionMap2, SSA2} = convert_stmts(T, ContainerMap, VersionMap1, Alias, SSA1),
    {[H|append(Poison, T1)], ContainerMap1, VersionMap2, SSA2};
convert_stmts([H|T], ContainerMap, VersionMap, Alias, SSA) ->
    H1 = convert_stmt(H, ContainerMap),
    {T1, ContainerMap1, VersionMap1, SSA1} = convert_stmts(T, ContainerMap, VersionMap, Alias, SSA),
    {[H1|T1], ContainerMap1, VersionMap1, SSA1}.

poison_aliases([], VersionMap, SSA) ->
    {[], VersionMap, SSA};
poison_aliases([H|T], VersionMap, SSA) ->
    {H1, VersionMap1, SSA1} = poison_alias(H, VersionMap, SSA),
    {T1, VersionMap2, SSA2} = poison_aliases(T, VersionMap1, SSA1),
    {[H1|T1], VersionMap2, SSA2}.

poison_alias(ID, VersionMap, SSA) ->
    Version = maps:get(ID, VersionMap),
    {Version1, SSA1} = mmb_ssa:add_node({var, 'Int', {op, poison,[Version]}}, SSA),
    {{'let', Version1}, VersionMap#{ID => Version1}, SSA1}.

convert_stmt(fail, _) ->
    fail;
convert_stmt(return, _) ->
    return;
convert_stmt({return, Expr}, ContainerMap) ->
    {return, maps:get(Expr, ContainerMap, Expr)}.

convert_expr(ID, Type, {op, {load, ref}, [Ref]}, ContainerMap, VersionMap, Alias, SSA) ->
    Group = mmb_alias:get_group(Ref, Alias),
    Version = maps:get(Group, VersionMap),
    Expr = {op, {load, vref}, [Version, maps:get(Ref, ContainerMap)]},
    SSA1 = mmb_ssa:set_node(ID, {var, Type, Expr}, SSA),
    {[{'let', ID}], VersionMap, SSA1};
convert_expr(ID, Type, {op, {load, array}, [Array, Index]}, ContainerMap, VersionMap, Alias, SSA) ->
    Group = mmb_alias:get_group(Array, Alias),
    Version = maps:get(Group, VersionMap),
    Expr = {op, {load, varray}, [Version, maps:get(Array, ContainerMap), Index]},
    SSA1 = mmb_ssa:set_node(ID, {var, Type, Expr}, SSA),
    {[{'let', ID}], VersionMap, SSA1};
convert_expr(ID, Type, {op, {make, ref}, [Value]}, ContainerMap, VersionMap, Alias, SSA) ->
    Group = mmb_alias:get_group(ID, Alias),
    Version = maps:get(Group, VersionMap),
    {Version1, SSA1} = mmb_ssa:add_node({var, 'Int', {op, poison, [Version]}}, SSA),
    VersionMap1 = VersionMap#{Group => Version1},
    Expr = {op, {make, vref}, [Version1, maps:get(Value, ContainerMap, Value)]},
    SSA2 = mmb_ssa:set_node(ID, {var, Type, Expr}, SSA1),
    {[{'let', Version1}, {'let', ID}], VersionMap1, SSA2};
convert_expr(ID, Type, {op, {make, array}, [N]}, _ContainerMap, VersionMap, Alias, SSA) ->
    Group = mmb_alias:get_group(ID, Alias),
    Version = maps:get(Group, VersionMap),
    {Version1, SSA1} = mmb_ssa:add_node({var, 'Int', {op, poison, [Version]}}, SSA),
    VersionMap1 = VersionMap#{Group => Version1},
    Expr = {op, {make, varray}, [Version1, N]},
    SSA2 = mmb_ssa:set_node(ID, {var, Type, Expr}, SSA1),
    {[{'let', Version1}, {'let', ID}], VersionMap1, SSA2};
convert_expr(ID, Type, {op, {make, array}, [N, K]}, ContainerMap, VersionMap, Alias, SSA) ->
    Group = mmb_alias:get_group(ID, Alias),
    Version = maps:get(Group, VersionMap),
    {Version1, SSA1} = mmb_ssa:add_node({var, 'Int', {op, poison, [Version]}}, SSA),
    VersionMap1 = VersionMap#{Group => Version1},
    Expr = {op, {make, varray}, [Version1, N, maps:get(K, ContainerMap, K)]},
    SSA2 = mmb_ssa:set_node(ID, {var, Type, Expr}, SSA1),
    {[{'let', Version1}, {'let', ID}], VersionMap1, SSA2};
convert_expr(ID, Type, {call, Fun, Args}, ContainerMap, VersionMap, Alias, SSA = #ssa{nodes=Nodes}) ->
    Expr = {call, Fun, [maps:get(X, ContainerMap, X) || X <- Args]},
    SSA1 = mmb_ssa:set_node(ID, {var, Type, Expr}, SSA),
    Groups = maps:keys(mmb_alias:get_members(filter_const([ID|Args], Nodes), Alias)),
    Groups1 = [G || G <- Groups, maps:is_key(G, VersionMap)],
    {Poison, VersionMap1, SSA2} = poison_aliases(Groups1, VersionMap, SSA1),
    {[{'let', ID}|Poison], VersionMap1, SSA2};
convert_expr(ID, Type, {op, Op, List}, ContainerMap, VersionMap, _, SSA) ->
    Expr = {op, Op, [maps:get(X, ContainerMap, X) || X <- List]},
    SSA1 = mmb_ssa:set_node(ID, {var, Type, Expr}, SSA),
    {[{'let', ID}], VersionMap, SSA1}.

convert_output(none, _, _, _, _, _) ->
    none;
convert_output({ExitID, Values}, Containers, ContainerMap, Versions, VersionMap, Uses) ->
    Usage = maps:get(ExitID, Uses, #{}),
    Versions1 = [maps:get(V, VersionMap) || V <- Versions],
    Values1 = [maps:get(X, ContainerMap, X) || X <- Values],
    {ExitID, append(Versions1, append(convert_phis(Containers, Usage, ContainerMap), Values1))};
convert_output({'if', Cond, True, False}, Containers, ContainerMap, Versions, VersionMap, Uses) ->
    True1 = convert_output(True, Containers, ContainerMap, Versions, VersionMap, Uses),
    False1 = convert_output(False, Containers, ContainerMap, Versions, VersionMap, Uses),
    {'if', Cond, True1, False1}.

convert_phis([], _, _) ->
    [];
convert_phis([H|T], Usage, ContainerMap) when is_map_key(H, Usage) ->
    #{H := H1} = ContainerMap,
    [H1|convert_phis(T, Usage, ContainerMap)];
convert_phis([_|T], Usage, ContainerMap) ->
    convert_phis(T, Usage, ContainerMap).


append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].



is_const(ID, Nodes) ->
    #{ID := {Kind, _, _}} = Nodes,
    case Kind of
        const ->
            true;
        _ ->
            false
    end.


filter_const([], _) ->
    [];
filter_const([H|T], Nodes) ->
    case is_const(H, Nodes) of
        true ->
            filter_const(T, Nodes);
        false ->
            [H|filter_const(T, Nodes)]
    end.
