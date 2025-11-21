%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_global).

-export([convert/1]).

-include("mmb_ssa.hrl").

convert(SSA = #ssa{root=Root, nodes=Nodes}) ->
    Fns = mmb_ssa:collect_fns(SSA),
    List = maps:to_list(Fns),
    NonRoot = [X || {ID, _}= X <- List, ID=/=Root],
    {Consumers, ValueMap} = collect_fns(NonRoot, #{}, #{}, Nodes),
    ValueList = maps:to_list(ValueMap),
    BadList = [ID || {ID, bad} <- ValueList],
    BadList1 = propagate_bad({BadList, []}, #{}, Consumers),
    Consumers1 = maps:from_list(
      [{X, maps:keys(maps:without(BadList1, M))}
       || {X, M} <- maps:to_list(Consumers)]),
    ValueMap1 = maps:merge(ValueMap, maps:from_list([{ID, bad} || ID <- BadList1])),

    Queue = queue_blocks(maps:get(Root, Fns), mmb_queue:init(), Nodes),
    ValueMap2 = propagate_value(Queue, ValueMap1, Consumers1),
    ValueMap3 =
        maps:from_list(
          [{ID, ValueID}
           || {ID, ValueID} <- maps:to_list(ValueMap2),
              ValueID =/= bad]),

    SSA1 = convert_fns(List, ValueMap3, SSA),
    SSA2 = convert_frees(NonRoot, ValueMap3, SSA1),
    Globals =
        maps:from_list(
          [{ID, []}
           || ID <- maps:values(ValueMap3),
              is_var(ID, Nodes)]),
    convert_root(maps:get(Root, Fns), Globals, SSA2).

is_var(ID, Nodes) ->
    case Nodes of
        #{ID := {var, _, _}} ->
            true;
        _ ->
            false
    end.

queue_blocks([], Queue, _Nodes) ->
    Queue;
queue_blocks([H|T], Queue, Nodes) ->
    Queue1 = queue_block(H, Queue, Nodes),
    queue_blocks(T, Queue1, Nodes).

queue_block(ID, Queue, Nodes) ->
    #{ID := {bb, _, Output, Stmts}} = Nodes,
    Queue1 = queue_stmts(Stmts, Queue, Nodes),
    queue_output(Output, Queue1, Nodes).

queue_stmts([], Queue, _) ->
    Queue;
queue_stmts([H|T], Queue, Nodes) ->
    Queue1 = queue_stmt(H, Queue, Nodes),
    queue_stmts(T, Queue1, Nodes).

queue_stmt(Stmt, Queue, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    queue_values(List, Queue, Nodes).

queue_output(none, Queue, _) ->
    Queue;
queue_output({_, List}, Queue, Nodes) ->
    queue_values(List, Queue, Nodes);
queue_output({'if', Cond, True, False}, Queue, Nodes) ->
    Queue1 = queue_value(Cond, Queue, Nodes),
    Queue2 = queue_output(True, Queue1, Nodes),
    queue_output(False, Queue2, Nodes).

queue_values([], Queue, _) ->
    Queue;
queue_values([H|T], Queue, Nodes) ->
    Queue1 = queue_value(H, Queue, Nodes),
    queue_values(T, Queue1, Nodes).

queue_value(ID, Queue, Nodes) ->
    #{ID := Node} = Nodes,
    case Node of
        {_, _, {op, {cast, up, {fn, FnID}}, [TupleID]}} ->
            #{TupleID := {_, _, {op, {make, tuple}, [_|Args]}}} = Nodes,
            #{FnID := {fn, Free, _, _, _, _}} = Nodes,
            Queue1 = queue_pairs(Free, Args, Queue);
        _ ->
            Queue1 = Queue
    end,

    case Node of
        {const, _, {op, {cast, _, _},  List}} ->
            queue_values(List, Queue1, Nodes);
        {const, _, {op, {make, tuple},  List}} ->
            queue_values(List, Queue1, Nodes);
        _ ->
            Queue1
    end.

queue_pairs([], [], Queue) ->
    Queue;
queue_pairs([H1|T1], [H2|T2], Queue) ->
    Queue1 = queue_pair(H1, H2, Queue),
    queue_pairs(T1, T2, Queue1).

queue_pair(Free, ValueID, Queue) ->
    mmb_queue:push({Free, ValueID}, Queue).

propagate_value(Queue, ValueMap, Consumers) ->
    case mmb_queue:pop(Queue) of
        none ->
            ValueMap;
        {{Free, ValueID}, Queue1} ->
            case ValueMap of
                #{Free := bad} ->
                 propagate_value(Queue1, ValueMap, Consumers);
                #{Free := ValueID} ->
                    propagate_value(Queue1, ValueMap, Consumers);
                #{Free := _} ->
                    Queue2 = queue_consumers(maps:get(Free, Consumers, []), ValueID, Queue1),
                    propagate_value(Queue2, ValueMap#{Free => bad}, Consumers);
                _ ->
                    Queue2 = queue_consumers(maps:get(Free, Consumers, []), ValueID, Queue1),
                    propagate_value(Queue2, ValueMap#{Free => ValueID}, Consumers)
            end
    end.

queue_consumers([], _, Queue) ->
    Queue;
queue_consumers([H|T], ValueID, Queue) ->
    queue_consumers(T, ValueID, mmb_queue:push({H, ValueID}, Queue)).


collect_fns([], Consumers, ValueMap, _Nodes) ->
    {Consumers, ValueMap};
collect_fns([H|T], Consumers, ValueMap, Nodes) ->
    {Consumers1, ValueMap1} = collect_fn(H, Consumers, ValueMap, Nodes),
    collect_fns(T, Consumers1, ValueMap1, Nodes).


collect_fn({ID, []}, Consumers, ValueMap, _) when is_atom(ID) ->
    {Consumers, ValueMap};
collect_fn({ID, Blocks}, Consumers, ValueMap, Nodes) when is_integer(ID) ->
    collect_blocks(Blocks, Consumers, ValueMap, Nodes).


collect_blocks([], Consumers, ValueMap, _) ->
    {Consumers, ValueMap};
collect_blocks([H|T], Consumers, ValueMap, Nodes) ->
    {Consumers1, ValueMap1} = collect_block(H, Consumers, ValueMap, Nodes),
    collect_blocks(T, Consumers1, ValueMap1, Nodes).

collect_block(ID, Consumers, ValueMap, Nodes) ->
    #{ID := {bb, _, Output, Stmts}} = Nodes,
    {Consumers1, ValueMap1} = collect_stmts(Stmts, Consumers, ValueMap, Nodes),
    collect_output(Output, Consumers1, ValueMap1, Nodes).

collect_stmts([], Consumers, ValueMap, _) ->
    {Consumers, ValueMap};
collect_stmts([H|T], Consumers, ValueMap, Nodes) ->
    {Consumers1, ValueMap1} = collect_stmt(H, Consumers, ValueMap, Nodes),
    collect_stmts(T, Consumers1, ValueMap1, Nodes).

collect_stmt(Stmt, Consumers, ValueMap, Nodes) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    collect_values(List, Consumers, ValueMap, Nodes).

collect_output(none, Consumers, ValueMap, _) ->
    {Consumers, ValueMap};
collect_output({_, List}, Consumers, ValueMap, Nodes) ->
    collect_values(List, Consumers, ValueMap, Nodes);
collect_output({'if', Cond, True, False}, Consumers, ValueMap, Nodes) ->
    {Consumers1, ValueMap1} = collect_value(Cond, Consumers, ValueMap, Nodes),
    {Consumers2, ValueMap2} = collect_output(True, Consumers1, ValueMap1, Nodes),
    collect_output(False, Consumers2, ValueMap2, Nodes).

collect_values([], Consumers, ValueMap, _) ->
    {Consumers, ValueMap};
collect_values([H|T], Consumers, ValueMap, Nodes) ->
    {Consumers1, ValueMap1} = collect_value(H, Consumers, ValueMap, Nodes),
    collect_values(T, Consumers1, ValueMap1, Nodes).

collect_value(ID, Consumers, ValueMap, Nodes) ->
    #{ID := Node} = Nodes,
    case Node of
        {_, _, {op, {cast, up, {fn, FnID}}, [TupleID]}} ->
            #{TupleID := {_, _, {op, {make, tuple}, [_|Args]}}} = Nodes,
            #{FnID := {fn, Free, _, _, _, _}} = Nodes,
            {Consumers1, ValueMap1} = collect_pairs(Free, Args, Consumers, ValueMap, Nodes);
        _ ->
            Consumers1 = Consumers,
            ValueMap1 = ValueMap
    end,

    case Node of
        {const, _, {op, {cast, _, _},  List}} ->
            collect_values(List, Consumers1, ValueMap1, Nodes);
        {const, _, {op, {make, tuple},  List}} ->
            collect_values(List, Consumers1, ValueMap1, Nodes);
        _ ->
            {Consumers1, ValueMap1}
    end.

collect_pairs([], [], Consumers, ValueMap, _Nodes) ->
    {Consumers, ValueMap};
collect_pairs([H1|T1], [H2|T2], Consumers, ValueMap, Nodes) ->
    {Consumers1, ValueMap1} = collect_pair(H1, H2, Consumers, ValueMap, Nodes),
    collect_pairs(T1, T2, Consumers1, ValueMap1, Nodes).

collect_pair(Free, ValueID, Consumers, ValueMap, Nodes) ->
    case Nodes of
        #{ValueID := {var, _, free}} ->
            M = maps:get(ValueID, Consumers, #{}),
            {Consumers#{ValueID => M#{Free => []}}, ValueMap};
        #{ValueID := {const, _, _}} ->
            case ValueMap of
                #{Free := ValueID} ->
                    {Consumers, ValueMap};
                #{Free := bad} ->
                    {Consumers, ValueMap};
                #{Free := _} ->
                    {Consumers, ValueMap#{Free => bad}};
                _ ->
                    {Consumers, ValueMap#{Free => ValueID}}
            end;
        _ ->
            {Consumers, ValueMap#{Free => bad}}
    end.


propagate_bad(Queue, Bad, Consumers) ->
    case mmb_queue:pop(Queue) of
        none ->
            maps:keys(Bad);
        {ID, Queue1} ->
            case Bad of
                #{ID := _} ->
                    propagate_bad(Queue1, Bad, Consumers);
                _ ->
                    Queue2 = push_bad_queue(maps:keys(maps:get(ID, Consumers, #{})), Queue1),
                    propagate_bad(Queue2, Bad#{ID => []}, Consumers)
            end
    end.

push_bad_queue([], Queue) ->
    Queue;
push_bad_queue([H|T], Queue) ->
    push_bad_queue(T, mmb_queue:push(H, Queue)).



convert_fns([], _ValueMap, SSA) ->
    SSA;
convert_fns([H|T], ValueMap, SSA) ->
    SSA1 = convert_fn(H, ValueMap, SSA),
    convert_fns(T, ValueMap, SSA1).


convert_fn({ID, []}, _ValueMap, SSA) when is_atom(ID) ->
    SSA;
convert_fn({ID, Blocks}, ValueMap, SSA) when is_integer(ID) ->
    convert_blocks(Blocks, ValueMap, SSA).


convert_blocks([], _ValueMap, SSA) ->
    SSA;
convert_blocks([H|T], ValueMap, SSA) ->
    SSA1 = convert_block(H, ValueMap, SSA),
    convert_blocks(T, ValueMap, SSA1).

convert_block(ID, ValueMap, SSA = #ssa{nodes = Nodes}) ->
    #{ID := {bb, _, Output, Stmts}} = Nodes,
    SSA1 = convert_stmts(Stmts, ValueMap, SSA),
    convert_output(Output, ValueMap, SSA1).

convert_stmts([], _ValueMap, SSA) ->
    SSA;
convert_stmts([H|T], ValueMap, SSA) ->
    SSA1 = convert_stmt(H, ValueMap, SSA),
    convert_stmts(T, ValueMap, SSA1).

convert_stmt(Stmt, ValueMap, SSA = #ssa{nodes=Nodes}) ->
    List = mmb_ssa:uses(Stmt, Nodes),
    convert_values(List, ValueMap, SSA).

convert_output(none, _ValueMap, SSA) ->
    SSA;
convert_output({_, List}, ValueMap, SSA) ->
    convert_values(List, ValueMap, SSA);
convert_output({'if', Cond, True, False}, ValueMap, SSA) ->
    SSA1 = convert_value(Cond, ValueMap, SSA),
    SSA2 = convert_output(True, ValueMap, SSA1),
    convert_output(False, ValueMap, SSA2).

convert_values([], _ValueMap, SSA) ->
    SSA;
convert_values([H|T], ValueMap, SSA) ->
    SSA1 = convert_value(H, ValueMap, SSA),
    convert_values(T, ValueMap, SSA1).

convert_value(ID, ValueMap, SSA = #ssa{nodes=Nodes}) ->
    #{ID := Node} = Nodes,
    case Node of
        {_, _, {op, {cast, up, {fn, FnID}}, [TupleID]}} ->
            #{TupleID := {Kind, _, {op, {make, tuple}, [Closure|Args]}}} = Nodes,
            #{FnID := {fn, Free, _, _, _, _}} = Nodes,
            case has_any_global(Free, ValueMap) of
                false ->
                    SSA2 = SSA;
                true ->
                    FreeTypes = mmb_ssa:types(Free, Nodes),
                    ArgTypes = mmb_ssa:types(Args, Nodes),
                    case ArgTypes =:= FreeTypes of
                        false ->
                            SSA2 = SSA;
                        true ->
                            Args1 = [Closure|remove_global(Free, Args, ValueMap)],
                            {TupleType, SSA1} = mmb_ssa:typeid({tuple, mmb_ssa:types(Args1, Nodes)}, SSA),
                            SSA2 = mmb_ssa:set_node(TupleID, {Kind, TupleType, {op, {make, tuple}, Args1}}, SSA1)
                    end
            end;
        _ ->
            SSA2 = SSA
    end,

    case Node of
        {const, _, {op, {cast, _, _},  List}} ->
            convert_values(List, ValueMap, SSA2);
        {const, _, {op, {make, tuple},  List}} ->
            convert_values(List, ValueMap, SSA2);
        _ ->
            SSA2
    end.

has_any_global([], _) ->
    false;
has_any_global([H|T], ValueMap) ->
    case ValueMap of
        #{H := _} ->
            true;
        _ ->
            has_any_global(T, ValueMap)
    end.

remove_global([], [], _) ->
    [];
remove_global([H1|T1], [H2|T2], ValueMap) ->
    case ValueMap of
        #{H1 := _} ->
            remove_global(T1, T2, ValueMap);
        _ ->
            [H2|remove_global(T1, T2, ValueMap)]
    end.

convert_frees([], _ValueMap, SSA) ->
    SSA;
convert_frees([H|T], ValueMap, SSA) ->
    SSA1 = convert_free(H, ValueMap, SSA),
    convert_frees(T, ValueMap, SSA1).


convert_free({ID, []}, _ValueMap, SSA) when is_atom(ID) ->
    SSA;
convert_free({ID, Blocks}, ValueMap, SSA = #ssa{nodes=Nodes}) when is_integer(ID) ->
    #{ID := {fn, Free, Params, ReturnType, Entry, Exit}} = Nodes,
    case Free of
        none ->
            SSA;
        _ ->
            case remove_global(Free, ValueMap) of
                {Free, _} ->
                    SSA;
                {Free1, Globals} ->
                    #{Entry := {bb, Input, Output, Stmts}} = Nodes,
                    {Consts, Stmts1, SSA1} = load_globals(Globals, #{}, Stmts, SSA),
                    SSA2 = mmb_ssa:set_node(Entry, {bb, Input, Output, Stmts1}, SSA1),
                    SSA3 = mmb_ssa:set_node(ID, {fn, Free1, Params, ReturnType, Entry, Exit}, SSA2),
                    mmb_ssa:rename_blocks(Blocks, Consts, SSA3)
            end
    end.


remove_global([], _) ->
    {[], []};
remove_global([H1|T1], ValueMap) ->
    case ValueMap of
        #{H1 := Value} ->
            {T2, T3} = remove_global(T1, ValueMap),
            {T2, [{H1, Value}|T3]};
        _ ->
            {T2, T3} = remove_global(T1, ValueMap),
            {[H1|T2], T3}
    end.

load_globals([], Consts, Stmts, SSA) ->
    {Consts, Stmts, SSA};
load_globals([H|T], Consts, Stmts, SSA) ->
    {Consts1, Stmts1, SSA1} = load_global(H, Consts, Stmts, SSA),
    load_globals(T, Consts1, Stmts1, SSA1).

load_global({ID, ValueID}, Consts, Stmts, SSA = #ssa{nodes=Nodes}) ->
    case Nodes of
        #{ValueID := {const, _, _}} ->
            {Consts#{ID => ValueID}, Stmts, SSA};
        _ ->
            #{ID := {var, Type, free}} = Nodes,
            {Consts, [{'let', ID}|Stmts], mmb_ssa:set_node(ID, {var, Type, {op, {load, global, ValueID}, []}}, SSA)}
    end.


convert_root([], _Globals, SSA) ->
    SSA;
convert_root([H|T], Globals, SSA) ->
    SSA1 = convert_root_block(H, Globals, SSA),
    convert_root(T, Globals, SSA1).

convert_root_block(ID, Globals, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Stmts1 = convert_root_stmts(Stmts, Globals),
    {Input1, Stmts2} = convert_input(Input, Stmts1, Globals),
    mmb_ssa:set_node(ID, {bb, Input1, Output, Stmts2}, SSA).

convert_input([], Stmts, _) ->
    {[], Stmts};
convert_input([H|T], Stmts, Globals) ->
    case Globals of
        #{H := _} ->
            {T1, Stmts1} = convert_input(T, Stmts, Globals),
            {[H|T1], [{op, {store, global, H}, [H]}|Stmts1]};
        _ ->
            {T1, Stmts1} = convert_input(T, Stmts, Globals),
            {[H|T1], Stmts1}
    end.


convert_root_stmts([], _) ->
    [];
convert_root_stmts([{'let', ID}=H|T], Globals) ->
    case Globals of
        #{ID := _} ->
            [H, {op, {store, global, ID}, [ID]}|convert_root_stmts(T, Globals)];
        _ ->
            [H|convert_root_stmts(T, Globals)]
    end;
convert_root_stmts([H|T], Globals) ->
    [H|convert_root_stmts(T, Globals)].
