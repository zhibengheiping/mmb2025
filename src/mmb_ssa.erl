%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa).

-export([collect_fns/1, collect_blocks/2, collect_phi/2, collect_src/2, uses/2, types/2, typeid/2, set_node/3, add_node/2, rename_blocks/3, rename_stmts/3, rename_output/2, rename_stmt/3, copy_fn/2]).

-include("mmb_ssa.hrl").

collect_fns(#ssa{root=Root, nodes=Nodes}) ->
    Queue = mmb_queue:init(),
    Queue1 = mmb_queue:push(Root, Queue),
    collect_fns(Queue1, #{}, Nodes).

collect_fns([], Done, _Nodes) ->
    Done;
collect_fns(Queue, Done, Nodes) ->
    case mmb_queue:pop(Queue) of
        none ->
            Done;
        {ID, Queue1} ->
            case Done of
                #{ID := _} ->
                    collect_fns(Queue1, Done, Nodes);
                _ when is_integer(ID) ->
                    Blocks = collect_blocks(ID, Nodes),
                    Queue2 = collect_fn(Blocks, Queue1, Nodes),
                    collect_fns(Queue2, Done#{ID => Blocks}, Nodes);
                _ ->
                    collect_fns(Queue1, Done#{ID => []}, Nodes)
            end
    end.


collect_blocks(ID, Nodes) ->
    #{ID := {fn, _, _, _, Entry, _}} = Nodes,
    collect_blocks([Entry], #{}, Nodes).

collect_blocks([], _, _) ->
    [];
collect_blocks([H|T], Done, Nodes) when is_map_key(H, Done) ->
    collect_blocks(T, Done, Nodes);
collect_blocks([H|T], Done, Nodes) ->
    #{H := {bb, _, Output, _}} = Nodes,
    T1 =
        case Output of
            none ->
                T;
            {Exit, _} ->
                [Exit|T];
            {'if', _, {True, _}, {False, _}} ->
                [True, False|T]
        end,
    [H|collect_blocks(T1, Done#{H => []}, Nodes)].


collect_fn([], Queue, _) ->
    Queue;
collect_fn([H|T], Queue, Nodes) ->
    #{H := {bb, _, Output, Stmts}} = Nodes,
    Queue1 = queue_stmts_uses(Stmts, Queue, Nodes),
    Queue2 = queue_output_uses(Output, Queue1, Nodes),
    collect_fn(T, Queue2, Nodes).

queue_output_uses(none, Queue, _) ->
    Queue;
queue_output_uses({_, Values}, Queue, Nodes) ->
    queue_values_uses(Values, Queue, Nodes);
queue_output_uses({'if', Cond, True, False}, Queue, Nodes) ->
    Queue1 = queue_value_uses(Cond, Queue, Nodes),
    Queue2 = queue_output_uses(True, Queue1, Nodes),
    queue_output_uses(False, Queue2, Nodes).


queue_values_uses([], Queue, _Nodes) ->
    Queue;
queue_values_uses([H|T], Queue, Nodes) ->
    Queue1 = queue_value_uses(H, Queue, Nodes),
    queue_values_uses(T, Queue1, Nodes).

queue_value_uses(ID, Queue, Nodes) ->
    case Nodes of
        #{ID := {const, _, {fn, Fn}}} ->
            mmb_queue:push(Fn, Queue);
        #{ID := {const, _, {op, {cast, _, _}, [X]}}} ->
            queue_value_uses(X, Queue, Nodes);
        #{ID := {const, _, {op, {make, tuple}, List}}} ->
            queue_values_uses(List, Queue, Nodes);
        _ ->
            Queue
    end.


queue_stmts_uses([], Queue, _Nodes) ->
    Queue;
queue_stmts_uses([H|T], Queue, Nodes) ->
    Queue1 = queue_stmt_uses(H, Queue, Nodes),
    queue_stmts_uses(T, Queue1, Nodes).

queue_stmt_uses(Stmt, Queue, Nodes) ->
    queue_values_uses(uses(Stmt, Nodes), Queue, Nodes).

uses({'let', ID}, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    uses(Expr, Nodes);
uses({op, _, List}, _) ->
    List;
uses({call, Fun, Args}, _) ->
    [Fun|Args];
uses(fail, _) ->
    [];
uses(return, _) ->
    [];
uses({return, Expr}, _) ->
    [Expr].


collect_phi(Blocks, Nodes) ->
    collect_phi(Blocks, #{}, Nodes).

collect_phi([], PhiMap, _) ->
    PhiMap;
collect_phi([H|T], PhiMap, Nodes) ->
    #{H := {bb, _, Output, _}} = Nodes,
    PhiMap1 = collect_output_phi(H, Output, PhiMap),
    collect_phi(T, PhiMap1, Nodes).

collect_output_phi(_, none, PhiMap) ->
    PhiMap;
collect_output_phi(BlockID, {ExitID, Values}, PhiMap) ->
    case PhiMap of
        #{ExitID := List} ->
            ok;
        _ ->
            List = []
    end,
    PhiMap#{ExitID => [{BlockID, Values}|List]};
collect_output_phi(BlockID, {'if', _, True, False}, PhiMap) ->
    PhiMap1 = collect_output_phi(BlockID, True, PhiMap),
    collect_output_phi(BlockID, False, PhiMap1).

collect_src(Blocks, Nodes) ->
    collect_src(Blocks, #{}, Nodes).

collect_src([], SrcMap, _Nodes) ->
    SrcMap;
collect_src([H|T], SrcMap, Nodes) ->
    #{H := {bb, _, Output, _}} = Nodes,
    SrcMap1 = collect_output_src(H, Output, SrcMap),
    collect_src(T, SrcMap1, Nodes).

collect_output_src(_, none, SrcMap) ->
    SrcMap;
collect_output_src(ID, {ExitID, _}, SrcMap) ->
    List = maps:get(ExitID, SrcMap, []),
    SrcMap#{ExitID => [ID|List]};
collect_output_src(ID, {'if', _, True, False}, SrcMap) ->
    SrcMap1 = collect_output_src(ID, True, SrcMap),
    collect_output_src(ID, False, SrcMap1).


types([], _) ->
    [];
types([H|T], Nodes) ->
    [type(H, Nodes)|types(T, Nodes)].

type(ID, Nodes) ->
    #{ID := Node} = Nodes,
    case Node of
        {var, Type, _} ->
            Type;
        {const, Type, _} ->
            Type
    end.

typeid(Type, SSA = #ssa{types=Types}) ->
    case Types of
        #{Type := ID} ->
            {ID, SSA};
        _ ->
            {ID, SSA1} = add_node({type, Type}, SSA),
            Types1 = Types#{Type => ID},
            {ID, SSA1#ssa{types=Types1}}
    end.

set_node(ID, Node, SSA = #ssa{nodes=Nodes}) ->
    Nodes1 = Nodes#{ID => Node},
    SSA#ssa{nodes=Nodes1}.

add_node(Node, SSA = #ssa{count=Count}) ->
    {Count, set_node(Count, Node, SSA#ssa{count=Count+1})}.

rename_blocks([], _Map, SSA) ->
    SSA;
rename_blocks([H|T], Map, SSA) ->
    rename_blocks(T, Map, rename_block(H, Map, SSA)).

rename_block(ID, Map, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    {Stmts1, SSA1} = rename_stmts(Stmts, Map, SSA),
    Output1 = rename_output(Output, Map),
    set_node(ID, {bb, Input, Output1, Stmts1}, SSA1).

rename_output(none, _) ->
    none;
rename_output({ExitID, Values}, Map) ->
    {ExitID, rename_values(Values, Map)};
rename_output({'if', Cond, True, False}, Map) ->
    {'if',
     rename_value(Cond, Map),
     rename_output(True, Map),
     rename_output(False, Map)}.

rename_stmts([], _Map, SSA) ->
    {[], SSA};
rename_stmts([H|T], Map, SSA) ->
    {H1, SSA1} = rename_stmt(H, Map, SSA),
    {T1, SSA2} = rename_stmts(T, Map, SSA1),
    {[H1|T1], SSA2}.

rename_stmt({'let', ID}=Stmt, Map, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, Expr}} = Nodes,
    {Expr1, SSA1} = rename_stmt(Expr, Map, SSA),
    {Stmt, set_node(ID, {var, Type, Expr1}, SSA1)};
rename_stmt({op, Op, List}, Map, SSA) ->
    List1 = rename_values(List, Map),
    {{op, Op, List1}, SSA};
rename_stmt({call, Fun, Args}, Map, SSA) ->
    [Fun1|Args1] = rename_values([Fun|Args], Map),
    {{call, Fun1, Args1}, SSA};
rename_stmt(fail, _,  SSA) ->
    {fail, SSA};
rename_stmt(return, _, SSA) ->
    {return, SSA};
rename_stmt({return, Expr}, Map, SSA) ->
    Expr1 = rename_value(Expr, Map),
    {{return, Expr1}, SSA}.

rename_values([], _) ->
    [];
rename_values([H|T], Map) ->
    [rename_value(H, Map)|rename_values(T, Map)].

rename_value(X, Map) ->
    case Map of
        #{X := Y} ->
            rename_value(Y, Map);
        _ ->
            X
    end.


copy_fn(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {fn, Free, Params, ReturnType, Entry, Exit}} = Nodes,
    Blocks = mmb_ssa:collect_blocks(ID, Nodes),
    case Free of
        none ->
            Free1 = none,
            Rename = #{},
            SSA2 = SSA;
        _ ->
            {Free1, Rename, SSA1} = rename_ids(Free, #{}, SSA),
            SSA2 = copy_vars(Free, Free1, SSA1)
        end,
    {Params1, Rename1, SSA3} = rename_ids(Params, Rename, SSA2),
    SSA4 = copy_vars(Params, Params1, SSA3),
    {Rename2, SSA5} = copy_blocks(Blocks, Rename1, SSA4),
    {{fn, Free1, Params1, ReturnType, maps:get(Entry, Rename2), maps:get(Exit, Rename2)}, SSA5}.

copy_vars([], [], SSA) ->
    SSA;
copy_vars([H1|T1], [H2|T2], SSA = #ssa{nodes=Nodes}) ->
    #{H1 := {var, Type, Expr}} = Nodes,
    true = is_atom(Expr),
    copy_vars(T1, T2, mmb_ssa:set_node(H2, {var, Type, Expr}, SSA)).

copy_blocks([], Rename, SSA) ->
    {Rename, SSA};
copy_blocks([H|T], Rename, SSA) ->
    {Rename1, SSA1} = copy_block(H, Rename, SSA),
    copy_blocks(T, Rename1, SSA1).

copy_block(ID, Rename, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    {[ID1|Input1], Rename1, SSA1} = rename_ids([ID|Input], Rename, SSA),
    SSA2 = copy_vars(Input, Input1, SSA1),
    {Stmts1, Rename2, SSA3} = copy_stmts(Stmts, Rename1, SSA2),
    {Output1, Rename3, SSA4} = copy_output(Output, Rename2, SSA3),
    {Rename3, set_node(ID1, {bb, Input1, Output1, Stmts1}, SSA4)}.

copy_stmts([], Rename, SSA) ->
    {[], Rename, SSA};
copy_stmts([H|T], Rename, SSA) ->
    {H1, Rename1, SSA1} = copy_stmt(H, Rename, SSA),
    {T1, Rename2, SSA2} = copy_stmts(T, Rename1, SSA1),
    {[H1|T1], Rename2, SSA2}.

copy_stmt({'let', ID}, Rename, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, Expr}} = Nodes,
    {ID1, Rename1, SSA1} = rename_id(ID, Rename, SSA),
    {Expr1, Rename2, SSA2} = copy_stmt(Expr, Rename1, SSA1),
    {{'let', ID1}, Rename2, set_node(ID1, {var, Type, Expr1}, SSA2)};
copy_stmt(fail, Rename, SSA) ->
    {fail, Rename, SSA};
copy_stmt(return, Rename, SSA) ->
    {return, Rename, SSA};
copy_stmt({return, Expr}, Rename, SSA) ->
    {Expr1, Rename1, SSA1} = rename_id(Expr, Rename, SSA),
    {{return, Expr1}, Rename1, SSA1};
copy_stmt({op, Op, List}, Rename, SSA) ->
    {List1, Rename1, SSA1} = rename_ids(List, Rename, SSA),
    {{op, Op, List1}, Rename1, SSA1};
copy_stmt({call, Fun, Args}, Rename, SSA) ->
    {[Fun1|Args1], Rename1, SSA1} = rename_ids([Fun|Args], Rename, SSA),
    {{call, Fun1, Args1}, Rename1, SSA1}.

copy_output(none, Rename, SSA) ->
    {none, Rename, SSA};
copy_output({ExitID, Values}, Rename, SSA) ->
    {[ExitID1|Values1], Rename1, SSA1} = rename_ids([ExitID|Values], Rename, SSA),
    {{ExitID1, Values1}, Rename1, SSA1};
copy_output({'if', Cond, True, False}, Rename, SSA) ->
    {Cond1, Rename1, SSA1} = rename_id(Cond, Rename, SSA),
    {True1, Rename2, SSA2} = copy_output(True, Rename1, SSA1),
    {False1, Rename3, SSA3} = copy_output(False, Rename2, SSA2),
    {{'if', Cond1, True1, False1}, Rename3, SSA3}.

rename_ids([], Rename, SSA) ->
    {[], Rename, SSA};
rename_ids([H|T], Rename, SSA) ->
    {H1, Rename1, SSA1} = rename_id(H, Rename, SSA),
    {T1, Rename2, SSA2} = rename_ids(T, Rename1, SSA1),
    {[H1|T1], Rename2, SSA2}.

rename_id(H, Rename, SSA = #ssa{nodes=Nodes}) ->
    case Rename of
        #{H := H1} ->
            {H1, Rename, SSA};
        _ ->
            case Nodes of
                #{H := {const, _, _}} ->
                    {H, Rename#{H => H}, SSA};
                _ ->
                    {H1, SSA1} = new_id(SSA),
                    {H1, Rename#{H => H1}, SSA1}
            end
    end.


new_id(SSA = #ssa{count=Count}) ->
    {Count, SSA#ssa{count=Count+1}}.
