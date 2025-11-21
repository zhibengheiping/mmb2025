%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_llvm_compute).

-export([init/0, resolve_vars/3, get_value_id/2, set_var/3, get_var/2, add_value/2, bind_value/3, eval/4, is_const/2, is_var/2, is_eval/2, uses/2, phi_back/3, get_type/2, get_value/2, is_pure/2]).

-include("mmb_ssa.hrl").

-record(ctx, {var2id=#{}, value2id=#{}, id2value=#{}}).

init() ->
    #ctx{}.

set_var(Var, ValueID, Context = #ctx{var2id=Vars}) ->
    Vars1 = Vars#{Var => ValueID},
    Context#ctx{var2id=Vars1}.

get_var(Var, #ctx{var2id=Vars}) ->
    #{Var := ValueID} = Vars,
    ValueID.


get_value_id(Value, #ctx{value2id=Value2ID}) ->
    #{Value := ID} = Value2ID,
    ID.

bind_value(Value, ID, Context = #ctx{value2id=Value2ID}) ->
    Value2ID1 = Value2ID#{Value => ID},
    Context#ctx{value2id=Value2ID1}.

add_value(Value, Context = #ctx{value2id=Value2ID, id2value=ID2Value}) ->
    case Value2ID of
        #{Value := ValueID} ->
            Value2ID1 = Value2ID,
            ID2Value1 = ID2Value;
        _ ->
            ValueID = maps:size(ID2Value),
            Value2ID1 = Value2ID#{Value => ValueID},
            ID2Value1 = ID2Value#{ValueID => Value}
    end,
    {ValueID, Context#ctx{value2id=Value2ID1, id2value=ID2Value1}}.

eval(Type, {op, Op, List}, Nodes, Context) ->
    {List1, Context1} = resolve_vars(List, Nodes, Context),
    eval_op(Op, Type, List1, Context1);
eval(_Type, {call, _Fun, _Args}, _Nodes, _Context) ->
    none.

eval_op({gep, _}=Op, Type, [Ptr|List], Context) ->
    case remove_tail_zero(List, Context) of
        [] ->
            {Ptr, Context};
        List1 ->
            add_value({eval, Type, {op, Op, [Ptr|List1]}}, Context)
    end;
eval_op(shl=Op, Type, [X, Y] = List, Context) ->
    case is_all_const(List, Context) of
        true ->
            X1 = get_const_value(X, Context),
            Y1 = get_const_value(Y, Context),
            add_value({const, Type, X1 bsl Y1}, Context);
        false ->
            add_value({eval, Type, {op, Op, List}}, Context)
    end;
eval_op(_, _, _, _) ->
    none.

remove_tail_zero([], _Context) ->
    [];
remove_tail_zero([H|T], Context) ->
    case remove_tail_zero(T, Context) of
        [] ->
            case is_const(H, Context) andalso get_const_value(H, Context) =:= 0 of
                true ->
                    [];
                false ->
                    [H]
            end;
        T1 ->
            [H|T1]
    end.


get_const_value(ID, #ctx{id2value=Values}) ->
    #{ID := {const, _, Value}} = Values,
    Value.

is_all_const([], _) ->
    true;
is_all_const([H|T], Context) ->
    is_const(H, Context) andalso is_all_const(T, Context).

is_const(ID, #ctx{id2value=Values}) ->
    case Values of
        #{ID := {const, _, _}} ->
            true;
        _ ->
            false
    end.

is_var(ID, #ctx{id2value=Values}) ->
    case Values of
        #{ID := {var, _, _}} ->
            true;
        _ ->
            false
    end.

is_eval(ID, #ctx{id2value=Values}) ->
    case Values of
        #{ID := {eval, _, _}} ->
            true;
        _ ->
            false
    end.

resolve_vars([], _, Context) ->
    {[], Context};
resolve_vars([H|T], Nodes, Context = #ctx{var2id=Vars}) ->
    case Vars of
        #{H := H1} ->
            Context2 = Context;
        _ ->
            #{H := {const, Type, Value}} = Nodes,
            {H1, Context2} =
                case Value of
                    {op, Op, List} ->
                        {List1, Context1} = resolve_vars(List, Nodes, Context),
                        add_value({const, Type, {op, Op, List1}}, Context1);
                    _ ->
                        add_value({const, Type, Value}, Context)
                end
    end,
    {T1, Context3} = resolve_vars(T, Nodes, Context2),
    {[H1|T1], Context3}.


uses(ValueID, #ctx{id2value=Values}) ->
    #{ValueID := Value} = Values,
    case Value of
        {const, _, _} ->
            [];
        {eval, _, {op, _, List}} ->
            List;
        {eval, _, {call, Fun, Args}} ->
            [Fun|Args];
        {var, _, _} ->
            []
    end.

phi_back(ValueID, Phi, Context = #ctx{id2value=Values}) ->
    #{ValueID := {eval, Type, Expr}} = Values,
    Expr1 = phi_back_expr(Expr, Phi),
    case add_value({eval, Type, Expr1}, Context) of
        {ValueID, Context1} ->
            {ValueID, Phi, Context1};
        {ValueID1, Context1} ->
            {ValueID1, Phi#{ValueID => ValueID1}, Context1}
    end.

phi_back_expr({op, Op, List}, Phi) ->
    List1 = phi_back_list(List, Phi),
    {op, Op, List1};
phi_back_expr({call, Fun, Args}, Phi) ->
    [Fun1|Args1] = phi_back_list([Fun|Args], Phi),
    {call, Fun1, Args1}.

phi_back_list(List, Phi) ->
    [maps:get(ID, Phi, ID) || ID <- List].


get_type(ValueID, #ctx{id2value=Values}) ->
    #{ValueID := {_, Type, _}} = Values,
    Type.

get_value(ValueID, #ctx{id2value=Values}) ->
    #{ValueID := Value} = Values,
    Value.


is_pure({call, _, _}, _Nodes) ->
    false;
is_pure({op, {gep, _}, _}, _Nodes) ->
    true;
is_pure({op, shl, _}, _Nodes) ->
    true;
is_pure({op, _, _}, _Nodes) ->
    false.
