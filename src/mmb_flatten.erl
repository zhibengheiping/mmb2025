%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_flatten).

-export([flatten/3]).

-record(
   s,
   {count,
    values,
    exit=none,
    blocks=[],
    free=#{},
    fns=#{}}).

flatten(Count, Fns, Values) ->
    [{fn, Root, _, _, _, _, _}|_] = Fns,
    #s{fns=Fns1} = fns(Fns, #s{count = Count, values = Values}),
    {Root, Fns1}.

fns([], State) ->
    State;
fns([H|T], State) ->
    {ID, Fn, State1 = #s{fns=Fns}} = fn(H, State),
    fns(T, State1#s{fns = Fns#{ID=>Fn}}).

fn({fn, ID, Free, Gen, Params, Return, Body}, State) ->
    {Exit, State1} = new_id(State),
    ExitBlock = {Exit, [Return], none, [{return, Return}]},
    FreeMap =
        case Free of
            none ->
                #{};
            _ ->
                maps:from_list([{V, []} || V <- Free])
        end,
    {Acc, Output, State2 = #s{blocks = Blocks}} = block(Body, Exit, State1#s{blocks=[ExitBlock], exit=Exit, free=FreeMap}),
    Entry = {ID, [], Output, Acc},
    Fn = {fn, Free, Gen, Params, Return, [Entry|Blocks]},
    {ID, Fn, State2}.

block({block, Stmts, Expr}, Exit, State) ->
    {Acc, Output, State1} = value(Expr, [], {Exit, [Expr]}, State),
    values(Stmts, Acc, Output, State1).

values([], Acc, Output, State) ->
    {Acc, Output, State};
values([H|T], Acc, Output, State) ->
    {Acc1, Output1, State1} = values(T, Acc, Output, State),
    value(H, Acc1, Output1, State1).

value(ID, Acc, Output, State = #s{values = Values, free=Free}) ->
    case Free of
        #{ID := _} ->
            {Acc, Output, State};
        _ ->
            #{ID := Value} = Values,
            value(ID, Value, Acc, Output, State)
    end.

stmt(ID, Acc, Output, State) ->
    {[{'let', ID, {literal, '()'}}|Acc], Output, State}.

value(ID, {return, Expr}, Acc, Output, State) ->
    {Acc1, Output1, State1} = stmt(ID, Acc, Output, State),
    {BlockID, State2 = #s{exit=Exit, blocks=Blocks}} = new_id(State1),
    Blocks1 = [{BlockID, [], Output1, Acc1}|Blocks],
    value(Expr, [], {Exit, [Expr]}, State2#s{blocks=Blocks1});
value(ID, {'let', Expr}, Acc, Output, State) ->
    {Acc1, Output1, State1} = stmt(ID, Acc, Output, State),
    value(Expr, Acc1, Output1, State1);
value(ID, {assign, Var, Value}, Acc, Output, State) ->
    {Acc1, Output1, State1} = stmt(ID, Acc, Output, State),
    value(Value, [{op, {store, ref}, [Value, Var]}|Acc1], Output1, State1);
value(ID, {assign, Array, Index, Value}, Acc, Output, State) ->
    {Acc1, Output1, State1} = stmt(ID, Acc, Output, State),
    values([Array, Index, Value], [{op, {store, array}, [Value, Array, Index]}|Acc1], Output1, State1);
value(ID, {destruct, N, Names, Value}, Acc, Output, State) ->
    {Acc1, Output1, State1} = stmt(ID, Acc, Output, State),
    value(Value, [{destruct, N, Names, Value}|Acc1], Output1, State1);
value(ID, {while, Cond, Body}, Acc, Output, State) ->
    {Acc1, Output1, State1} = stmt(ID, Acc, Output, State),
    {CondID, State2} = new_id(State1),
    {BodyID, State3} = new_id(State2),
    {ExitID, State4 = #s{blocks = Blocks}} = new_id(State3),
    Blocks1 = [{ExitID, [], Output1, Acc1}|Blocks],

    {Acc2, Output2, State5 = #s{blocks = Blocks2}} =
        values(Body, [], {CondID, []}, State4#s{blocks = Blocks1}),
    Blocks3 = [{BodyID, [], Output2, Acc2}|Blocks2],

    {Acc3, Output3, State6 = #s{blocks = Blocks4}} =
        value(Cond, [], {'if', Cond, {BodyID, []}, {ExitID, []}},
              State5#s{blocks = Blocks3}),
    Blocks5 = [{CondID, [], Output3, Acc3}|Blocks4],
    {[], {CondID, []}, State6#s{blocks = Blocks5}};

value(ID, {do_while, Cond, Body}, Acc, Output, State) ->
    {Acc1, Output1, State1} = stmt(ID, Acc, Output, State),
    {CondID, State2} = new_id(State1),
    {BodyID, State3} = new_id(State2),
    {ExitID, State4 = #s{blocks = Blocks}} = new_id(State3),
    Blocks1 = [{ExitID, [], Output1, Acc1}|Blocks],

    {Acc2, Output2, State5 = #s{blocks = Blocks2}} =
        value(Cond, [], {'if', Cond, {BodyID, []}, {ExitID, []}},
              State4#s{blocks = Blocks1}),
    Blocks3 = [{CondID, [], Output2, Acc2}|Blocks2],

    {Acc3, Output3, State6 = #s{blocks = Blocks4}} =
        values(Body, [], {CondID, []}, State5#s{blocks = Blocks3}),
    Blocks5 = [{BodyID, [], Output3, Acc3}|Blocks4],
    {[], {BodyID, []}, State6#s{blocks = Blocks5}};

value(ID, {literal, _}=Value, Acc, Output, State) ->
    {[{'let', ID, Value}|Acc], Output, State};
value(ID, {var, Value}, Acc, Output, State) ->
    {[{'let', ID, {move, Value}}|Acc], Output, State};
value(ID, {alias, Value}, Acc, Output, State) ->
    value(Value, [{'let', ID, {move, Value}}|Acc], Output, State);
value(ID, {op, Op, List}, Acc, Output, State) ->
    values(List, [{'let', ID, {op, Op, List}}|Acc], Output, State);
value(ID, {closure, Fun, Free}, Acc, Output, State) ->
    value(Fun, [{'let', ID, {closure, Fun, Free}}|Acc], Output, State);
value(ID, {attr, Name, Expr}, Acc, Output, State) ->
    value(Expr, [{'let', ID, {attr, Name, Expr}}|Acc], Output, State);
value(ID, {call, Fun, Args}, Acc, Output, State) ->
    values([Fun|Args], [{'let', ID, {call, Fun, Args}}|Acc], Output, State);
value(ID, {block, Stmts, Expr}, Acc, Output, State) ->
    {Acc1, Output1, State1} = value(Expr, [{'let', ID, {move, Expr}}|Acc], Output, State),
    values(Stmts, Acc1, Output1, State1);
value(ID, {'if', Cond, True, False}, Acc, Output, State) ->
    {TrueID, State1} = new_id(State),
    {FalseID, State2} = new_id(State1),
    {ExitID, State3 = #s{blocks = Blocks}} = new_id(State2),
    Blocks1 = [{ExitID, [ID], Output, Acc}|Blocks],

    {Acc1, Output1, State4 = #s{blocks = Blocks2}} =
        value(False, [], {ExitID, [False]}, State3#s{blocks = Blocks1}),
    Blocks3 = [{FalseID, [], Output1, Acc1}|Blocks2],

    {Acc2, Output2, State5 = #s{blocks = Blocks4}} =
        value(True, [], {ExitID, [True]}, State4#s{blocks = Blocks3}),
    Blocks5 = [{TrueID, [], Output2, Acc2}|Blocks4],

    value(Cond, [],
          {'if', Cond, {TrueID, []}, {FalseID, []}},
          State5#s{blocks = Blocks5});
value(ID, {match, Expr, Arms}, Acc, Output, State) ->
    {ExitID, State1} = new_id(State),
    {FailID, State2 = #s{blocks = Blocks}} = new_id(State1),
    Blocks1 = [{FailID, [], none, [fail]},
               {ExitID, [ID], Output, Acc}|Blocks],
    {EntryID, State3} = arms(Arms, FailID, ExitID, State2#s{blocks = Blocks1}),

    value(Expr, [], {EntryID, []}, State3).


new_id(State = #s{count = Count}) ->
    {Count, State#s{count = Count + 1}}.


arms([], FailID, _ExitID, State) ->
    {FailID, State};
arms([H|T], FailID, ExitID, State) ->
    {FailID1, State1} = arms(T, FailID, ExitID, State),
    arm(H, FailID1, ExitID, State1).

arm({Patterns, Expr}, FailID, ExitID, State) ->
    {ArmID, State1} = new_id(State),

    {Acc, Output, State2 = #s{blocks = Blocks}} =
        value(Expr, [], {ExitID, [Expr]}, State1),

    Blocks1 = [{ArmID, [], Output, Acc}|Blocks],

    {Acc1, Output1, State3} = patterns(Patterns, [], {ArmID, []}, FailID, State2#s{blocks = Blocks1}),
    {EntryID, State4 = #s{blocks = Blocks2}} = new_id(State3),
    Blocks3 = [{EntryID, [], Output1, Acc1}|Blocks2],
    {EntryID, State4#s{blocks = Blocks3}}.


pattern({'if', Cond}, Acc, Output, FailID, State) ->
    {SuccessID, State1 = #s{blocks = Blocks}} = new_id(State),
    Blocks1 = [{SuccessID, [], Output, Acc}|Blocks],
    value(Cond, [],
          {'if', Cond, {SuccessID, []}, {FailID, []}},
          State1#s{blocks = Blocks1});
pattern({destruct, N, Vars, Value}, Acc, Output, _, State) ->
    value(Value, [{destruct, N, Vars, Value}|Acc], Output, State).

patterns([], Acc, Output, _FailID, State) ->
    {Acc, Output, State};
patterns([H|T], Acc, Output, FailID, State) ->
    {Acc1, Output1, State1} = patterns(T, Acc, Output, FailID, State),
    pattern(H, Acc1, Output1, FailID, State1).
