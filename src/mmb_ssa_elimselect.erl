%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimselect).

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
convert_fn({ID, Blocks}, SSA) when is_integer(ID) ->
    convert_blocks(Blocks, SSA).


convert_blocks([], SSA) ->
    SSA;
convert_blocks([H|T], SSA) ->
    SSA1 = convert_block(H, SSA),
    convert_blocks(T, SSA1).

convert_block(ID, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {bb, _, _, Stmts}} = Nodes,
    convert_stmts(Stmts, SSA).

convert_stmts([], SSA) ->
    SSA;
convert_stmts([H|T], SSA) ->
    SSA1 = convert_stmt(H, SSA),
    convert_stmts(T, SSA1).

convert_stmt({'let', ID}, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, Type, Expr}} = Nodes,
    case Expr of
        {op, select, [Cond, X, Y]} ->
            case Nodes of
                #{Y := {var, 'Double', _},
                  X := {var, 'Double', {op, {arith, 'Double', neg}, [Y]}},
                  Cond := {var, 'Bool', {op, {cmp, 'Double', '<'}, [Y, Zero]}}} ->
                    case Nodes of
                        #{Zero := {const, 'Double', 0.0}} ->
                            {Abs, SSA1} = create_fabs(SSA),
                            mmb_ssa:set_node(ID, {var, Type, {call, Abs, [Y]}}, SSA1);
                        _ ->
                            SSA
                    end;
                #{Y := {_, 'Double', _},
                  X := {_, 'Double', _},
                  Cond := {var, 'Bool', {op, {cmp, 'Double', '>'}, [X, Y]}}} ->
                    {Max, SSA1} = create_max(SSA),
                    mmb_ssa:set_node(ID, {var, Type, {call, Max, [X, Y]}}, SSA1);
                #{Y := {_, 'Double', _},
                  X := {_, 'Double', _},
                  Cond := {var, 'Bool', {op, {cmp, 'Double', '>='}, [X, Y]}}} ->
                    {Max, SSA1} = create_max(SSA),
                    mmb_ssa:set_node(ID, {var, Type, {call, Max, [X, Y]}}, SSA1);
                _ ->
                    SSA
            end;
        _ ->
            SSA
    end;
convert_stmt(_, SSA) ->
    SSA.

create_fabs(SSA) ->
    {Type, SSA1} = create_type({fn, ['Double'], 'Double'}, SSA),
    create_value({const, Type, {fn, abs_float}}, SSA1).

create_max(SSA) ->
    {Type, SSA1} = create_type({fn, ['Double', 'Double'], 'Double'}, SSA),
    create_value({const, Type, {fn, max_float}}, SSA1).

create_type(Type, SSA = #ssa{types=Types}) ->
    case Types of
        #{Type := ID} ->
            {ID, SSA};
        _ ->
            {ID, SSA1} = mmb_ssa:add_node({type, Type}, SSA),
            {ID, SSA1#ssa{types = Types#{Type => ID}}}
    end.


create_value(Value, SSA = #ssa{values=Values}) ->
    case Values of
        #{Value := ID} ->
            {ID, SSA};
        _ ->
            {ID, SSA1} = mmb_ssa:add_node(Value, SSA),
            {ID, SSA1#ssa{values = Values#{Value => ID}}}
    end.
