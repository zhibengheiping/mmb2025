%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_elimtag).

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
    #{ID := {bb, _Input, _Output, Stmts}} = Nodes,
    convert_stmts(Stmts, SSA).

convert_stmts([], SSA) ->
    SSA;
convert_stmts([H|T], SSA) ->
    SSA1 = convert_stmt(H, SSA),
    convert_stmts(T, SSA1).

convert_stmt({'let', ID}, SSA = #ssa{nodes=Nodes}) ->
    #{ID := {var, _, Expr}} = Nodes,
    case Expr of
        {op, {cmp, 'Int', '=='}, [X, Y]} ->
            case Nodes of
                #{X := {const, 'Int', X1},
                  Y := {var, 'Int', {op, {load, tag}, [Enum]}}
                 } ->
                    #{Enum := {_, TypeID, _}} = Nodes,
                    #{TypeID := {type, Type}} = Nodes,
                    case Type of
                        {enum, Variants} ->
                            case lookup(X1, Variants) of
                                {_, []} ->
                                    {ConstID, SSA1} = build_enum(TypeID, X, X1, SSA),
                                    mmb_ssa:set_node(ID, {var, 'Bool', {op, is_same_ptr, [Enum, ConstID]}}, SSA1);
                                _ ->
                                    SSA
                            end;
                        _ ->
                            SSA
                    end;
                _ ->
                    SSA
            end;
        _ ->
            SSA
    end;
convert_stmt(_, SSA) ->
    SSA.

lookup(0, [H|_]) ->
    H;
lookup(N, [_|T]) ->
    lookup(N-1, T).

build_enum(Type, Value, Tag, SSA) ->
    {Tuple, SSA1} = build_tuple(Value, SSA),
    build_const(Type, {op, {cast, up, Tag}, [Tuple]}, SSA1).

build_tuple(Value, SSA) ->
    {Type, SSA1} = build_type({tuple, ['Int']}, SSA),
    build_const(Type, {op, {make, tuple}, [Value]}, SSA1).

build_const(Type, Value, SSA = #ssa{values=Values}) ->
    Const = {const, Type, Value},
    case Values of
        #{Const := ID} ->
            {ID, SSA};
        _ ->
            {ID, SSA1} = mmb_ssa:add_node(Const, SSA),
            Values1 = Values#{Const => ID},
            {ID, SSA1#ssa{values=Values1}}
    end.

build_type(Type, SSA = #ssa{types = Types}) ->
    case Types of
        #{Type := ID} ->
            {ID, SSA};
        _ ->
            {ID, SSA1} = mmb_ssa:add_node({type, Type}, SSA),
            Types1 = Types#{Type => ID},
            {ID, SSA1#ssa{types=Types1}}
    end.
