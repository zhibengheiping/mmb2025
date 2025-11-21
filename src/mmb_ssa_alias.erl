%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_ssa_alias).

-export([analysis/3]).

-include("mmb_ssa.hrl").

analysis(ID, Blocks, Nodes) ->
    #{ID := {fn, Free, Params, _ReturnType, _Entry, _Exit}} = Nodes,
    Alias = mmb_alias:init(),
    Args =
        case Free of
            none ->
                Params;
            _ ->
                append(Free, Params)
        end,
    Alias1 = add_vars(Args, Alias, Nodes),
    Alias2 = mmb_alias:new_call(Args, Alias1),

    Alias3 = blocks(Blocks, Alias2, Nodes),
    PhiMap = mmb_ssa:collect_phi(Blocks, Nodes),
    block_phis(Blocks, PhiMap, Alias3, Nodes).

block_phis([], _, Alias, _) ->
    Alias;
block_phis([H|T], PhiMap, Alias, Nodes) ->
    block_phis(T, PhiMap, block_phi(H, PhiMap, Alias, Nodes), Nodes).

block_phi(ID, PhiMap, Alias, Nodes) ->
    #{ID := {bb, Input, _, _}} = Nodes,
    case Input of
        [] ->
            Alias;
        _ ->
            #{ID := Phi} = PhiMap,
            phi_list(Phi, Input, Alias, Nodes)
    end.

phi_list([], _, Alias, _) ->
    Alias;
phi_list([{_, Values}|T], Input, Alias, Nodes) ->
    Alias1 = phis(Values, Input, Alias, Nodes),
    phi_list(T, Input, Alias1, Nodes).

phis([], [], Alias, _) ->
    Alias;
phis([H1|T1], [H2|T2], Alias, Nodes) ->
    Alias1 = phi(H1, H2, Alias, Nodes),
    phis(T1, T2, Alias1, Nodes).

phi(Var, Phi, Alias, Nodes) ->
    case is_const(Var, Nodes) of
        true ->
            Alias;
        false ->
            mmb_alias:alias(Var, Phi, Alias)
    end.


add_vars([], Alias, _) ->
    Alias;
add_vars([H|T], Alias, Nodes) ->
    Alias1 = mmb_alias:add_var(H, Alias, Nodes),
    add_vars(T, Alias1, Nodes).

append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].


blocks([], Alias, _) ->
    Alias;
blocks([H|T], Alias, Nodes) ->
    blocks(T, block(H, Alias, Nodes), Nodes).

block(ID, Alias, Nodes) ->
    #{ID := {bb, Input, _Output, Stmts}} = Nodes,
    Alias1 = add_vars(Input, Alias, Nodes),
    stmts(Stmts, Alias1, Nodes).

stmts([], Alias, _) ->
    Alias;
stmts([H|T], Alias, Nodes) ->
    stmts(T, stmt(H, Alias, Nodes), Nodes).

stmt({'let', ID}, Alias, Nodes) ->
    #{ID := {var, _Type, Expr}} = Nodes,
    Alias1 = mmb_alias:add_var(ID, Alias, Nodes),
    case Expr of
        {call, _Fun, Args} ->
            mmb_alias:new_call(filter_const([ID|Args], Nodes), Alias1);
        {op, {make, array}, [_]} ->
            Alias1;
        {op, {make, array}, [_, K]} ->
            case is_const(K, Nodes) of
                true ->
                    Alias1;
                false ->
                    mmb_alias:array_elem(ID, K, Alias1)
            end;
        {op, {make, ref}, [Value]} ->
            case is_const(Value, Nodes) of
                true ->
                    Alias1;
                false ->
                    mmb_alias:ref_elem(ID, Value, Alias1)
            end;
        {op, {make, tuple}, List} ->
            mmb_alias:make_tuple(
              ID,
              [case is_const(X, Nodes) of
                   true ->
                       '_';
                   false ->
                       X
               end
               || X <- List],
              Alias1);
        {op, select, [_, X, Y]} ->
            Alias2 =
                case is_const(X, Nodes) of
                    true ->
                        Alias1;
                    false ->
                        mmb_alias:alias(ID, X, Alias1)
                end,
            case is_const(Y, Nodes) of
                true ->
                    Alias2;
                false ->
                    mmb_alias:alias(ID, Y, Alias2)
            end;
        {op, {load, array}, [Array, _]} ->
            mmb_alias:array_elem(Array, ID, Alias1);
        {op, {load, ref}, [Ref]} ->
            mmb_alias:ref_elem(Ref, ID, Alias1);
        {op, {load, tuple, N}, [Tuple]} ->
            case is_const(Tuple, Nodes) of
                true ->
                    Alias1;
                false ->
                    mmb_alias:tuple_elem(Tuple, N, ID, Alias1)
            end;
        {op, {cast, down, Tag}, [Enum]} when is_integer(Tag) ->
            case is_const(Enum, Nodes) of
                true ->
                    Alias1;
                false ->
                    mmb_alias:enum_variant(Enum, Tag, ID, Alias1)
            end;
        {op, {cast, up, Tag}, [Tuple]} when is_integer(Tag) ->
            case is_const(Tuple, Nodes) of
                true ->
                    Alias1;
                false ->
                    mmb_alias:enum_variant(ID, Tag, Tuple, Alias1)
            end;
        {op, {cast, down, {fn, Tag}}, [Closure]} ->
            case is_const(Closure, Nodes) of
                true ->
                    Alias1;
                false ->
                    mmb_alias:closure_variant(Closure, Tag, ID, Alias1)
            end;
        {op, {cast, up, {fn, Tag}}, [Tuple]} ->
            case is_const(Tuple, Nodes) of
                true ->
                    Alias1;
                false ->
                    mmb_alias:closure_variant(ID, Tag, Tuple, Alias1)
            end;
        {op, {load, tag}, _} ->
            Alias1;
        {op, {cmp, _, _}, _} ->
            Alias1;
        {op, {arith, _, _}, _} ->
            Alias1;
        {op, {bool, _}, _} ->
            Alias1;
        {op, is_same_ptr, _} ->
            Alias1
    end;
stmt(fail, Alias, _Nodes) ->
    Alias;
stmt(return, Alias, _Nodes) ->
    Alias;
stmt({return, _}, Alias, _Nodes) ->
    Alias;
stmt({call, _, Args}, Alias, Nodes) ->
    mmb_alias:new_call(filter_const(Args, Nodes), Alias);
stmt({op, {store, array}, [Value, Array, _]}, Alias, Nodes) ->
    case is_const(Value, Nodes) of
        true ->
            Alias;
        false ->
            mmb_alias:array_elem(Array, Value, Alias)
    end;
stmt({op, {store, ref}, [Value, Ref]}, Alias, Nodes) ->
    case is_const(Value, Nodes) of
        true ->
            Alias;
        false ->
            mmb_alias:ref_elem(Ref, Value, Alias)
    end.


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
