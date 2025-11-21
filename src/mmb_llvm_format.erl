%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_llvm_format).

-export([format/1]).

-include("mmb_ssa.hrl").

format(SSA = #ssa{root=Root, nodes=Nodes, types=Typeids}) ->
    Fns = mmb_ssa:collect_fns(SSA),
    Fns1 = maps:to_list(Fns),
    {Types, Consts} = collect_fns(Fns1, #{}, #{}, Nodes),

    Consts1 = tsort(maps:keys(Consts), #{}, Nodes),
    Types1 = add_const_types(Consts1, Types, Typeids, Nodes),
    Types2 = maps:keys(Types1),
    Types3 = types(Types2, Nodes),
    Consts2 = consts(Consts1, Typeids, Nodes),

    Prog = fns(Fns1, Nodes),
    Main = [<<"\n@minimbt_main = alias void(), ptr ">>, fn_name(Root), <<"\n">>],

    iolist_to_binary([Types3, Consts2, Prog, Main]).


collect_fns([], Types, Consts, _Nodes) ->
    {Types, Consts};
collect_fns([{_, Blocks}|T], Types, Consts, Nodes) ->
    {Types1, Consts1} = collect_blocks(Blocks, Types, Consts, Nodes),
    collect_fns(T, Types1, Consts1, Nodes).

add_const_types([], Types, _, _) ->
    Types;
add_const_types([{_, {const, _, {op, {sizeof, Type}, _}}}|T], Types, Typeids, Nodes) ->
    add_const_types(T, Types#{Type => []}, Typeids, Nodes);
add_const_types([{_, {const, _, {op, {make, tuple}, List}}}|T], Types, Typeids, Nodes) ->
    Struct = {struct, mmb_ssa:types(List, Nodes)},
    #{Struct := ID} = Typeids,
    add_const_types(T, Types#{ID => []}, Typeids, Nodes);
add_const_types([_|T], Types, Typeids, Nodes) ->
    add_const_types(T, Types, Typeids, Nodes).

tsort([], _, _) ->
    [];
tsort([H|T], Done, Nodes) ->
    case Done of
        #{H := _} ->
            tsort(T, Done, Nodes);
        _ ->
            #{H := {const, _, {op, _Op, List}} = Const} = Nodes,
            case [ID || ID <- List, is_op_const(ID, Nodes), not maps:is_key(ID, Done)] of
                [] ->
                    [{H, Const}|tsort(T, Done#{H => []}, Nodes)];
                List1 ->
                    tsort(append(List1, [H|T]), Done, Nodes)
            end
    end.

append([], List) ->
    List;
append([H|T], List) ->
    [H|append(T, List)].

is_op_const(ID, Nodes) ->
    #{ID := {const, _, Expr}} = Nodes,
    case Expr of
        {op, _, _} ->
            true;
        _ ->
            false
    end.


collect_blocks([], Types, Consts, _Nodes) ->
    {Types, Consts};
collect_blocks([H|T], Types, Consts, Nodes) ->
    #{H := {bb, _, Output, Stmts}} = Nodes,
    {Types1, Consts1} = collect_stmts(Stmts, Types, Consts, Nodes),
    Consts2 = collect_output(Output, Consts1, Nodes),
    collect_blocks(T, Types1, Consts2, Nodes).

collect_output(none, Consts, _) ->
    Consts;
collect_output({_, Values}, Consts, Nodes) ->
    collect_const(Values, Consts, Nodes);
collect_output({'if', _, True, False}, Consts, Nodes) ->
    Consts1 = collect_output(True, Consts, Nodes),
    collect_output(False, Consts1, Nodes).

collect_stmts([], Types, Consts, _Nodes) ->
    {Types, Consts};
collect_stmts([H|T], Types, Consts, Nodes) ->
    Types1 = collect_type(H, Types, Nodes),
    Consts1 = collect_const(mmb_ssa:uses(H, Nodes), Consts, Nodes),
    collect_stmts(T, Types1, Consts1, Nodes).


collect_type({'let', ID}, Types, Nodes) ->
    #{ID := {var, _, Expr}} = Nodes,
    case Expr of
        {op, {gep, Struct}, _} ->
            Types#{Struct => []};
        _ ->
            Types
    end;
collect_type(_, Types, _) ->
    Types.

collect_const([], Consts, _Nodes) ->
    Consts;
collect_const([H|T], Consts, Nodes) ->
    case Nodes of
        #{H := {const, _, {op, _, _}}} ->
            collect_const(T, Consts#{H => []}, Nodes);
        _ ->
            collect_const(T, Consts, Nodes)
    end.



types([], _Nodes) ->
    [];
types([H|T], Nodes) ->
    [type(H, Nodes)|types(T, Nodes)].

type(ID, Nodes) when is_integer(ID) ->
    #{ID := {type, {struct, List}}} = Nodes,
    [type_name(ID), <<" = type {">>, type_list(List), <<"}\n">>];
type(ID, _) when is_atom(ID) ->
    [].

type_name(ID) when is_integer(ID) ->
    [<<"%T">>, integer_to_binary(ID)];
type_name(ID) when is_atom(ID) ->
    atom_to_binary(ID).


type_list([]) ->
    [];
type_list([E]) ->
    [type(E)];
type_list([H|T]) ->
    [type(H), <<", ">>|type_list(T)].

type(X) when is_atom(X) ->
    atom_to_binary(X).


consts(List, Typeids, Nodes) ->
    [const(ID, Op, Args, Typeids, Nodes)
     || {ID, {const, _, {op, Op, Args}}} <- List].

const(ID, {make, tuple}, List, Typeids, Nodes) ->
    Struct = {struct, mmb_ssa:types(List, Nodes)},
    #{Struct := Type} = Typeids,
    [global_name(ID), <<"= private global ">>, type_name(Type),
     <<" {">>, args(List, Nodes), <<"}\n">>];
const(ID, {zero, Type}, [], _, _) ->
    [global_name(ID), <<"= private global ">>, type(Type),
     <<" zeroinitializer\n">>];
const(_, {sizeof, _}, [], _, _) ->
    [].


global_name(ID) when is_integer(ID) ->
    [<<"@v">>, integer_to_binary(ID)].


fn_name(ID) when is_integer(ID) ->
    [<<"@f">>, integer_to_binary(ID)];
fn_name(sin) ->
    [<<"@llvm.sin.f64">>];
fn_name(cos) ->
    [<<"@llvm.cos.f64">>];
fn_name(sqrt) ->
    [<<"@llvm.sqrt.f64">>];
fn_name(abs_int) ->
    [<<"@llvm.abs.i32">>];
fn_name(abs_float) ->
    [<<"@llvm.fabs.f64">>];
fn_name(max_float) ->
    [<<"@llvm.maxnum.f64">>];
fn_name(Atom) when is_atom(Atom) ->
    [<<"@minimbt_">>, atom_to_binary(Atom)].

var_name(ID) when is_integer(ID) ->
    [<<"%v">>, integer_to_binary(ID)].

var_name(ID, Nodes) when is_integer(ID) ->
    case Nodes of
        #{ID := {var, _Type, _Expr}} ->
            var_name(ID);
        #{ID := {const, _Type, Expr}} ->
            case Expr of
                {fn, Fn} ->
                    fn_name(Fn);
                X when is_integer(X) ->
                    integer_to_binary(X);
                X when is_float(X) ->
                    mmb_compat:encode_float(X);
                true ->
                    <<"1">>;
                false ->
                    <<"0">>;
                nan ->
                    <<"0x7ff8000000000000">>;
                inf ->
                    <<"0x7ff0000000000000">>;
                ninf ->
                    <<"0xfff0000000000000">>;
                null ->
                    <<"null">>;
                {op, {make, tuple}, _} ->
                    global_name(ID);
                {op, {zero, _}, _} ->
                    global_name(ID);
                {op, {sizeof, T}, []} ->
                    [<<"add(i32 ptrtoint(ptr getelementptr(">>, type_name(T), <<", ptr null, i32 1) to i32), i32 15)">>]
            end
    end.

values([], _) ->
    [];
values([E], Nodes) ->
    [value(E, Nodes)];
values([H|T], Nodes) ->
    H1 = value(H, Nodes),
    T1 = values(T, Nodes),
    [H1, <<", ">>|T1].

value(ID, Nodes) when is_integer(ID) ->
    var_name(ID, Nodes).

var(ID, Nodes) when is_integer(ID) ->
    #{ID := {_, Type, _}} = Nodes,
    [type(Type), <<" ">>, var_name(ID, Nodes)].

args([], _) ->
    [];
args([E], Nodes) ->
    [arg(E, Nodes)];
args([H|T], Nodes) ->
    H1 = arg(H, Nodes),
    T1 = args(T, Nodes),
    [H1, <<", ">>|T1].

arg(ID, Nodes) ->
    var(ID, Nodes).

label(ID) ->
    [<<"L">>, integer_to_binary(ID)].


fns(List, Nodes) ->
    [fn(X, Nodes) || X <- List].

fn({ID, []}, _Nodes) when is_atom(ID) ->
    #{ID := {Params, Return}} =
        #{
          read_int =>  {[], i32},
          print_int => {[i32], void},
          read_char =>  {[], i32},
          print_char => {[i32], void},
          print_endline => {[], void},
          int_of_float => {[double], i32},
          float_of_int =>  {[i32], double},
          truncate => {[double], i32},
          floor => {[double], double},
          abs_int => {[i32, i1], i32},
          abs_float => {[double], double},
          max_float => {[double, double], double},
          sqrt => {[double], double},
          sin => {[double], double},
          cos => {[double], double},
          atan => {[double], double},
          malloc => {[i32], ptr},
          create_array => {[i32, i32], ptr},
          create_float_array => {[i32, double], ptr},
          create_ptr_array => {[i32, ptr], ptr}
        },

    [<<"\ndeclare ">>, type(Return), <<" ">>,
     fn_name(ID), <<"(">>, type_list(Params), <<")\n">>];
fn({ID, Blocks}, Nodes) when is_integer(ID) ->
    #{ID := {fn, none, Params, ReturnType, _, _}} = Nodes,
    PhiMap = mmb_ssa:collect_phi(Blocks, Nodes),
    Blocks1 = blocks(Blocks, PhiMap, Nodes),
    [<<"\ndefine private ">>, type(ReturnType), <<" ">>,
     fn_name(ID), <<"(">>, args(Params, Nodes), <<") {">>,
     Blocks1, <<"}\n">>].


blocks(List, PhiMap, Nodes) ->
    [block(X, PhiMap, Nodes) || X <- List].

block(ID, PhiMap, Nodes) ->
    #{ID := {bb, Input, Output, Stmts}} = Nodes,
    Input1 =
        case Input of
            [] ->
                [];
            _ ->
                #{ID := Phi} = PhiMap,
                inputs(Input, Phi, Nodes)
        end,
    Stmts1 = stmts(Stmts, Nodes),
    Outputs1 = output(Output, Nodes),
    [<<"\n">>, label(ID), <<":\n">>, Input1, Stmts1, Outputs1].


inputs([], _, _) ->
    [];
inputs([H|T], Phi, Nodes) ->
    {PhiH, PhiT} = consume_phi(Phi),
    H1 = input(H, PhiH, Nodes),
    T1 = inputs(T, PhiT, Nodes),
    [<<"  ">>,H1|T1].

input(ID, Phi, Nodes) ->
    #{ID := {var, Type, phi}} = Nodes,
    [var_name(ID, Nodes),
     <<" = phi ">>,
     type(Type),
     <<" ">>,
     phi_list(Phi, Nodes),
     <<"\n">>].

phi_list([], _) ->
    [];
phi_list([E], Nodes) ->
    [phi(E, Nodes)];
phi_list([H|T], Nodes) ->
    H1 = phi(H, Nodes),
    T1 = phi_list(T, Nodes),
    [H1, <<", ">>|T1].

phi({Block, ID}, Nodes) ->
    [<<"[">>,
     var_name(ID, Nodes),
     <<", %">>,
     label(Block),
     <<"]">>].

consume_phi([]) ->
    {[], []};
consume_phi([{BlockID, [ID|Rest]}|T]) ->
    H1 = {BlockID, ID},
    H2 = {BlockID, Rest},
    {T1, T2} = consume_phi(T),
    {[H1|T1], [H2|T2]}.


output(none, _) ->
    [];
output({Exit, _}, _) ->
    [<<"  br label %">>, label(Exit), <<"\n">>];
output({'if', Cond, {True, _}, {False, _}}, Nodes) ->
    [<<"  br ">>, var(Cond, Nodes),
     <<", label %">>, label(True),
     <<", label %">>, label(False),
     <<"\n">>].

stmts(List, Nodes) ->
    [stmt(X, Nodes) || X <- List].

stmt({'let', ID}, Nodes) ->
    #{ID := {var, Type, Expr}} = Nodes,
    [<<"  ">>, var_name(ID), <<" = ">>, expr(Type, Expr, Nodes)];
stmt(fail, _) ->
    <<"  call void @llvm.trap()\n  unreachable\n">>;
stmt(return, _) ->
    <<"  ret void\n">>;
stmt({return, Expr}, Nodes) ->
    [<<"  ret ">>, var(Expr, Nodes), <<"\n">>];
stmt({op, store, List}, Nodes) ->
    [<<"  store ">>, args(List, Nodes), <<"\n">>];
stmt({call, Fun, Args}, Nodes) ->
    [<<"  ">>, call(void, Fun, Args, Nodes)].

expr(Type, {call, Fun, Args}, Nodes) ->
    call(Type, Fun, Args, Nodes);
expr(_Type, {op, {gep, Type}, List}, Nodes) ->
    [<<"getelementptr ">>, type_name(Type), <<", ">>, args(List, Nodes), <<"\n">>];
expr(_Type, {op, select, List}, Nodes) ->
    [<<"select ">>, args(List, Nodes), <<"\n">>];
expr(Type, {op, load, List}, Nodes) ->
    [<<"load ">>, type(Type), <<", ">>, args(List, Nodes), <<"\n">>];
expr(Type, {op, fptosi, [X]}, Nodes) ->
    [<<"fptosi ">>, arg(X, Nodes), <<" to ">>, type(Type), <<"\n">>];
expr(Type, {op, sitofp, [X]}, Nodes) ->
    [<<"sitofp ">>, arg(X, Nodes), <<" to ">>, type(Type), <<"\n">>];
expr(_Type, {op, neg, List}, Nodes) ->
    [<<"sub i32 0, ">>, values(List, Nodes), <<"\n">>];
expr(_Type, {op, 'not', List}, Nodes) ->
    [<<"xor i1 1, ">>, values(List, Nodes), <<"\n">>];
expr(_Type, {op, Op, [H|_]=List}, Nodes) when is_atom(Op) ->
    #{H := {_, Type, _}} = Nodes,
    [atom_to_binary(Op), <<" ">>, type(Type), <<" ">>, values(List, Nodes), <<"\n">>].

call(Type, Fun, Args, Nodes) ->
    [<<"call ">>, type(Type), <<" ">>, var_name(Fun, Nodes), <<"(">>, args(Args, Nodes), <<")\n">>].
