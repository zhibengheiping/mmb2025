%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_parser).

-feature(maybe_expr, enable).

-export([parse/1]).

parse(Tokens) ->
    maybe
        {ok, Types, Globals, []} ?= prog(Tokens),
        {ok, Types, Globals}
    end.

prog([]) ->
    {ok, [], [], []};
prog(Tokens) ->
    maybe
        {ok, H, Tokens1} ?= top_level(Tokens),
        {ok, T1, T2, Tokens2} ?= prog(Tokens1),
        case H of
            {typedef, Kind, Gen, Name, Body} ->
                {ok, [{Kind, Gen, Name, Body}|T1], T2, Tokens2};
            _ ->
                {ok, T1, [H|T2], Tokens2}
        end
    end.

top_level(['let', {vid, Name}|Tokens]) ->
    maybe
        {ok, Type, Tokens1} ?= type_annotation(Tokens),
        {ok, Tokens2} ?= consume('=', Tokens1),
        {ok, Expr, Tokens3} ?= expr(Tokens2),
        {ok, Tokens4} ?= consume(';', Tokens3),
        {ok, {'let', Name, Type, Expr}, Tokens4}
    end;
top_level([fn, {vid, <<"main">>}, '{'|Tokens]) ->
    maybe
        {ok, Body, Tokens1} ?= block_expr(Tokens),
        {ok, {fn, [], <<"main">>, [], 'Unit', Body}, Tokens1}
    end;
top_level([fn|Tokens]) ->
    maybe
        {ok, Gen, Tokens1} ?= gen_params(Tokens),
        {ok, Name, Tokens2} ?= vid(Tokens1),
        {ok, Tokens3} ?= consume('(', Tokens2),
        {ok, Params, Tokens4} ?= param_list(Tokens3),
        {ok, Tokens5} ?= consume('->', Tokens4),
        {ok, Type, Tokens6} ?= type(Tokens5),
        {ok, Tokens7} ?= consume('{', Tokens6),
        {ok, Body, Tokens8} ?= block_expr(Tokens7),
        {ok, {fn, Gen, Name, Params, Type, Body}, Tokens8}
    end;
top_level([struct, {tid, Name}|Tokens]) ->
    maybe
        {ok, Gen, Tokens1} ?= gen_params(Tokens),
        {ok, Tokens2} ?= consume('{', Tokens1),
        {ok, Fields, Tokens3} ?= struct_field_list(Tokens2),
        {ok, {typedef, struct, Gen, Name, Fields}, Tokens3}
    end;
top_level([enum, {tid, Name}|Tokens]) ->
    maybe
        {ok, Gen, Tokens1} ?= gen_params(Tokens),
        {ok, Tokens2} ?= consume('{', Tokens1),
        {ok, Fields, Tokens3} ?= enum_variant_list(Tokens2),
        {ok, {typedef, enum, Gen, Name, Fields}, Tokens3}
    end.

type_annotation([':'|Tokens])->
    type(Tokens);
type_annotation(Tokens) ->
    {ok, '_', Tokens}.

gen_params(['[', ']'|Tokens]) ->
    {ok, [], Tokens};
gen_params(['[', {tid, Name}|Tokens]) ->
    gen_params(Name, Tokens);
gen_params(Tokens) ->
    {ok, [], Tokens}.

gen_params(E, [']'|Tokens]) ->
    {ok, [E], Tokens};
gen_params(H, [','|Tokens]) ->
    maybe
        {ok, Name, Tokens1} ?= tid(Tokens),
        {ok, T, Tokens2} ?= gen_params(Name, Tokens1),
        {ok, [H|T], Tokens2}
    end.

param_list([')'|Tokens]) ->
    {ok, [], Tokens};
param_list(Tokens) ->
    maybe
        {ok, Param, Tokens1} ?= param(Tokens),
        param_list(Param, Tokens1)
    end.

param_list(H, [',' | Tokens]) ->
    maybe
        {ok, Param, Tokens1} ?= param(Tokens),
        {ok, T, Tokens2} ?= param_list(Param, Tokens1),
        {ok, [H|T], Tokens2}
    end;
param_list(E, [')'|Tokens]) ->
    {ok, [E], Tokens}.

param([{vid, Name}, ':'|Tokens]) ->
    maybe
        {ok, Type, Tokens1} ?= type(Tokens),
        {ok, {Name, Type}, Tokens1}
    end.

nt_param_list([')'|Tokens]) ->
    {ok, [], Tokens};
nt_param_list(Tokens) ->
    maybe
        {ok, Param, Tokens1} ?= nt_param(Tokens),
        nt_param_list(Param, Tokens1)
    end.

nt_param_list(H, [',' | Tokens]) ->
    maybe
        {ok, Param, Tokens1} ?= nt_param(Tokens),
        {ok, T, Tokens2} ?= nt_param_list(Param, Tokens1),
        {ok, [H|T], Tokens2}
    end;
nt_param_list(E, [')'|Tokens]) ->
    {ok, [E], Tokens}.

nt_param([{vid, Name}|Tokens]) ->
    maybe
        {ok, Type, Tokens1} ?= type_annotation(Tokens),
        {ok, {Name, Type}, Tokens1}
    end.

block_expr(['}'|Tokens]) ->
    {ok, {block, [], {literal, 'Unit', '()'}}, Tokens};
block_expr(Tokens) ->
    maybe
        {ok, Stmt, Tokens1} ?= stmt(Tokens),
        block_expr(Stmt, Tokens1)
    end.

block_expr({'Last', Expr}, Tokens) ->
    {ok, {block, [], Expr}, Tokens};
block_expr(E, ['}'|Tokens]) ->
    {ok, {block, [], E}, Tokens};
block_expr(H, Tokens) ->
    maybe
        {ok, Stmt, Tokens1} ?= stmt(Tokens),
        {ok, Block, Tokens2} ?= block_expr(Stmt, Tokens1),
        {block, T, Expr} = Block,
        {ok, {block, [H|T], Expr}, Tokens2}
    end.

struct_field_list(['}'|Tokens]) ->
    {ok, [], Tokens};
struct_field_list([{vid, Name}, ':'|Tokens]) ->
    maybe
        {ok, Type, Tokens1} ?= type(Tokens),
        case Tokens1 of
            [';'|Tokens2] ->
                ok;
            _ ->
                Tokens2 = Tokens1
        end,
        {ok, T, Tokens3} ?= struct_field_list(Tokens2),
        {ok, [{Name, Type}|T], Tokens3}
    end.

enum_variant_list(['}'|Tokens]) ->
    {ok, [], Tokens};
enum_variant_list([{tid, Name}, '('|Tokens]) ->
    maybe
        {ok, Types, Tokens1} ?= type_list(Tokens),
        case Tokens1 of
            [';'|Tokens2] ->
                ok;
            _ ->
                Tokens2 = Tokens1
        end,
        {ok, T, Tokens3} ?= enum_variant_list(Tokens2),
        {ok, [{Name, Types}|T], Tokens3}
    end;
enum_variant_list([{tid, Name}|Tokens]) ->
    maybe
        case Tokens of
            [';'|Tokens1] ->
                ok;
            _ ->
                Tokens1 = Tokens
        end,
        {ok, T, Tokens2} ?= enum_variant_list(Tokens1),
        {ok, [{Name, []}|T], Tokens2}
    end.


stmt(['let', '('|Tokens]) ->
    maybe
        {ok, Names, Tokens1} ?= bindings(Tokens),
        {ok, Type, Tokens2} ?= type_annotation(Tokens1),
        {ok, Tokens3} ?= consume('=', Tokens2),
        {ok, Expr, Tokens4} ?= expr(Tokens3),
        {ok, Tokens5} ?= consume(';', Tokens4),
        {ok, {destruct, Names, Type, Expr}, Tokens5}
    end;
stmt(['let', 'mut'|Tokens]) ->
    maybe
        {ok, Name, Tokens1} ?= vid(Tokens),
        {ok, Type, Tokens2} ?= type_annotation(Tokens1),
        {ok, Tokens3} ?= consume('=', Tokens2),
        {ok, Expr, Tokens4} ?= expr(Tokens3),
        {ok, Tokens5} ?= consume(';', Tokens4),
        {ok, {'let', Name, {ref, Type}, {ref, Expr}}, Tokens5}
    end;
stmt(['let'|Tokens]) ->
    maybe
        {ok, Name, Tokens1} ?= binding(Tokens),
        {ok, Type, Tokens2} ?= type_annotation(Tokens1),
        {ok, Tokens3} ?= consume('=', Tokens2),
        {ok, Expr, Tokens4} ?= expr(Tokens3),
        {ok, Tokens5} ?= consume(';', Tokens4),
        {ok, {'let', Name, Type, Expr}, Tokens5}
    end;
stmt([fn, {vid, Name}, '('|Tokens]) ->
    maybe
        {ok, Params, Tokens1} ?= nt_param_list(Tokens),
        {ok, ReturnType, Tokens2} ?= return_type(Tokens1),
        {ok, Tokens3} ?= consume('{', Tokens2),
        {ok, Body, Tokens4} ?= block_expr(Tokens3),
        Type =
            case ReturnType of
                none -> '_';
                _ -> ReturnType
            end,
        {ok, {fn, Name, Params, Type, Body}, Tokens4}
    end;
stmt([while|Tokens]) ->
    maybe
        {ok, Expr, Tokens1} ?= expr(Tokens),
        {ok, Tokens2} ?= consume('{', Tokens1),
        {ok, Stmts, Tokens3} ?= stmts(Tokens2),
        {ok, {'if', Expr, {block, [{do_while, Expr, Stmts}], {literal, 'Unit', '()'}}, {literal, 'Unit', '()'}}, Tokens3}
    end;
stmt([return, ';'|Tokens]) ->
    {ok, {return, {literal, 'Unit', '()'}}, Tokens};
stmt([return|Tokens]) ->
    maybe
        {ok, Expr, Tokens1} ?= expr(Tokens),
        {ok, Tokens2} ?= consume(';', Tokens1),
        {ok, {return, Expr}, Tokens2}
    end;
stmt(Tokens) ->
    maybe
        {ok, Expr, Tokens1} ?= expr(Tokens),
        last(Expr, Tokens1)
    end.

bindings(Tokens) ->
    maybe
        {ok, Binding, Tokens1} ?= binding(Tokens),
        bindings(Binding, Tokens1)
    end.

bindings(E, [')'|Tokens]) ->
    {ok, [E], Tokens};
bindings(H, [','|Tokens]) ->
    maybe
        {ok, Binding, Tokens1} ?= binding(Tokens),
        {ok, T, Tokens2} ?= bindings(Binding, Tokens1),
        {ok, [H|T], Tokens2}
    end.

binding(['_'|Tokens]) ->
    {ok, '_', Tokens};
binding([{vid, Name}|Tokens]) ->
    {ok, Name, Tokens}.

vid([{vid, Name}|Tokens]) ->
    {ok, Name, Tokens}.

tid([{tid, Name}|Tokens]) ->
    {ok, Name, Tokens}.

return_type(['->'|Tokens]) ->
    type(Tokens);
return_type(Tokens) ->
    {ok, none, Tokens}.

stmts(['}'|Tokens]) ->
    {ok, [], Tokens};
stmts(Tokens) ->
    maybe
        {ok, Stmt, Tokens1} ?= stmt(Tokens),
        stmts(Stmt, Tokens1)
    end.

stmts({'Last', _}, _) ->
    error;
stmts(E, ['}'|Tokens]) ->
    {ok, [E], Tokens};
stmts(H, Tokens) ->
    maybe
        {ok, Stmt, Tokens1} ?= stmt(Tokens),
        {ok, T, Tokens2} ?= stmts(Stmt, Tokens1),
        {ok, [H|T], Tokens2}
    end.

last(Expr, ['}'|Tokens]) ->
    {ok, {'Last', Expr}, Tokens};
last({var, _}=Expr, ['='|Tokens]) ->
    assign(Expr, Tokens);
last({sub, _, _}=Expr, ['='|Tokens]) ->
    assign(Expr, Tokens);
last({attr, _, _}=Expr, ['='|Tokens]) ->
    assign(Expr, Tokens);
last(Expr, [';'|Tokens]) ->
    {ok, Expr, Tokens}.

assign(Expr, Tokens) ->
    maybe
        {ok, Value, Tokens1} ?= expr(Tokens),
        {ok, Tokens2} ?= consume(';', Tokens1),
        {ok, {assign, Expr, Value}, Tokens2}
    end.

args([')'|Tokens]) ->
    {ok, [], Tokens};
args(Tokens) ->
    maybe
        {ok, Arg, Tokens1} ?= expr(Tokens),
        args(Arg, Tokens1)
    end.

args(E, [')'|Tokens]) ->
    {ok, [E], Tokens};
args(H, [','|Tokens]) ->
    maybe
        {ok, Arg, Tokens1} ?= expr(Tokens),
        {ok, T, Tokens2} ?= args(Arg, Tokens1),
        {ok, [H|T], Tokens2}
    end.

expr(Tokens) ->
    or_expr(Tokens).

or_expr(Tokens) ->
    maybe
        {ok, LHS, Tokens1} ?= and_expr(Tokens),
        or_expr(LHS, Tokens1)
    end.

or_expr(LHS, ['||'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= and_expr(Tokens),
        {ok, RHS1, Tokens2} ?= or_expr(RHS, Tokens1),
        {ok, {'if', LHS, {literal, 'Bool', true}, RHS1}, Tokens2}
    end;
or_expr(LHS, Tokens) ->
    {ok, LHS, Tokens}.

and_expr(Tokens) ->
    maybe
        {ok, LHS, Tokens1} ?= cmp_expr(Tokens),
        and_expr(LHS, Tokens1)
    end.

and_expr(LHS, ['&&'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= cmp_expr(Tokens),
        {ok, RHS1, Tokens2} ?= and_expr(RHS, Tokens1),
        {ok, {'if', LHS, RHS1, {literal, 'Bool', false}}, Tokens2}
    end;
and_expr(LHS, Tokens) ->
    {ok, LHS, Tokens}.


cmp_expr(Tokens) ->
    maybe
        {ok, LHS, Tokens1} ?= add_expr(Tokens),
        cmp_expr(LHS, Tokens1)
    end.

cmp_expr(LHS, ['=='|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= add_expr(Tokens),
        {ok, {op, {cmp, '=='}, LHS, RHS}, Tokens1}
    end;
cmp_expr(LHS, ['!='|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= add_expr(Tokens),
        {ok, {op, {cmp, '!='}, LHS, RHS}, Tokens1}
    end;
cmp_expr(LHS, ['>='|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= add_expr(Tokens),
        {ok, {op, {cmp, '>='}, LHS, RHS}, Tokens1}
    end;
cmp_expr(LHS, ['<='|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= add_expr(Tokens),
        {ok, {op, {cmp, '<='}, LHS, RHS}, Tokens1}
    end;
cmp_expr(LHS, ['>'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= add_expr(Tokens),
        {ok, {op, {cmp, '>'}, LHS, RHS}, Tokens1}
    end;
cmp_expr(LHS, ['<'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= add_expr(Tokens),
        {ok, {op, {cmp, '<'}, LHS, RHS}, Tokens1}
    end;
cmp_expr(LHS, Tokens) ->
    {ok, LHS, Tokens}.


add_expr(Tokens) ->
    maybe
        {ok, LHS, Tokens1} ?= mul_expr(Tokens),
        add_expr(LHS, Tokens1)
    end.

add_expr(LHS, ['+'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= mul_expr(Tokens),
        add_expr({op, {arith, '+'}, LHS, RHS}, Tokens1)
    end;
add_expr(LHS, ['-'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= mul_expr(Tokens),
        add_expr({op, {arith, '-'}, LHS, RHS}, Tokens1)
    end;
add_expr(LHS, Tokens) ->
    {ok, LHS, Tokens}.


mul_expr(Tokens) ->
    maybe
        {ok, LHS, Tokens1} ?= if_expr(Tokens),
        mul_expr(LHS, Tokens1)
    end.

mul_expr(LHS, ['*'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= if_expr(Tokens),
        mul_expr({op, {arith, '*'}, LHS, RHS}, Tokens1)
    end;
mul_expr(LHS, ['/'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= if_expr(Tokens),
        mul_expr({op, {arith, '/'}, LHS, RHS}, Tokens1)
    end;
mul_expr(LHS, ['%'|Tokens]) ->
    maybe
        {ok, RHS, Tokens1} ?= if_expr(Tokens),
        mul_expr({op, {arith, '%'}, LHS, RHS}, Tokens1)
    end;
mul_expr(LHS, Tokens) ->
    {ok, LHS, Tokens}.


if_expr(['if'|Tokens]) ->
    maybe
        {ok, Cond, Tokens1} ?= expr(Tokens),
        {ok, Tokens2} ?= consume('{', Tokens1),
        {ok, True, Tokens3} ?= block_expr(Tokens2),
        {ok, False, Tokens4} ?= else_expr(Tokens3),
        {ok, {'if', Cond, True, False}, Tokens4}
    end;
if_expr([match|Tokens]) ->
    maybe
        {ok, Expr, Tokens1} ?= expr(Tokens),
        {ok, Tokens2} ?= consume('{', Tokens1),
        {ok, List, Tokens3} ?= match_arm_list(Tokens2),
        {ok, {match, Expr, List}, Tokens3}
    end;
if_expr(Tokens) ->
    get_expr(Tokens).

else_expr(['else', '{'|Tokens]) ->
    block_expr(Tokens);
else_expr(['else'|Tokens]) ->
    if_expr(Tokens);
else_expr(Tokens) ->
    {ok, {literal, 'Unit', '()'}, Tokens}.

match_arm_list(['}'|Tokens]) ->
    {ok, [], Tokens};
match_arm_list(Tokens) ->
    maybe
        {ok, Pattern, Tokens1} ?= pattern(Tokens),
        {ok, Tokens2} ?= consume('=>', Tokens1),
        {ok, Expr, Tokens3} ?= expr(Tokens2),
        case Tokens3 of
            [';'|Tokens4] ->
                Tokens4;
            _ ->
                Tokens4 = Tokens3
        end,
        {ok, T, Tokens5} ?= match_arm_list(Tokens4),
        {ok, [{Pattern, Expr}|T], Tokens5}
    end.

pattern(['('|Tokens]) ->
    maybe
        {ok, List, Tokens1} ?= pattern_list(Tokens),
        {ok, {tuple, List}, Tokens1}
    end;
pattern([true|Tokens]) ->
    {ok, {literal, 'Bool', true}, Tokens};
pattern([false|Tokens]) ->
    {ok, {literal, 'Bool', false}, Tokens};
pattern([{num, I}|Tokens]) ->
    {ok, {literal, 'Int', binary_to_integer(I)}, Tokens};
pattern(['_'|Tokens]) ->
    {ok, '_', Tokens};
pattern([{tid, Type}, '::', {tid, Name}|Tokens]) ->
    enum_pattern(Type, Name, Tokens);
pattern([{tid, Name}|Tokens]) ->
    enum_pattern('_', Name, Tokens);
pattern([{vid, Name}|Tokens]) ->
    {ok, {var, Name}, Tokens}.

pattern_list([')'|Tokens]) ->
    {ok, [], Tokens};
pattern_list(Tokens) ->
    maybe
        {ok, Pattern, Tokens1} ?= pattern(Tokens),
        pattern_list(Pattern, Tokens1)
    end.

pattern_list(E, [')'|Tokens]) ->
    {ok, [E], Tokens};
pattern_list(H, [','|Tokens]) ->
    maybe
        {ok, Pattern, Tokens1} ?= pattern(Tokens),
        {ok, T, Tokens2} ?= pattern_list(Pattern, Tokens1),
        {ok, [H|T], Tokens2}
    end.


enum_pattern(Type, Name, ['('|Tokens]) ->
    maybe
        {ok, List, Tokens1} ?= pattern_list(Tokens),
        {ok, {enum, Type, Name, List}, Tokens1}
    end;
enum_pattern(Type, Name, Tokens) ->
    {ok, {enum, Type, Name, []}, Tokens}.

get_expr(Tokens) ->
    maybe
        {ok, Expr, Tokens1} ?= value_expr(Tokens),
        get_expr(Expr, Tokens1)
    end.

get_expr(Expr, ['['|Tokens]) ->
    maybe
        {ok, Sub, Tokens1} ?= expr(Tokens),
        {ok, Tokens2} ?= consume(']', Tokens1),
        get_expr({sub, Expr, Sub}, Tokens2)
    end;
get_expr(Expr, ['('|Tokens]) ->
    maybe
        {ok, Args, Tokens1} ?= args(Tokens),
        get_expr({call, Expr, Args}, Tokens1)
    end;
get_expr(Expr, ['.'|Tokens]) ->
    maybe
        {ok, Name, Tokens1} ?= vid(Tokens),
        get_expr({attr, Expr, Name}, Tokens1)
    end;
get_expr(Expr, Tokens) ->
    {ok, Expr, Tokens}.

value_expr(['('|Tokens]) ->
    maybe
        {ok, Args, Tokens1} ?= args(Tokens),
        Expr =
            case Args of
                [] -> {literal, 'Unit', '()'};
                [E] -> E;
                _ -> {tuple, Args}
            end,
        {ok, Expr, Tokens1}
    end;
value_expr(['['|Tokens]) ->
    maybe
        {ok, List, Tokens1} ?= array(Tokens),
        {ok, {array, List}, Tokens1}
    end;
value_expr(['{'|Tokens]) ->
    block_expr(Tokens);
value_expr([true|Tokens]) ->
    {ok, {literal, 'Bool', true}, Tokens};
value_expr([false|Tokens]) ->
    {ok, {literal, 'Bool', false}, Tokens};
value_expr(['-'|Tokens]) ->
    maybe
        {ok, Expr, Tokens1} ?= value_expr(Tokens),
        {ok, {op, {arith, neg}, Expr}, Tokens1}
    end;
value_expr([{num, I}, '.', {num, F}|Tokens]) ->
    {ok, {literal, 'Double', mmb_compat:parse_float(I, F)}, Tokens};
value_expr([{num, I}, '.'|Tokens]) ->
    {ok, {literal, 'Double', mmb_compat:parse_float(I)}, Tokens};
value_expr([{num, I}|Tokens]) ->
    {ok, {literal, 'Int', binary_to_integer(I)}, Tokens};
value_expr(['!'|Tokens]) ->
    maybe
        {ok, Expr, Tokens1} ?= expr(Tokens),
        {ok, {op, {bool, 'not'}, Expr}, Tokens1}
    end;
value_expr(['Array', '::', {vid, <<"make">>}, '(' | Tokens]) ->
    maybe
        {ok, Expr1, Tokens1} ?= expr(Tokens),
        {ok, Tokens2} ?= consume(',', Tokens1),
        {ok, Expr2, Tokens3} ?= expr(Tokens2),
        {ok, Tokens4} ?= consume(')', Tokens3),
        {ok, {array, Expr1, Expr2}, Tokens4}
    end;
value_expr([{tid, Name}, '::', '{'|Tokens]) ->
    maybe
        {ok, List, Tokens1} ?= struct_field_expr_list(Tokens),
        {ok, {struct, Name, List}, Tokens1}
    end;
value_expr([{tid, Type}, '::', {tid, Name}|Tokens]) ->
    enum_expr(Type, Name, Tokens);
value_expr([{tid, Name}|Tokens]) ->
    enum_expr('_', Name, Tokens);
value_expr([{vid, Name}|Tokens]) ->
    {ok, {var, Name}, Tokens}.

struct_field_expr_list([')'|Tokens]) ->
    {ok, [], Tokens};
struct_field_expr_list(Tokens) ->
    maybe
        {ok, Expr, Tokens1} ?= struct_field_expr(Tokens),
        struct_field_expr_list(Expr, Tokens1)
    end.

struct_field_expr_list(E, ['}'|Tokens]) ->
    {ok, [E], Tokens};
struct_field_expr_list(H, [','|Tokens]) ->
    maybe
        {ok, Expr, Tokens1} ?= struct_field_expr(Tokens),
        {ok, T, Tokens2} ?= struct_field_expr_list(Expr, Tokens1),
        {ok, [H|T], Tokens2}
    end.

struct_field_expr([{vid, Name}, ':'|Tokens]) ->
    maybe
        {ok, Expr, Tokens1} ?= expr(Tokens),
        {ok, {Name, Expr}, Tokens1}
    end.

enum_expr(Type, Name, ['('|Tokens]) ->
    maybe
        {ok, List, Tokens1} ?= args(Tokens),
        {ok, {enum, Type, Name, List}, Tokens1}
    end;
enum_expr(Type, Name, Tokens) ->
    {ok, {enum, Type, Name, []}, Tokens}.


array([']'|Tokens]) ->
    {ok, [], Tokens};
array(Tokens) ->
    maybe
        {ok, Arg, Tokens1} ?= expr(Tokens),
        array(Arg, Tokens1)
    end.

array(E, [']'|Tokens]) ->
    {ok, [E], Tokens};
array(H, [','|Tokens]) ->
    maybe
        {ok, Arg, Tokens1} ?= expr(Tokens),
        {ok, T, Tokens2} ?= array(Arg, Tokens1),
        {ok, [H|T], Tokens2}
    end.


type(['Unit'|Tokens]) ->
    {ok, 'Unit', Tokens};
type(['Bool'|Tokens]) ->
    {ok, 'Bool', Tokens};
type(['Int'|Tokens]) ->
    {ok, 'Int', Tokens};
type(['Double'|Tokens]) ->
    {ok, 'Double', Tokens};
type(['Array', '['|Tokens]) ->
    maybe
        {ok, Type, Tokens1} ?= type(Tokens),
        {ok, Tokens2} ?= consume(']', Tokens1),
        {ok, {array, Type}, Tokens2}
    end;
type(['('|Tokens]) ->
    maybe
        {ok, Types, Tokens1} ?= type_list(Tokens),
        {ok, ReturnType, Tokens2}  ?= return_type(Tokens1),
        Type =
            case ReturnType of
                none ->
                    {tuple, Types};
                _ ->
                    {closure, Types, ReturnType}
            end,
        {ok, Type, Tokens2}
    end;
type([{tid, Name}, '['|Tokens]) ->
    maybe
        {ok, Gen, Tokens1} ?= gen_type_list(Tokens),
        {ok, {type, Name, Gen}, Tokens1}
    end;
type([{tid, Name}|Tokens]) ->
    {ok, {type, Name}, Tokens}.

type_list([')'|Tokens]) ->
    {ok, [], Tokens};
type_list(Tokens) ->
    maybe
        {ok, Type, Tokens1} ?= type(Tokens),
        type_list(Type, Tokens1)
    end.

type_list(E, [')'|Tokens]) ->
    {ok, [E], Tokens};
type_list(H, [','|Tokens]) ->
    maybe
        {ok, Type, Tokens1} ?= type(Tokens),
        {ok, T, Tokens2} ?= type_list(Type, Tokens1),
        {ok, [H|T], Tokens2}
    end.

gen_type_list([']'|Tokens]) ->
    {ok, [], Tokens};
gen_type_list(Tokens) ->
    maybe
        {ok, Type, Tokens1} ?= type(Tokens),
        gen_type_list(Type, Tokens1)
    end.

gen_type_list(E, [']'|Tokens]) ->
    {ok, [E], Tokens};
gen_type_list(H, [','|Tokens]) ->
    maybe
        {ok, Type, Tokens1} ?= type(Tokens),
        {ok, T, Tokens2} ?= gen_type_list(Type, Tokens1),
        {ok, [H|T], Tokens2}
    end.

consume(H, [H|T]) ->
    {ok, T}
%% ;
%% consume(_, _) ->
%%     error
.
