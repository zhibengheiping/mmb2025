%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_lexer).

-feature(maybe_expr, enable).

-compile({parse_transform, brlex}).

-export([tokens/1]).

-rule(true).
-rule(false).
-rule('Unit').
-rule('Bool').
-rule('Int').
-rule('Double').
-rule('Array').
-rule('not').
-rule('if').
-rule('else').
-rule(fn).
-rule('let').
-rule(while).
-rule(return).
-rule(mut).
-rule(enum).
-rule(struct).
-rule(match).
-rule({num, "[0-9]+"}).
-rule('_').
-rule({tid, "[A-Z][a-zA-Z0-9_]*"}).
-rule({vid, "[a-z][a-zA-Z0-9_]*"}).
-rule('=>').
-rule('==').
-rule('!=').
-rule('>=').
-rule('<=').
-rule('>').
-rule('<').
-rule('&&').
-rule('||').
-rule('.').
-rule('+').
-rule('-').
-rule('*').
-rule('/').
-rule('%').
-rule('=').
-rule('(').
-rule(')').
-rule('[').
-rule(']').
-rule('{').
-rule('}').
-rule('->').
-rule('::').
-rule(':').
-rule(';').
-rule(',').
-rule('!').
-rule({skip, "[ \t\r\n]+"}).
-rule({skip, "//[^\r\n]*"}).

tokens(Bin) ->
    tokens(Bin, 0).

tokens(Bin, S) ->
    if byte_size(Bin) =< S ->
            {ok, []};
       true ->
            maybe
                {ok, Name, E} ?= token(Bin, S),
                H = if Name =:= num; Name =:= vid; Name =:= tid ->
                            {Name, binary:part(Bin, S, E-S)};
                       true ->
                            Name
                    end,
                {ok, T} ?= tokens(Bin, E),
                {ok,
                 case H of
                     'skip' ->
                         T;
                     _ ->
                         [H|T]
                 end}
            end
    end.

token(Bin, S) ->
    token(Bin, error, S, 1).
