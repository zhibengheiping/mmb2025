%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb).

-export([main/1]).

parse_args(Acc, []) ->
    {ok, Acc};
parse_args(Acc, ["--typecheck"|Rest]) ->
    parse_args(Acc#{typecheck => true}, Rest);
parse_args(Acc, ["-o", Output|Rest]) ->
    parse_args(Acc#{output => Output}, Rest);
parse_args(Acc, [Input|Rest]) ->
    parse_args(Acc#{input => Input}, Rest).

main(Args) ->
    {ok, Config} = parse_args(#{}, Args),
    #{input := Input} = Config,
    {ok, Bin} = file:read_file(Input),
    Bin1 = compile(Bin),
    case Config of
        #{output := Output} ->
            ok = file:write_file(Output, Bin1);
        #{typecheck := true} ->
            ok;
        _ ->
            mmb_compat:print(Bin1)
    end.

pass(gp, SSA) ->
    mmb_ssa_gp:convert(SSA);
pass(cbc, SSA) ->
    mmb_ssa_cbc:convert(SSA);
pass(select, SSA) ->
    mmb_ssa_select:convert(SSA);
pass(allphis, SSA) ->
    mmb_ssa_allphis:convert(SSA);
pass(tail, SSA) ->
    mmb_ssa_tail:convert(SSA);
pass(licm, SSA) ->
    mmb_ssa_licm:convert(SSA);
pass(inlineonce, SSA) ->
    mmb_ssa_inlineonce:convert(SSA);
pass(inlinesmall, SSA) ->
    mmb_ssa_inlinesmall:convert(SSA, 10);
pass(elimarg, SSA) ->
    mmb_ssa_elimarg:convert(SSA);
pass(elimsingle, SSA) ->
    mmb_ssa_elimsingle:convert(SSA);
pass(elimempty, SSA) ->
    mmb_ssa_elimempty:convert(SSA);
pass(elimphi, SSA) ->
    mmb_ssa_elimphi:convert(SSA);
pass(elimvalue, SSA) ->
    mmb_ssa_elimvalue:convert(SSA);
pass(elimref, SSA) ->
    mmb_ssa_elimref:convert(SSA);
pass(vin, SSA) ->
    mmb_ssa_vin:convert(SSA);
pass(vout, SSA) ->
    mmb_ssa_vout:convert(SSA);
pass(global, SSA) ->
    mmb_ssa_global:convert(SSA);
pass(delayglobal, SSA) ->
    mmb_ssa_delayglobal:convert(SSA);
pass(delayclosure, SSA) ->
    mmb_ssa_delayclosure:convert(SSA);
pass(elimfree, SSA) ->
    mmb_ssa_elimfree:convert(SSA);
pass(desfree, SSA) ->
    mmb_ssa_desfree:convert(SSA);
pass(elimtag, SSA) ->
    mmb_ssa_elimtag:convert(SSA);
pass(elimselect, SSA) ->
    mmb_ssa_elimselect:convert(SSA);
pass(escape, SSA) ->
    mmb_ssa_escape:convert(SSA);
pass(tollvm, SSA) ->
    mmb_tollvm:convert(SSA);
pass(llgp, SSA) ->
    mmb_llvm_gp:convert(SSA);
pass(return, SSA) ->
    mmb_llvm_return:convert(SSA);
pass(format, SSA) ->
    mmb_llvm_format:format(SSA);
pass(_, SSA) ->
    SSA.

passes([], SSA) ->
    SSA;
passes([H|T], SSA) ->
    passes(T, pass(H, SSA)).

compile(Bin) ->
    {ok, Tokens} = mmb_lexer:tokens(Bin),
    {ok, Typedefs, Globals} = mmb_parser:parse(Tokens),
    {Count, Fns, Values, TypeMap, Typedefs1} = mmb_scope:resolve(Typedefs, Globals),
    {Root, Fns1} = mmb_flatten:flatten(Count, Fns, Values),
    SSA = mmb_compact:compact(Root, Fns1, TypeMap, Typedefs1),
    passes(
      [
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       select,

       inlineonce,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       inlinesmall,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       elimref, elimphi, elimvalue,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       inlineonce,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       elimarg,

       inlinesmall,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       vin,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       licm,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       vout, elimphi, elimvalue,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       global,
       delayglobal,
       elimfree,
       delayclosure,

       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       desfree,
       delayclosure,

       tail,

       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       elimtag,
       elimvalue,

       elimselect,
       elimvalue,
       gp, elimvalue, cbc, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,
       elimsingle, allphis, elimempty, elimphi, elimvalue,

       tollvm,
       llgp, allphis, elimempty, elimphi, elimvalue,

       return, elimphi, elimvalue,
       format
      ],
      SSA).
