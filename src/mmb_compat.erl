%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_compat).

-export(
   [
    parse_float/1,
    parse_float/2,
    print/1,
    encode_float/1
]).

parse_float(N) ->
    binary_to_float(<<N/binary, ".0">>).

parse_float(N, M) ->
    binary_to_float(<<N/binary, ".", M/binary>>).

print(Bin) ->
    io:format("~ts~n", [Bin]).

encode_float(X) ->
    [<<"0x">>, binary:encode_hex(<<X/float>>)].
