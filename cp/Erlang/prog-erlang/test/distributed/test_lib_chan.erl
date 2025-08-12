%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_lib_chan).

%% ====================================================================
%% API functions
%% ====================================================================
%-compile(export_all).
-export([test_start_server/0, test_start_client/0]).

%% ====================================================================
%% Internal functions
%% ====================================================================

test_start_server() ->
  lib_chan:start_server("conf/lib_chan.conf").

test_start_client() ->
  {ok, S} = lib_chan:connect("localhost", 2233, math, "qwerty", {yes, go}),
  Res1 = lib_chan:rpc(S, {factorial, 20}),
  io:format("Res1=~p~n", [Res1]),
  Res2 = lib_chan:rpc(S, {fibonacci, 15}),
  io:format("Res2=~p~n", [Res2]),
  lib_chan:disconnect(S),
  ok.
