%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(mod_math).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/3]).
%-compile(export_all).

run(MM, ArgC, ArgS) ->
  io:format("mod_math: run starting, ArgC=~p,ArgS=~p~n", [ArgC, ArgS]),
  loop(MM).

%% ====================================================================
%% Internal functions
%% ====================================================================

loop(MM) ->
  receive
    {chan, MM, {factorial, N}} ->
      MM ! {send, lib_math:fac(N)},
      loop(MM);
    {chan, MM, {fibonacci, N}} ->
      MM ! {send, lib_math:fib(N)},
      loop(MM);
    {chan_closed, MM} ->
      io:format("mod_math stopping~n"),
      exit(normal)
  end.
