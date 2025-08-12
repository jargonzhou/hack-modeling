%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_macro).

%% ====================================================================
%% API functions
%% ====================================================================
-export([foo/1, loop/1]).
%%-compile(export_all).

% usage: c(test_macro, {d, debug_flag}).
-ifdef(debug_flag).
-define(DEBUG(X), io:format("DEBUG ~p:~p ~p~n", [?MODULE, ?LINE, X])).
-else.
-define(DEBUG(X), void).
-endif.

-define(MAX_CONNECTION, 10).
-define(macro1(X, Y), {ok, X, Y}).


%% ====================================================================
%% Internal functions
%% ====================================================================

foo(A) ->
  X = ?macro1(A + 10, b),
  io:format("X=~p~n", [X])
.

loop(0) -> done;
loop(N) ->
  ?DEBUG(N),
  loop(N - 1).
