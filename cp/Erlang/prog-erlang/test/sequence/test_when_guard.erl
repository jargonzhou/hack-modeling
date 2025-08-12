%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_when_guard).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
  ?INFO("max(2, 3)", mymax(2, 3)),
  test_andalso(),
  test_and().


%% ====================================================================
%% Internal functions
%% ====================================================================

mymax(X, Y) when X > Y -> X;
mymax(_X, Y) -> Y.


test_andalso() ->
  A = 1,
  Bool = A < 0 andalso begin
                         io:format("a~n", []),
                         A < 2
                       end,
  ?INFO("Bool", Bool).

test_and() ->
  A = 1,
  Bool = (A < 0) and begin
                       io:format("a~n", []),
                       A < 2
                     end,
  ?INFO("Bool", Bool).

