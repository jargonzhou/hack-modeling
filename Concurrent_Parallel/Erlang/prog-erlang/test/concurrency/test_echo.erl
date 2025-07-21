%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(test_echo).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
  echo:start(),
  EchoPid = whereis(echo),
  ?INFO("echo Pid", EchoPid),
  echo ! {self(), "hello, there"},
  receive
    {Pid, Message} -> ?INFO("Message from Pid", {Message, Pid})
  end,
  echo ! stop,
  ?INFO("echo Pid", whereis(echo)).

%% ====================================================================
%% Internal functions
%% ====================================================================

