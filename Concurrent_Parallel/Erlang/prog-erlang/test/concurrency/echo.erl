%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% Echo Server
%%% @end
%%%-------------------------------------------------------------------


-module(echo).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/0, loop/0]).

start() ->
  register(echo, spawn(echo, loop, [])),
  echo ! {self(), hello},
  receive
    {_Pid, Message} ->
      ?INFO("Message", Message)
  end.

% 消息格式: {发送方Pid, 消息}
loop() ->
  receive
    {From, Message} ->
      From ! {self(), Message},
      loop();
    stop -> true
  end.

%% ====================================================================
%% Internal functions
%% ====================================================================

