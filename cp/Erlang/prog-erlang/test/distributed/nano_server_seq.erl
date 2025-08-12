%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(nano_server_seq).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_nano_server/1]).

%% 顺序服务器
start_nano_server(Port) ->
  {ok, Listen} = gen_tcp:listen(Port, [binary,
    {packet, 4},
    {reuseaddr, true},
    {active, true}]),
  loop_listen(Listen).

%% ====================================================================
%% Internal functions
%% ====================================================================

loop_listen(Listen) ->
  {ok, Socket} = gen_tcp:accept(Listen), % blocking
  loop(Socket),
  loop_listen(Listen). % tail call

loop(Socket) ->
  receive
    {tcp, Socket, Bin} ->
      io:format("Server received binary=~p~n", [Bin]),
      Str = binary_to_term(Bin),
      io:format("Server unpacked received binary=~p~n", [Str]),
      Reply = lib_eval:eval(Str),
      io:format("Server reply=~p~n", [Reply]),
      gen_tcp:send(Socket, term_to_binary(Reply)),
      loop(Socket);
    {tcp_closed, Socket} ->
      io:format("Server socket closed~n")
  end.

