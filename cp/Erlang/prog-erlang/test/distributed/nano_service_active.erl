%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(nano_service_active).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_nano_server1/1,
  start_nano_server2/1,
  start_nano_server3/1]).

start_nano_server1(Port) ->
  {ok, Listen} = gen_tcp:listen(Port, [binary,
    {packet, 4},
    {reuseaddr, true},
    {active, true}]), % true
  {ok, Socket} = gen_tcp:accept(Listen), % blocking
  loop_active_true(Socket).

start_nano_server2(Port) ->
  {ok, Listen} = gen_tcp:listen(Port, [binary,
    {packet, 4},
    {reuseaddr, true},
    {active, false}]), % false
  {ok, Socket} = gen_tcp:accept(Listen), % blocking
  loop_active_false(Socket).


start_nano_server3(Port) ->
  {ok, Listen} = gen_tcp:listen(Port, [binary,
    {packet, 4},
    {reuseaddr, true},
    {active, once}]), % once
  {ok, Socket} = gen_tcp:accept(Listen), % blocking
  loop_active_once(Socket).

%% ====================================================================
%% Internal functions
%% ====================================================================

loop_active_true(Socket) ->
  receive
    {tcp, Socket, Bin} ->
      ?INFO("Server received binary", Bin),
      Str = binary_to_term(Bin),
      ?INFO("Server unpacked received binary", Str),
      Reply = lib_eval:eval(Str),
      ?INFO("Server reply", Reply),
      gen_tcp:send(Socket, term_to_binary(Reply)),
      loop_active_true(Socket);
    {tcp_closed, Socket} ->
      ?INFO("Server socket closed")
  end.

loop_active_false(Socket) ->
  case gen_tcp:recv(Socket, 0) of % 0 means all available bytes
    {ok, Bin} ->
      io:format("Server received binary=~p~n", [Bin]),
      Str = binary_to_term(Bin),
      io:format("Server unpacked received binary=~p~n", [Str]),
      Reply = lib_eval:eval(Str),
      io:format("Server reply=~p~n", [Reply]),
      gen_tcp:send(Socket, term_to_binary(Reply)),
      loop_active_false(Socket);
    {error, closed} ->
      io:format("Server socket closed~n")
  end.

loop_active_once(Socket) ->
  receive
    {tcp, Socket, Bin} ->
      io:format("Server received binary=~p~n", [Bin]),
      Str = binary_to_term(Bin),
      io:format("Server unpacked received binary=~p~n", [Str]),
      Reply = lib_eval:eval(Str),
      io:format("Server reply=~p~n", [Reply]),
      gen_tcp:send(Socket, term_to_binary(Reply)),
      inet:setopts(Socket, [{active, once}]),
      loop_active_once(Socket);
    {tcp_closed, Socket} ->
      io:format("Server socket closed~n")
  end.