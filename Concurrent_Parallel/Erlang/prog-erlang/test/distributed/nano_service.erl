%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(nano_service).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_nano_server/1,
  nano_client_eval/2]).

% Server
start_nano_server(Port) ->
  {ok, Listen} = gen_tcp:listen(Port, [binary,
    {packet, 4},
    {reuseaddr, true},
    {active, true}]),
  {ok, Socket} = gen_tcp:accept(Listen), % blocking
  gen_tcp:close(Listen), % close listening
  loop(Socket).

% Client
nano_client_eval(Port, Str) ->
  {ok, Socket} = gen_tcp:connect("localhost", Port, [binary,
    {packet, 4}]),
  ok = gen_tcp:send(Socket, term_to_binary(Str)),
  receive
    {tcp, Socket, Bin} ->
      io:format("Client receive binary=~p~n", [Bin]),
      Value = binary_to_term(Bin),
      io:format("Client result=~p~n", [Value]),
      gen_tcp:close(Socket)
  end.

%% ====================================================================
%% Internal functions
%% ====================================================================

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

