%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(fac_service_udp).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_server/1,
  client/3,
  client_with_ref/3]).
% Server
start_server(Port) ->
  spawn(fun() -> server(Port) end).

% Client
client(Host, Port, N) ->
  {ok, Socket} = gen_udp:open(0, [binary]),
  io:format("Client opened socket=~p~n", [Socket]),
  ok = gen_udp:send(Socket, Host, Port, term_to_binary(N)),
  io:format("Client send: ~p~n", [N]),
  Value = receive
            {udp, Socket, _, _, Bin} = Msg ->
              Fac = binary_to_term(Bin),
              io:format("Client received:~p[~p]~n", [Msg, Fac]),
              Fac
          after 2000 -> % timeout
      0
          end,
  gen_udp:close(Socket),
  Value.

client_with_ref(Host, Port, N) ->
  {ok, Socket} = gen_udp:open(0, [binary]),
  Ref = make_ref(),
  io:format("Client opened socket=~p~n", [Socket]),
  Request = term_to_binary({Ref, N}),
  ok = gen_udp:send(Socket, Host, Port, Request),
  io:format("Client send: ~p~n", [{Ref, N}]),
  wait_for_ref(Socket, Ref).

%% ====================================================================
%% Internal functions
%% ====================================================================

server(Port) ->
  {ok, Socket} = gen_udp:open(Port, [binary]),
  io:format("Server open socket:~p~n", [Socket]),
  loop(Socket).

loop(Socket) ->
  receive
    {udp, Socket, Host, Port, Bin} = Msg ->
      Term = binary_to_term(Bin),
      case Term of
        {Ref, N} ->
          io:format("Server received:~p[~p]~n", [Msg, N]),
          Fac = lib_math:fac(N),
          gen_udp:send(Socket, Host, Port, term_to_binary({Ref, Fac})),
          io:format("Server responsed:~p~n", [{Ref, Fac}]),
          loop(Socket);
        N when is_integer(N) ->
          io:format("Server received:~p[~p]~n", [Msg, N]),
          Fac = lib_math:fac(N),
          gen_udp:send(Socket, Host, Port, term_to_binary(Fac)),
          io:format("Server responsed:~p~n", [Fac]),
          loop(Socket)
      end
  end.


wait_for_ref(Socket, Ref) ->
  Value = receive
            {udp, Socket, _, _, Bin} = Msg ->
              io:format("Client received:~p~n", [Msg]),
              case binary_to_term(Bin) of
                {Ref, Val} -> Val;
                {_Ref, _} -> wait_for_ref(Socket, Ref)
              end
          after 2000 -> % timeout
      0
          end,
  gen_udp:close(Socket),
  Value.