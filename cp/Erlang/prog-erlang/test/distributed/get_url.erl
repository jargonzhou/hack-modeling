%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(get_url).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([nano_get_url/2]).

nano_get_url(Host, Port) ->
  % 建立连接
  {ok, Socket} = gen_tcp:connect(Host, Port, [binary,
    {packet, 0}]),
  % 发送请求
  ok = gen_tcp:send(Socket, "GET / HTTP/1.0\r\n\r\n"),
  % 接收响应
  Bin = receive_data(Socket, []),
  ?INFO("Bin", Bin),
  ?INFO("Data", string:tokens(binary_to_list(Bin), "\r\n")),
  % 关闭连接
  gen_tcp:close(Socket).

%% ====================================================================
%% Internal functions
%% ====================================================================

receive_data(Socket, SoFar) ->
  receive
    {tcp, Socket, Bin} ->
      receive_data(Socket, [Bin | SoFar]);
    {tcp_closed, Socket} ->
      list_to_binary(lists:reverse(SoFar))
  end.
