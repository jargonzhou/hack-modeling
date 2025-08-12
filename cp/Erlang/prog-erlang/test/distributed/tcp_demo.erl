%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% TCP通信示例: 包括服务器和客户端
%%% 端口1234, 数据格式100字节的二进制数据包.
%%% @end
%%%-------------------------------------------------------------------


-module(tcp_demo).

%% ====================================================================
%% API functions
%% ====================================================================
-export([client/2, server/0, wait_connect/2]).

client(Host, Data) ->
  % 连接
  {ok, Socket} = gen_tcp:connect(Host, 1234, [binary, {packet, 0}]),
  % 发送数据
  send(Socket, Data),
  ok = gen_tcp:close(Socket).

server() ->
  % 被动接收模式
  {ok, ListenSocket} = gen_tcp:listen(1234, [binary, {active, false}]),
  % 等待连接
  wait_connect(ListenSocket, 0).

wait_connect(ListenSocket, Count) ->
  % 成为控制进程
  {ok, Socket} = gen_tcp:accept(ListenSocket),
  % 生成新的监听进程
  spawn(?MODULE, wait_connect, [ListenSocket, Count + 1]),
  get_request(Socket, [], Count).

%% ====================================================================
%% Internal functions
%% ====================================================================

%% client
% 以100字节数据块发送数据
send(Socket, <<Chunk:100/binary, Rest/binary>>) ->
  gen_tcp:send(Socket, Chunk),
  send(Socket, Rest);
send(Socket, Rest) ->
  gen_tcp:send(Socket, Rest).

%% server
% 获取客户端请求数据
get_request(Socket, BinaryList, Count) ->
  case gen_tcp:recv(Socket, 0, 5000) of
    {ok, Binary} ->
      get_request(Socket, [Binary | BinaryList], Count);
    {error, closed} ->
      io:format("handle request data...~n"),
      handle(lists:reverse(BinaryList), Count)
  end.

% 处理客户端数据: 记录入文件中
handle(Binary, Count) ->
  {ok, Fd} = file:open(
    "log_file" ++ integer_to_list(Count), write),
  io:format("write to file[~p]~n", [Fd]),
  file:write(Fd, Binary),
  file:close(Fd).