%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(test_introduction).

-export([simple_arith/0,
  float_value/0,
  atom_value/0,
  tuple_value/0,
  list_value/0,
  string_value/0,
  pattern_match/0,
  start/1,
  file_server_loop/1,
  ls/1,
  get_file/2]).
%%-compile(export_all).

%% 简单的整数运算
simple_arith() ->
  % 变量首字母大写
  X = 2 + 3 * 4,
  io:format("~w~n", [X]).

%% 浮点数
float_value() ->
  A = 5 / 3,
  B = 4 / 2,
  C = 5 div 3, % 取整
  D = 5 rem 3, % 余数
  io:format("A=~w, B=~w, C=~w, D=~w~n", [A, B, C, D]).

%% 原子
%% (1) 小写字母开头, 后接字母/数字/_/@;
%% (2) 单引号内, 'a'与a相同 
atom_value() ->
  A = red,
  B = 'what is red',
  io:format("A=~w, B=~w~n", [A, B]).

%% 元组
tuple_value() ->
  Person = {person, {name, joe}, {height, 1.82},
    {footsize, 42}, {eyecolour, brown}},
  io:format("~p~n", [Person]),

  % 元组嵌套
  F = {firstName, joe},
  L = {lastName, armstrong},
  P = {person, F, L},
  io:format("~p~n", [P]),

  % 提取元组的值
  Point = {point, 10, 45},
  {point, A, B} = Point,
  io:format("A=~w, B=~w~n", [A, B]),

  % 使用匿名变量(_)
  {_, {_, FirstName}, {_, LastName}} = P,
  io:format("FirstName=~w, LastName=~w~n", [FirstName, LastName])
.

%% 列表
list_value() ->
  Drawing = [{square, {10, 10}, 10}, {triangle, {15, 10}, {25, 10}, {30, 40}}],
  io:format("~p~n", [Drawing]),

  % 列表中各元素可以是任何类型
  A = [1 + 7, hello, 2 - 2, {cost, apple, 30 - 20}, 3],
  io:format("~p~n", [A]),


  % 定义列表: [H|T], [...|T]
  ThingsToBuy = [{apples, 10}, {pears, 6}, {milk, 3}],
  ThingsToBuy1 = [{oranges, 4}, {newspaper, 1} | ThingsToBuy],
  io:format("ThingsToBuy1=~p~n", [ThingsToBuy1]),

  % 提取列表元素
  [Buy1 | ThingsToBuy2] = ThingsToBuy1,
  io:format("Buy1=~p, ThingsToBuy2=~p ~n", [Buy1, ThingsToBuy2]),

  [Buy2, Buy3 | ThingsToBuy3] = ThingsToBuy2,
  io:format("Buy2=~p, Buy3=~p, ThingsToBuy3=~p ~n", [Buy2, Buy3, ThingsToBuy3])
.

%% 字符串: 使用"", 整数列表, 二进制型.
string_value() ->
  A = "hello",
  B = [$h, $e, $l, $l, $o],
  io:format("A=~p, A=~w~n", [A, A]),
  io:format("B=~p, B=~w~n", [B, B])
.

%% 模式匹配示例
pattern_match() ->
  {A, abc} = {123, abc},
  {B, C, D} = {222, def, "cat"},
  io:format("A=~p, B=~p, C=~p, D=~p~n", [A, B, C, D])
.

%% 简单的文件服务器
% server side
start(Dir) -> spawn(test_introduction, file_server_loop, [Dir]).

file_server_loop(Dir) ->
  receive
    {Client, list_dir} ->
      Client ! {self(), file:list_dir(Dir)};
    {Client, {get_file, File}} ->
      Full = filename:join(Dir, File),
      Client ! {self(), file:read_file(Full)}
  end,
  file_server_loop(Dir).

% client side
ls(Server) ->
  Server ! {self(), list_dir},
  receive
    {Server, FileList} -> FileList
  end.

get_file(Server, File) ->
  Server ! {self(), {get_file, File}},
  receive
    {Server, Content} -> Content
  end.
