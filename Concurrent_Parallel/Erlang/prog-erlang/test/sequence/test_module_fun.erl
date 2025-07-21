%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(test_module_fun).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).
%%-compile(export_all).

run() ->
  test_area(),
  test_total_price(),
  fun_data_type(),
  fun_as_parameter(),
  fun_as_return_value(),
  fun_as_control_abstraction(),
  test_max(),
  if_expression(),
  test_odds_and_evens()
.

%% ====================================================================
%% Internal functions
%% ====================================================================

%% 计算面积
area({rectangle, Width, Height}) -> Width * Height;
area({square, Side}) -> Side * Side;
area({circle, Radius}) -> 3.14159 * Radius * Radius.


test_area() ->
  A = area({rectangle, 10, 2}),
  B = area({square, 4}),
  C = area({circle, 10}),
  io:format("A=~p, B=~p, C=~p~n", [A, B, C]).

%% 获取价格
cost(oranges) -> 5;
cost(newspaper) -> 8;
cost(apples) -> 2;
cost(pears) -> 9;
cost(milk) -> 7.

%% 计算总价格
total_price([{What, N} | T]) -> cost(What) * N + total_price(T);
total_price([]) -> 0.

test_total_price() ->
  Buy = [{oranges, 4}, {newspaper, 1}, {apples, 10}, {pears, 6}, {milk, 3}],
  TotalPrice = total_price(Buy),
  io:format("TotalPrice=~p~n", [TotalPrice]).

%% fun作为一种函数数据类型
fun_data_type() ->
  % 匿名函数
  Double = fun(X) -> 2 * X end,
  A = Double(2),
  io:format("A=~p~n", [A]),

  % 计算直角三角形的斜边
  Hypot = fun(X, Y) -> math:sqrt(X * X + Y * Y) end,
  B = Hypot(3, 4),
  io:format("B=~p~n", [B]),

  % fun可以有多个子句
  % 华氏与摄氏温度的转换函数
  TempConvert = fun({c, C}) -> {f, 32 + C * 9 / 5};
    ({f, F}) -> {c, (F - 32) * 5 / 9}
                end,
  FValue = TempConvert({c, 100}),
  CValue = TempConvert({f, 212}),
  io:format("FValue=~p, CValue=~p~n", [FValue, CValue])
.

%% fun作为一种函数的参数
fun_as_parameter() ->
  % 以lists:map/2, lists:filter/2为例
  L = [1, 2, 3, 4],
  L2 = lists:map(fun(X) -> 2 * X end, L),
  io:format("L2=~p~n", [L2]),

  Even = fun(X) -> (X rem 2) =:= 0 end,
  io:format("Even(8)=~p, Even(7)=~p~n", [Even(8), Even(7)]),
  L3 = lists:map(Even, [1, 2, 3, 4, 5, 6, 8]),
  L4 = lists:filter(Even, [1, 2, 3, 4, 5, 6, 8]),
  io:format("L3=~p, L4=~p~n", [L3, L4])
.

%% fun作为函数的返回值
fun_as_return_value() ->
  Fruit = [apple, pear, orange],
  MakeTest = fun(L) ->
    (fun(X) -> lists:member(X, L) end)
             end,
  IsFruit = MakeTest(Fruit),
  io:format("IsFruit(pear)=~p, IsFruit(dog)=~p~n", [IsFruit(pear), IsFruit(dog)])
.

%% fun作为控制抽象
fun_as_control_abstraction() ->
  A = lib_misc:for(1, 10, fun(X) -> X * X end),
  io:format("A=~p~n", [A])
.

test_max() ->
  X = 13, Y = 23,
  A = module_fun:max(X, Y),
  io:format("A=~p~n", [A]).


%% if表达式示例
if_expression() ->
  X = (fun(X) -> X * X end)(13),
  A = if
        X rem 3 =:= 0 -> 10;
        true -> 30
      end,
  io:format("A=~p~n", [A]).


%% 累加器(accumulator)示例: 分割列表中奇数(Odds)和偶数(Evens)
odds_and_evens(L) -> odds_and_evens_(L, [], []).
odds_and_evens_([H | T], Odds, Evens) ->
  case (H rem 2) of
    1 -> odds_and_evens_(T, [H | Odds], Evens);
    0 -> odds_and_evens_(T, Odds, [H | Evens])
  end;
odds_and_evens_([], Odds, Evens) -> {Odds, Evens}.

test_odds_and_evens() ->
  L = [1, 2, 3, 4, 5, 6, 7, 8, 9],
  R = module_fun:odds_and_evens(L),
  io:format("R=~p~n", [R]).

%% 函数引用
square(X) -> X * X.
double(L) -> lists:map(fun square/1, L).

test_double() ->
  double([1, 2, 3]).

