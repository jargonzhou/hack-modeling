%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(test_list).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
  test_sum(),
  test_map(),
  test_list_comprehension(),
  test_quick_sort(),
  test_pythag(),
  test_filter()
.


%% ====================================================================
%% Internal functions
%% ====================================================================

%% 计算列表中元素和
sum([H | T]) -> H + sum(T);
sum([]) -> 0.

test_sum() -> sum([1, 2, 3]).

%% 对列表中每个元素执行F, 生成结果列表
map(_, []) -> [];
map(F, [H | T]) -> [F(H) | map(F, T)].

map2(F, L) -> [F(X) || X <- L]. % 使用列表推导

test_map() ->
  L = map(fun(X) -> X * X end, [1, 2, 3]),
  io:format("L=~p~n", [L]),
  L = map2(fun(X) -> X * X end, [1, 2, 3]),
  io:format("L=~p~n", [L]).

%% 列表推导示例
list_comprehension() ->
  L = [2 * X || X <- [1, 2, 3]],
  io:format("L=~p~n", [L]),

  Buy = [{orange, 4}, {newspaper, 1}, {apples, 10}, {pears, 6}, {milk, 3}],
  L2 = [{Name, 2 * Number} || {Name, Number} <- Buy],
  io:format("L2=~p~n", [L2])
.

test_list_comprehension() -> list_comprehension().

%% 快速排序
quick_sort([]) -> [];
quick_sort([Pivot | T]) ->
  quick_sort([X || X <- T, X < Pivot])
  ++ [Pivot] ++
    quick_sort([X || X <- T, X >= Pivot]).

test_quick_sort() ->
  L1 = [23, 6, 2, 9, 27, 400, 78, 45, 61, 82, 14],
  L2 = quick_sort(L1),
  io:format("L1=~p,~nL2=~p~n", [L1, L2]).

%% 毕达哥拉斯三元数组: N=A+B+C, A^2+B^2=C^2.
pythag(N) ->
  [
    {A, B, C} ||
    A <- lists:seq(1, N), % 生成列表[1,2,...,N]
    B <- lists:seq(1, N),
    C <- lists:seq(1, N),
    A + B + C =< N,
    A * A + B * B =:= C * C
  ].

test_pythag() ->
  L = pythag(16),
  io:format("L=~p~n", [L]).

%% 列表过滤
filter(Pred, [H | T]) ->
  case Pred(H) of % 使用case表达式
    true -> [H | filter(Pred, T)];
    false -> filter(Pred, T)
  end;
filter(_Pred, []) -> [].

test_filter() ->
  Even = fun(X) -> (X rem 2) =:= 0 end,
  L = filter(Even, [1, 2, 3, 4, 5, 6, 8]),
  io:format("L=~p~n", [L]).

