%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(test_error_handling).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
  test_try_catch_demo(),
  test_catch_demo(),
  test_stacktrace_demo()
.

%% ====================================================================
%% Internal functions
%% ====================================================================

% 使用try-catch
test_try_catch_demo() ->
  [catch_exception(I) || I <- lists:seq(1, 5)].

% 使用catch
test_catch_demo() ->
  [{I, catch generate_exception(I)} || I <- lists:seq(1, 5)].

% 获取错误栈
test_stacktrace_demo() ->
  try generate_exception(5)
  catch
    % Class:Reason:Stacktrace
    error:X:Stacktrace -> {X, Stacktrace}
  end.


% 生成异常
generate_exception(1) -> a;
generate_exception(2) -> throw(a);
generate_exception(3) -> exit(a);
generate_exception(4) -> {'EXIT', a};
generate_exception(5) -> error(a).

% 捕获异常
catch_exception(N) ->
  try generate_exception(N) of
    Val -> {N, normal, Val}
  catch
    throw:X -> {N, caught, throw, X};
    exit:X -> {N, caught, exit, X};
    error:X -> {N, caught, error, X}
  end.