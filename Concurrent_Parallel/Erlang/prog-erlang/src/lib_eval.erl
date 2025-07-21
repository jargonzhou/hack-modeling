%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(lib_eval).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([eval/1]).

%% 表达式字符串求值.
eval(ExprStr) ->
  % happy path
  {ok, Tokens, _} = erl_scan:string(ExprStr),      % 扫描字符串, 输出token
  {ok, Exprs} = erl_parse:parse_exprs(Tokens),      % 解析token, 输出表达式
  Bindings = erl_eval:new_bindings(),          % 定义绑定
  {value, Value, _} = erl_eval:exprs(Exprs, Bindings),  % 表达式求值
  Value.

%% ====================================================================
%% Internal functions
%% ====================================================================


