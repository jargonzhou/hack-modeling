%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(example_ets_record).
-include("common.hrl").
% 引入fun语法到匹配规范的转换功能
-include_lib("stdlib/include/ms_transform.hrl").

% 记录定义
-record(capital, {
  name,
  country,
  pop}).

-define(TABLE_NAME, countries).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/0]).

start() ->
  op_with_record_example().

%%% 操作记录(record)
op_with_record_example() ->
  ets:new(?TABLE_NAME,
    [named_table,
      {keypos, #capital.name}]), % 指定记录中字段作为键

  % 插入记录
  ets:insert(?TABLE_NAME,
    #capital{name = "Budapest", country = "Hungary", pop = 2400000}),
  ets:insert(?TABLE_NAME,
    #capital{name = "Pretoria", country = "Sount Africa", pop = 2400000}),
  ets:insert(?TABLE_NAME,
    #capital{name = "Rome", country = "Italy", pop = 5500000}),

  % lookup
  ?INFO("ets:lookup(Pretoria)",
    ets:lookup(?TABLE_NAME, "Pretoria")),

  % match
  ?INFO("match #capital{country=\"Italy\", _='_'}",
    ets:match(?TABLE_NAME, #capital{country = "Italy", _ = '_'})),

  % match_object
  ?INFO("match object #capital{country=\"Italy\", _='_'}",
    ets:match_object(?TABLE_NAME, #capital{country = "Italy", _ = '_'})),

  % select with fun2ms
  MatchSpec = ets:fun2ms(
    fun(#capital{pop = P, name = N}) when P < 5000000 ->
      N
    end),
  ?INFO(MatchSpec),
  ?INFO("select", ets:select(?TABLE_NAME, MatchSpec)).

%% ====================================================================
%% Internal functions
%% ====================================================================


