%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% ETS示例.
%%% @end
%%%-------------------------------------------------------------------


-module(example_ets).
-include("common.hrl").

% 引入fun语法到匹配规范的转换功能
-include_lib("stdlib/include/ms_transform.hrl").

-define(TABLE_NAME, countries).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/0]).

start() ->
  init(),
  match_example(),
  select_example(),
  fun_to_ms_transform_example(),
  ok.

%% ====================================================================
%% Internal functions
%% ====================================================================

init() ->
  % 创建表
  % 四种类型的ETS表: set, ordered_set, bag, duplicate_bag.
  ets:new(?TABLE_NAME, [bag, named_table]),

  % 插入记录
  % {name, country, job}, 默认元组第一个字段为主键
  ets:insert(?TABLE_NAME, {yves, france, cook}),
  ets:insert(?TABLE_NAME, {sean, ireland, bartender}),
  ets:insert(?TABLE_NAME, {marco, italy, cook}),
  ets:insert(?TABLE_NAME, {chris, ireland, tester}),

  ?INFO("all", ets:tab2list(?TABLE_NAME)),
  % lookup, 按主键查找
  ?INFO("lookup(yves)", ets:lookup(?TABLE_NAME, yves)).

%%% match, match_object
match_example() ->
  ?INFO("match {'$1', ireland, '_'}", ets:match(?TABLE_NAME, {'$1', ireland, '_'})),
  ?INFO("match {'$1', '$0', cook}", ets:match(?TABLE_NAME, {'$1', '$0', cook})),
  ?INFO("match {'$2',ireland,'_'}", ets:match(?TABLE_NAME, {'$2', ireland, '_'})),
  ?INFO("match {'_',ireland,'_'}", ets:match(?TABLE_NAME, {'_', ireland, '_'})),
  ?INFO("match {'$2',cook,'_'}", ets:match(?TABLE_NAME, {'$2', cook, '_'})),
  ?INFO("match {'$0','$1',cook}", ets:match(?TABLE_NAME, {'$0', '$1', cook})),
  ?INFO("match {'$0','$0',cook}", ets:match(?TABLE_NAME, {'$0', '$0', cook})),

  % 返回整个元组
  ?INFO("match object {'_',ireland,'_'}", ets:match_object(?TABLE_NAME, {'_', ireland, '_'})),

  % 匹配删除
  ?INFO("match {'_',ireland,'_'}", ets:match(?TABLE_NAME, {'_', ireland, '_'})),
  ets:match_delete(?TABLE_NAME, {'_', ireland, '_'}),
  ?INFO("match {'_',ireland,'_'}", ets:match(?TABLE_NAME, {'_', ireland, '_'})).

%%% select
select_example() ->
  MatchSpec = [{
    {'$1', '$2', '$3'},    % 与ets:match中一致的模式
    [{'/=', '$3', cook1}],  % 护卫表达式
    [['$2', '$1']]      % 返回表达式
  }],
  ?INFO(MatchSpec),
  ?INFO("match", ets:match(?TABLE_NAME, {'$1', '$2', '$3'})),
  ?INFO("select", ets:select(?TABLE_NAME, MatchSpec)).

%%% fun2ms: function to match specification
fun_to_ms_transform_example() ->
  % fun语法转换为匹配规范
  MatchSpec = ets:fun2ms(
    fun({Name, Country, Job}) when Job /= cook ->
      [Country, Name]
    end),
  ?INFO(MatchSpec),
  ?INFO("select", ets:select(?TABLE_NAME, MatchSpec)).





