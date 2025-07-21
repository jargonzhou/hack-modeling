%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% DETS表示例.
%%% @end
%%%-------------------------------------------------------------------


-module(example_dets).
-include("common.hrl").
-include_lib("stdlib/include/ms_transform.hrl"). % 引入fun语法到匹配规范的转换功能

-define(FILE_NAME, "db/food.dets").
-define(TABLE_NAME, food).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/0]).

start() ->
  init(),
  reopen_ops(),
  ok.

%% ====================================================================
%% Internal functions
%% ====================================================================

init() ->
  % 四种类型的ETS表: set, bag, duplicate_bag.
  dets:open_file(?TABLE_NAME, [{type, bag}, {file, ?FILE_NAME}]),
  % 插入记录
  dets:insert(?TABLE_NAME, {italy, spaghetti}),
  dets:insert(?TABLE_NAME, {italy, pizza}),
  dets:insert(?TABLE_NAME, {sweden, meatballs}),
  dets:insert(?TABLE_NAME, {china, noodle}),

  % 按主键查找
  ?INFO("dets:lookup(china)", dets:lookup(?TABLE_NAME, china)),

  % select匹配规范查找
  MatchSpec = ets:fun2ms(fun({Loc, Food}) when Loc /= italy -> Food end),
  ?INFO("MatchSpec", MatchSpec),
  ?INFO("select by MatchSpec", dets:select(?TABLE_NAME, MatchSpec)),

  % 关闭表
  dets:close(?TABLE_NAME).

%%% 重新打开表
reopen_ops() ->
  % 重新打开表后, 使用表的引用
  {ok, TableRef} = dets:open_file(?FILE_NAME),
  ?INFO("dets:lookup(china)", dets:lookup(TableRef, china)).

