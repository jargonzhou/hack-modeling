%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% Mnesia示例.
%%% 
%%% 执行:
%%% erlang-playground]$ erl -sname a -pa ebin
%%% > mnesia:create_schema([node()|nodes()]). % 只执行一次, 或者删除目录下Mnesia表
%%% > mnesia:start().
%%% > example_mnesia:start(). 
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(example_mnesia).
-include("common.hrl").
-include("usr.hrl").

-define(TABLE_NAME, usr).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/0]).
-export([create_tables/0]).
-export([add_usr/3,
  delete_usr/1,
  update_status/2,
  lookup_id/1,
  dirty_lookup_id/1]).

start() ->
  create_tables(),

  add_usr(700000003, 3, prepay),
  ?INFO("id is 3", lookup_id(3)),
  update_status(3, disabled),
  ?INFO("id is 3", lookup_id(3)),

  ?INFO("id is 3[dirty read]", dirty_lookup_id(3)),

  delete_usr(3),
  ?INFO("id is 3", lookup_id(3)),
  ok.


%%% 创建表
create_tables() ->
  mnesia:create_table(?TABLE_NAME,
    [{disc_copies, [node()]},
      {ram_copies, nodes()},
      {type, set},                    % 表类型
      {attributes, record_info(fields, ?TABLE_NAME)},  % 表字段
      {index, [id]}                    % 索引
    ]),
  ok = mnesia:wait_for_tables([?TABLE_NAME], 6000). % 等待表可访问


%%% 添加用户
add_usr(PhoneNo, CustId, Plan) when Plan == prepay; Plan == postpay ->
  Usr = #usr{msisdn = PhoneNo, id = CustId, plan = Plan},
  Fun = fun() -> mnesia:write(Usr) end,
  {atomic, Res} = mnesia:transaction(Fun), % 事务中
  Res.

%%% 按id删除用户
delete_usr(CustId) ->
  Fun = fun() ->
    case mnesia:index_read(?TABLE_NAME, CustId, id) of
      [] ->
        {error, none};
      [Usr] ->
        mnesia:delete({?TABLE_NAME, Usr#usr.msisdn})
    end
        end,
  {atomic, Res} = mnesia:transaction(Fun), % 事务中
  Res.

%%% 更新状态(status)
update_status(CustId, Status) when Status == enabled; Status == disabled ->
  Fun = fun() ->
    case mnesia:index_read(?TABLE_NAME, CustId, id) of
      [] ->
        {error, none};
      [Usr] ->
        mnesia:write(Usr#usr{status = Status})
    end
        end,
  {atomic, Res} = mnesia:transaction(Fun), % 事务中
  Res.

%%% 按id查找
lookup_id(CustId) ->
  Fun = fun() ->
    case mnesia:index_read(?TABLE_NAME, CustId, id) of
      [] -> {error, none};
      [Usr] -> Usr
    end
        end,
  {atomic, Res} = mnesia:transaction(Fun), % 事务中
  Res.


%%% 脏读操作: 按id查找
dirty_lookup_id(CustId) ->
  case mnesia:dirty_index_read(?TABLE_NAME, CustId, id) of
    [Usr] -> {ok, Usr};
    [] -> {error, none}
  end.


%% ====================================================================
%% Internal functions
%% ====================================================================


