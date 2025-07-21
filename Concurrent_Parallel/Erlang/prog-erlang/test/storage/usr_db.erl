%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% ETS/DETS的综合使用.
%%% 
%%% 涉及表:
%%% UsrRam: ETS(set), 记录usr记录;
%%% UsrIndex: ETS(set), 记录id-msisdn索引(CustId, PhoneNo);
%%% UsrDisk: DETS(set), UsrRam的镜像.
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(usr_db).
-include("usr.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([create_tables/1,
  close_tables/0,
  restore_backup/0]).
-export([add_usr/1,
  update_usr/1,
  lookup_id/1,
  lookup_msisdn/1]).
-export([delete_disabled/0,
  delete_usr/2]).

%%% 创建表: usrRam, usrIndex, usrDisk
create_tables(FileName) ->
  ets:new(usrRam, [named_table, {keypos, #usr.msisdn}]),
  ets:new(usrIndex, [named_table]),
  dets:open_file(usrDisk, [{file, FileName}, {keypos, #usr.msisdn}]),
  ok.

%%% 关闭表: usrRam, usrIndex, usrDisk
close_tables() ->
  ets:delete(usrRam),
  ets:delete(usrIndex),
  dets:close(usrDisk).

%%% 从usrDisk中恢复usrRam和usrIndex
restore_backup() ->
  Insert =
    fun(#usr{msisdn = PhoneNo, id = CustId} = Usr) ->
      ets:insert(usrRam, Usr),
      ets:insert(usrIndex, {CustId, PhoneNo}),
      continue
    end,
  dets:traverse(usrDisk, Insert).

%%% 添加记录
add_usr(#usr{msisdn = PhoneNo, id = CustId} = Usr) ->
  ets:insert(usrIndex, {CustId, PhoneNo}),
  update_usr(Usr).

%%% 更新记录: usrRam, usrDisk
update_usr(Usr) ->
  ets:insert(usrRam, Usr),
  dets:insert(usrDisk, Usr),
  ok.

%%% 按id查找usrRam
lookup_id(CustId) ->
  case get_index(CustId) of
    {ok, PhoneNo} -> lookup_msisdn(PhoneNo);
    {error, none} -> {error, none}
  end.

%%% 按主键(msisdn)查找usrRam
lookup_msisdn(PhoneNo) ->
  case ets:lookup(usrRam, PhoneNo) of
    [Usr] -> {ok, Usr};
    [] -> {error, none}
  end.

%%% 按主键(id)查找usrIndex
get_index(CustId) ->
  case ets:lookup(usrIndex, CustId) of
    [{CustId, PhoneNo}] -> {ok, PhoneNo};
    [] -> {error, none}
  end.

%%% 删除失效的记录(status=disabled)
delete_disabled() ->
  % 确保只遍历每个元素一次, 不受遍历开始后的破坏性操作的影响
  ets:safe_fixtable(usrRam, true),  % +
  % ets:first/1返回主键或者'$end_of_table'
  catch loop_delete_disabled(ets:first(usrRam)),
  ets:safe_fixtable(usrRam, false),  % -
  ok.

loop_delete_disabled('$end_of_table') -> ok;
loop_delete_disabled(PhoneNo) ->
  case ets:lookup(usrRam, PhoneNo) of
    [#usr{status = disabled, id = CustId}] -> delete_usr(PhoneNo, CustId);
    _ -> ok
  end,
  loop_delete_disabled(ets:next(usrRam, PhoneNo)).

%%% 删除用户
delete_usr(PhoneNo, CustId) ->
  ets:delete(usrIndex, CustId),
  dets:delete(usrDisk, PhoneNo),
  ets:delete(usrRam, PhoneNo),
  ok.


%% ====================================================================
%% Internal functions
%% ====================================================================


