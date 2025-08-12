%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 键-Pid(sc_element生成的进程, 内存储值)的存储.
%%% @end
%%%-------------------------------------------------------------------


-module(sc_store).

%% ====================================================================
%% API functions
%% ====================================================================
-export([init/0, insert/2, lookup/1, delete/1]).

-define(TABLE_ID, ?MODULE). % ETS表名

%% 初始化
init() ->
	ets:new(?TABLE_ID, [public, named_table]),
	ok.

%% 插入
insert(Key, Pid) ->
	ets:insert(?TABLE_ID, {Key, Pid}).

%% 按缓存键查找, 返回sc_element的Pid
lookup(Key) ->
	case ets:lookup(?TABLE_ID, Key) of
		[{Key, Pid}] 	-> {ok, Pid};
		[]				-> {error, not_found}
	end.

%% 按Pid移除
delete(Pid) ->
	ets:match_delete(?TABLE_ID, {'_', Pid}).

%% ====================================================================
%% Internal functions
%% ====================================================================

