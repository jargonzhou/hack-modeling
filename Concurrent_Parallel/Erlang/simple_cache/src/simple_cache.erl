%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 缓存的API.
%%% @end
%%%-------------------------------------------------------------------


-module(simple_cache).

%% ====================================================================
%% API functions
%% ====================================================================
-export([insert/2, lookup/1, delete/1]).

insert(Key, Value) ->
	%  查找缓存键对应的值进程Pid
	case sc_store:lookup(Key) of
		{ok, Pid} 	-> 									% 缓存键已存在, 则替换值
			sc_element:replace(Pid, Value),
			sc_event:replace(Key, Value);% logging
		{error, _} 	-> 									% 缓存键不存在
			{ok, Pid} = sc_element:create(Value), 			% 创建缓存值进程
			sc_store:insert(Key, Pid),						% 生成Key-Pid记录
			sc_event:create(Key, Value) % logging
	end.

lookup(Key) ->
	sc_event:lookup(Key), 				% logging

	try
		{ok, Pid} = sc_store:lookup(Key),
		{ok, Value} = sc_element:fetch(Pid),
		{ok, Value}
	catch
		_:_ -> {error, not_found}
	end.

delete(Key) ->
	sc_event:delete(Key), 				% logging
	case sc_store:lookup(Key) of
		{ok, Pid} 	-> sc_element:delete(Pid); % sc_store中Key-Pid记录在sc_element:terminate/2中移除
		{error, _} -> ok
	end.


%% ====================================================================
%% Internal functions
%% ====================================================================


