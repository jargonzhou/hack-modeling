%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% hlr: Home Location Register.
%%% @end
%%%-------------------------------------------------------------------

-module(hlr).
-define(PHONE_2_PID, phone2pid).
-define(PID_2_PHONE, pid2phone).

%% ====================================================================
%% API functions
%% ====================================================================
-export([new/0,
		 destroy/0,
		 attach/1,
		 detach/0,
		 lookup_id/1,
		 lookup_ms/1]).

new() ->
	ets:new(?PHONE_2_PID, [public, named_table]),
	ets:new(?PID_2_PHONE, [public, named_table]),
	ok.

destroy() ->
	ets:delete(?PHONE_2_PID),
	ets:delete(?PID_2_PHONE),
	ok.
	

%% 添加手机号.
attach(Phone) ->
	ets:insert(?PHONE_2_PID, {Phone, self()}),
	ets:insert(?PID_2_PHONE, {self(), Phone}).

%% 移除当前Pid关联的手机号.
detach() ->
	case ets:lookup(?PID_2_PHONE, self()) of
		[{Pid, Phone}] ->
			ets:delete(?PID_2_PHONE, Pid),
			ets:delete(?PHONE_2_PID, Phone);
		[] ->
			ok
	end.

%% 按手机号查找.
lookup_id(Phone) ->
	case ets:lookup(?PHONE_2_PID, Phone) of
		[] -> {error, invalid};
		[{Phone, Pid}] -> {ok, Pid}
	end.

%% 按Pid查找.
lookup_ms(Pid) ->
	case ets:lookup(?PID_2_PHONE, Pid) of
		[] -> {error, invalid};
		[{Pid, Phone}] -> {ok, Phone}
	end.

%% ====================================================================
%% Internal functions
%% ====================================================================


