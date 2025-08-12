%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 简单缓存应用.
%%% @end
%%%-------------------------------------------------------------------


-module(sc_app).
-behaviour(application).
-export([start/2, stop/1]).

%% ====================================================================
%% API functions
%% ====================================================================
-export([]).



%% ====================================================================
%% Behavioural functions
%% ====================================================================

%% start/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/apps/kernel/application.html#Module:start-2">application:start/2</a>
-spec start(Type :: normal | {takeover, Node} | {failover, Node}, Args :: term()) ->
	{ok, Pid :: pid()}
	| {ok, Pid :: pid(), State :: term()}
	| {error, Reason :: term()}.
%% ====================================================================
start(_Type, _StartArgs) ->
	% 初始化存储, 放在应用而不是监督者中, 以保持监督者的单一职责
	sc_store:init(),
	% 启动顶层supervisor
    case sc_sup:start_link() of
		{ok, Pid} ->
			{ok, Pid};
		Error ->
			{error, Error}
    end.

%% stop/1
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/apps/kernel/application.html#Module:stop-1">application:stop/1</a>
-spec stop(State :: term()) ->  Any :: term().
%% ====================================================================
stop(_State) ->
    ok.

%% ====================================================================
%% Internal functions
%% ====================================================================


