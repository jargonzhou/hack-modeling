%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(sc_sup).
-behaviour(supervisor).
-export([init/1]).

-define(SERVER, ?MODULE).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0]).

start_link() ->
	% 启动
	supervisor:start_link({local, ?SERVER}, ?MODULE, []).

%% ====================================================================
%% Behavioural functions
%% ====================================================================

%% init/1
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/supervisor.html#Module:init-1">supervisor:init/1</a>
-spec init(Args :: term()) -> Result when
	Result :: {ok, {SupervisionPolicy, [ChildSpec]}} | ignore,
	SupervisionPolicy :: {RestartStrategy, MaxR :: non_neg_integer(), MaxT :: pos_integer()},
	RestartStrategy :: one_for_all
					 | one_for_one
					 | rest_for_one
					 | simple_one_for_one,
	ChildSpec :: {Id :: term(), StartFunc, RestartPolicy, Type :: worker | supervisor, Modules},
	StartFunc :: {M :: module(), F :: atom(), A :: [term()] | undefined},
	RestartPolicy :: permanent
				   | transient
				   | temporary,
	Modules :: [module()] | dynamic.
%% ====================================================================
init([]) ->
	% supervisor子进程规范
	ScElementSupChildSpec = {sc_element_sup_spec, {sc_element_sup, start_link, []},
						  permanent, 2000,
						  supervisor, [sc_element]},
	% gen_event容器(事件管理器)子进程规范
	ScEventChildSpec = {sc_event_spec, {sc_event, start_link, []},
						permanent, 2000,
						worker, [sc_event]},
	RestartStrategy = {one_for_one, 4, 3600},
    {ok,{RestartStrategy, [ScElementSupChildSpec, ScEventChildSpec]}}.

%% ====================================================================
%% Internal functions
%% ====================================================================


