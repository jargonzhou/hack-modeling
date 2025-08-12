%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(frequency_sup).
-behaviour(supervisor).
-export([init/1]).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0,
		 stop/0]).

start_link() ->
	supervisor:start_link({local, ?MODULE}, ?MODULE, []).

stop() ->
	exit(whereis(?MODULE), shutdown).


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
%% init([]) ->
%%     AChild = {'AName',{'AModule',start_link,[]},
%% 	      permanent,2000,worker,['AModule']},
%%     {ok,{{one_for_all,0,1}, [AChild]}}.
init(_) ->
	% 重启策略
	SupFlags = #{strategy => rest_for_one,
				 intensity => 2,
				 period => 3600},
	% 子进程规范, 注意启动顺序
	ChildSpecList = [child(freq_overload), child(frequency)],
	{ok, {SupFlags, ChildSpecList}}.

%% ====================================================================
%% Internal functions
%% ====================================================================

child(Module) ->
	#{id => Module,
	  start => {Module, start_link, []},
	  restart => permanent,
	  shutdown => 2000,
	  type => worker,
	  modules => [Module]}.




