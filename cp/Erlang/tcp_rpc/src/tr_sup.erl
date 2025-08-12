%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% TCP RPC应用中的监督者.
%%% @end
%%%-------------------------------------------------------------------


-module(tr_sup).
-behaviour(supervisor).
-export([init/1]).

-define(SERVER, ?MODULE).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0]).

start_link() ->
	% 使用supervisor模块启动自身及子进程(tr_server)
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
	% 子进程规范
    ChildSpec = {
				 tr_server_spec,			% 规范内部ID
				 {tr_server,start_link,[]}, % 子进程启动MFA
				 permanent,					% 子进程失败后是否重启: permanent是立即重启
				 2000,						% 子进程如何被杀死: 2000是无条件杀死后子进程清理状态的时间为2000ms
				 worker,					% 子进程是监督者还是工作者
				 [tr_server]				% 子进程依赖的模块, 用于发布处理中代码替换
				},
	% 监督策略{How, Max, Within}
	SupervisionPolicy = {
					   one_for_one,			% 只影响单个子进程
					   0, 1					% 1s内最大重启次数为0
					  },
    {ok,{SupervisionPolicy, [ChildSpec]}}.

%% ====================================================================
%% Internal functions
%% ====================================================================


