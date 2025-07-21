%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 动态创建子进程示例.
%%% @end
%%%-------------------------------------------------------------------

-module(phone_sup).
-behaviour(supervisor).
-export([init/1]).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0,
		 attach_phone/1,
		 detach_phone/1]).

start_link() ->
	supervisor:start_link({local, ?MODULE}, ?MODULE, []).

attach_phone(Ms) ->
	case hlr:lookup_id(Ms) of
		{ok, _Pid} -> {error, attached};
		_ ->
			ChildSpec = #{id => Ms,
						  start => {phone_fsm, start_link, [Ms]},
						  restart => transient,
						  shutdown => 2000,
						  type => worker,
						  modules => [phone_fsm]},
			supervisor:start_child(?MODULE, ChildSpec)
	end.

detach_phone(Ms) ->
	case hlr:lookup_id(Ms) of
		{ok, _Pid} ->
			% terminate then delete
			supervisor:terminate_child(?MODULE, Ms),
			supervisor:delete_child(?MODULE, Ms);
		_ ->
			{error, detached}
	end.


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
init([]) ->
	SupFlags = #{strategy => one_for_one,
				 intensity => 10,
				 period => 3600},
	{ok, {SupFlags, []}}.


%% ====================================================================
%% Internal functions
%% ====================================================================


