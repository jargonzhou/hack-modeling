%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(sc_element).
-behaviour(gen_server).
-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, code_change/3]).

-define(SERVER, ?MODULE).
-define(DEFAULT_LEASE_TIME, (60*60*24)). % 缓存默认失效时间: 1天

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/2,
		 create/1, create/2,
		 fetch/1, replace/2, delete/1]).

start_link(Value, LeaseTime) ->
	% 启动值进程
	gen_server:start_link(?MODULE, [Value, LeaseTime], []).

%% 使用默认失效时间创建值进程
create(Value) ->
	create(Value, ?DEFAULT_LEASE_TIME).
%% 创建带失效时间的值进程, 如果成功返回{ok, Pid}
create(Value, LeaseTime) ->
	% 委托给监督者
	sc_element_sup:start_child(Value, LeaseTime).

%% 获取缓存值
fetch(Pid) ->
	gen_server:call(Pid, fetch).
%% 替换缓存值
replace(Pid, Value) ->
	gen_server:cast(Pid, {replace, Value}).
%% 删除缓存值
delete(Pid) ->
	gen_server:cast(Pid, delete).


%% ====================================================================
%% Behavioural functions
%% ====================================================================
%% 状态记录
%% value: 缓存的值, lease_time: 缓存失效时间, start_time: 缓存生效时间
-record(state, {value, lease_time, start_time}).


%% init/1
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:init-1">gen_server:init/1</a>
-spec init(Args :: term()) -> Result when
	Result :: {ok, State}
			| {ok, State, Timeout}
			| {ok, State, hibernate}
			| {stop, Reason :: term()}
			| ignore,
	State :: term(),
	Timeout :: non_neg_integer() | infinity.
%% ====================================================================
init([Value, LeaseTime]) ->
	Now = calendar:local_time(), 								% 操作系统当前本地时间(ymd, hms)
	StartTime = calendar:datetime_to_gregorian_seconds(Now), 	% 转换为秒
	TimeLeft = time_left(StartTime, LeaseTime),
    {ok, #state{value=Value,
				lease_time=LeaseTime,
				start_time=StartTime},
	 TimeLeft}.


%% handle_call/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:handle_call-3">gen_server:handle_call/3</a>
-spec handle_call(Request :: term(), From :: {pid(), Tag :: term()}, State :: term()) -> Result when
	Result :: {reply, Reply, NewState}
			| {reply, Reply, NewState, Timeout}
			| {reply, Reply, NewState, hibernate}
			| {noreply, NewState}
			| {noreply, NewState, Timeout}
			| {noreply, NewState, hibernate}
			| {stop, Reason, Reply, NewState}
			| {stop, Reason, NewState},
	Reply :: term(),
	NewState :: term(),
	Timeout :: non_neg_integer() | infinity,
	Reason :: term().
%% ====================================================================
handle_call(fetch, _From, State) ->
	#state{value=Value, lease_time=LeaseTime, start_time=StartTime} = State,
	TimeLeft = time_left(StartTime, LeaseTime),
    Reply = {ok, Value},
    {reply, Reply, State, TimeLeft}.


%% handle_cast/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:handle_cast-2">gen_server:handle_cast/2</a>
-spec handle_cast(Request :: term(), State :: term()) -> Result when
	Result :: {noreply, NewState}
			| {noreply, NewState, Timeout}
			| {noreply, NewState, hibernate}
			| {stop, Reason :: term(), NewState},
	NewState :: term(),
	Timeout :: non_neg_integer() | infinity.
%% ====================================================================
handle_cast({replace, Value}, State) ->
	#state{lease_time=LeaseTime, start_time=StartTime} = State,
	TimeLeft = time_left(StartTime, LeaseTime),
    {noreply, State#state{value=Value}, TimeLeft};
handle_cast(delete, State) ->
	{stop, normal, State}.


%% handle_info/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:handle_info-2">gen_server:handle_info/2</a>
-spec handle_info(Info :: timeout | term(), State :: term()) -> Result when
	Result :: {noreply, NewState}
			| {noreply, NewState, Timeout}
			| {noreply, NewState, hibernate}
			| {stop, Reason :: term(), NewState},
	NewState :: term(),
	Timeout :: non_neg_integer() | infinity.
%% ====================================================================
handle_info(timeout, State) ->
    {stop, normal, State}.


%% terminate/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:terminate-2">gen_server:terminate/2</a>
-spec terminate(Reason, State :: term()) -> Any :: term() when
	Reason :: normal
			| shutdown
			| {shutdown, term()}
			| term().
%% ====================================================================
terminate(_Reason, _State) ->
	% 清除Key-Pid存储
	sc_store:delete(self()),
    ok.


%% code_change/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:code_change-3">gen_server:code_change/3</a>
-spec code_change(OldVsn, State :: term(), Extra :: term()) -> Result when
	Result :: {ok, NewState :: term()} | {error, Reason :: term()},
	OldVsn :: Vsn | {down, Vsn},
	Vsn :: term().
%% ====================================================================
code_change(_OldVsn, State, _Extra) ->
    {ok, State}.


%% ====================================================================
%% Internal functions
%% ====================================================================
%% 缓存剩余有效时间(单位ms), 为0表示缓存已失效, 其中:
%% StartTime: 缓存生效时间, LeaseTime: 缓存失效时间
time_left(_StartTime, infinity) ->
	infinity;
time_left(StartTime, LeaseTime) ->
	Now = calendar:local_time(),
	CurrentTime = calendar:datetime_to_gregorian_seconds(Now),
	TimeElasped = CurrentTime - StartTime,
	case LeaseTime - TimeElasped of
		Time when Time =< 0 -> 0;
		Time 				-> Time * 1000
	end.
























