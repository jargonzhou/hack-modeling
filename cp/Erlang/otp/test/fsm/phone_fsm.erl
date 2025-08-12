%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 手机系统.
%%% @end
%%%-------------------------------------------------------------------

-module(phone_fsm).
-behaviour(gen_fsm).
-export([init/1, handle_event/3, handle_sync_event/4, handle_info/3, terminate/3, code_change/4]).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/1]).
-export([inbound/1, action/2, busy/1, reject/1, accept/1, hangup/1]).
-export([idle/2, calling/2, connected/2, receiving/2]).

start_link(Ms) ->
	gen_fsm:start_link(?MODULE, Ms, [{debug, [trace]}]).
%%    gen_fsm:start_link(?MODULE, Ms, []).


%% Events from the Phone
action({outbound, ToMs}, MsId) ->
	gen_fsm:sync_send_all_state_event(MsId, {outbound, ToMs});
action(Action, MsId) ->  %Action == hangup, reject, accept
	gen_fsm:send_event(MsId, {action,Action}).

busy(ToMsId) ->
	gen_fsm:send_event(ToMsId, {busy, self()}).
reject(ToMsId) ->
	gen_fsm:send_event(ToMsId, {reject, self()}).
accept(ToMsId) ->
	gen_fsm:send_event(ToMsId, {accept, self()}).
hangup(ToMsId) ->
	gen_fsm:send_event(ToMsId, {hangup, self()}).
inbound(ToMsId) ->
	gen_fsm:send_event(ToMsId, {inbound, self()}).


%% ====================================================================
%% Behavioural functions
%% ====================================================================
%% -record(state, {}).

%% init/1
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:init-1">gen_fsm:init/1</a>
-spec init(Args :: term()) -> Result when
	Result :: {ok, StateName, StateData}
			| {ok, StateName, StateData, Timeout}
			| {ok, StateName, StateData, hibernate}
			| {stop, Reason}
			| ignore,
	StateName :: atom(),
	StateData :: term(),
	Timeout :: non_neg_integer() | infinity,
	Reason :: term().
%% ====================================================================
init(Ms) ->
	%%     {ok, state_name, #state{}}.
	process_flag(trap_exit, true),
	hlr:attach(Ms),
	{ok, idle, Ms}.

%% %% state_name/2
%% %% ====================================================================
%% %% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:StateName-2">gen_fsm:StateName/2</a>
%% -spec state_name(Event :: timeout | term(), StateData :: term()) -> Result when
%% 	Result :: {next_state, NextStateName, NewStateData}
%% 			| {next_state, NextStateName, NewStateData, Timeout}
%% 			| {next_state, NextStateName, NewStateData, hibernate}
%% 			| {stop, Reason, NewStateData},
%% 	NextStateName :: atom(),
%% 	NewStateData :: term(),
%% 	Timeout :: non_neg_integer() | infinity,
%% 	Reason :: term().
%% %% ====================================================================
%% % @todo implement actual state
%% state_name(Event, StateData) ->
%%     {next_state, state_name, StateData}.

%% State: idle
idle({inbound, FromMsId}, Ms) ->
	phone:reply(inbound, FromMsId, Ms),
	{next_state, receiving, {Ms, FromMsId}};
idle(_Ignore, State) ->  % , hangup, reject, accept
	io:format("~p in idle, ignored. State:~w, Event:~w~n",[self(), State, _Ignore]),
	{next_state, idle, State}.

%% State: calling(呼出)
calling({action, hangup}, {Ms, CallingMsId}) ->
	phone_fsm:hangup(CallingMsId),
	{next_state, idle, Ms};
calling({busy, Pid}, {Ms, Pid}) ->
	phone:reply(busy, Pid, Ms),
	{next_state, idle, Ms};
calling({reject, Pid}, {Ms, Pid}) ->
	phone:reply(rejected, Pid, Ms),
	{next_state, idle, Ms};
calling({accept, Pid}, {Ms, Pid}) ->
	case frequency:allocate() of
		{error, no_frequency} ->
			phone_fsm:reject(Pid),
			phone:reply(no_frequency, Pid, Ms),
			{next_state, idle, Ms};
		{ok, Freq} ->
			phone:reply(connected, Pid, Ms),
			{next_state, connected, {Ms, Pid, Freq}}
	end;
calling({inbound, Pid}, State) ->
	phone_fsm:busy(Pid),
	{next_state, calling, State};
calling(_Ignore, State) ->  % {action, reject}, {action, accept}
	io:format("In calling, ignored. State:~w, Event:~w~n",[State, _Ignore]),
	{next_state, calling, State}.

%% State: connected(通话建立)
connected({inbound, FromMsId}, State) ->
	phone_fsm:busy(FromMsId),
	{next_state, connected, State};
connected({action, hangup}, {Ms, OtherMsId, Freq}) -> %% We hang up, We initated call
	phone_fsm:hangup(OtherMsId),
	frequency:deallocate(Freq),
	{next_state, idle, Ms};
connected({action, hangup}, {Ms, OtherMsId}) -> %% We hang up, Other initated call
	phone_fsm:hangup(OtherMsId),
	{next_state, idle, Ms};
connected({hangup, OtherMsId}, {Ms, OtherMsId}) -> %% they hang Up
	phone:reply(hangup, OtherMsId, Ms),
	{next_state, idle, Ms};
connected({hangup, OtherMsId}, {Ms, OtherMsId, Freq}) -> %% they hang Up
	phone:reply(hangup, OtherMsId, Ms),
	frequency:deallocate(Freq),
	{next_state, idle, Ms};
connected(_Ignore, State) ->
	io:format("In connected, ignored. State:~w, Event:~w~n",[State, _Ignore]),
	{next_state, connected, State}.

%% State: receiving(有呼入)
receiving({action, accept}, {Ms, FromMsId}) ->
	phone_fsm:accept(FromMsId),
	{next_state, connected, {Ms, FromMsId}};
receiving({action, reject}, {Ms, FromMsId}) ->
	phone_fsm:reject(FromMsId),
	{next_state, idle, Ms};
receiving({hangup, FromMsId}, {Ms, FromMsId}) ->
	phone:reply(hangup, FromMsId, Ms),
	{next_state, idle, Ms};
receiving({inbound, FromMsId}, State) ->  %Others
	phone_fsm:busy(FromMsId),
	{next_state, receiving, State};
receiving(_Ignore, State) ->  % {action, hangup}
	io:format("In receiving, ignored. State:~w, Event:~w~n",[State, _Ignore]),
	{next_state, receiving, State}.


%% %% state_name/3
%% %% ====================================================================
%% %% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:StateName-3">gen_fsm:StateName/3</a>
%% -spec state_name(Event :: term(), From :: {pid(), Tag :: term()}, StateData :: term()) -> Result when
%% 	Result :: {reply, Reply, NextStateName, NewStateData}
%% 			| {reply, Reply, NextStateName, NewStateData, Timeout}
%% 			| {reply, Reply, NextStateName, NewStateData, hibernate}
%% 			| {next_state, NextStateName, NewStateData}
%% 			| {next_state, NextStateName, NewStateData, Timeout}
%% 			| {next_state, NextStateName, NewStateData, hibernate}
%% 			| {stop, Reason, Reply, NewStateData}
%% 			| {stop, Reason, NewStateData},
%% 	Reply :: term(),
%% 	NextStateName :: atom(),
%% 	NewStateData :: atom(),
%% 	Timeout :: non_neg_integer() | infinity,
%% 	Reason :: normal | term().
%% %% ====================================================================
%% state_name(Event, From, StateData) ->
%%     Reply = ok,
%%     {reply, Reply, state_name, StateData}.


%% handle_event/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:handle_event-3">gen_fsm:handle_event/3</a>
-spec handle_event(Event :: term(), StateName :: atom(), StateData :: term()) -> Result when
	Result :: {next_state, NextStateName, NewStateData}
			| {next_state, NextStateName, NewStateData, Timeout}
			| {next_state, NextStateName, NewStateData, hibernate}
			| {stop, Reason, NewStateData},
	NextStateName :: atom(),
	NewStateData :: term(),
	Timeout :: non_neg_integer() | infinity,
	Reason :: term().
%% ====================================================================
handle_event(Event, StateName, StateData) ->
    {next_state, StateName, StateData}.


%% handle_sync_event/4
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:handle_sync_event-4">gen_fsm:handle_sync_event/4</a>
-spec handle_sync_event(Event :: term(), From :: {pid(), Tag :: term()}, StateName :: atom(), StateData :: term()) -> Result when
	Result :: {reply, Reply, NextStateName, NewStateData}
			| {reply, Reply, NextStateName, NewStateData, Timeout}
			| {reply, Reply, NextStateName, NewStateData, hibernate}
			| {next_state, NextStateName, NewStateData}
			| {next_state, NextStateName, NewStateData, Timeout}
			| {next_state, NextStateName, NewStateData, hibernate}
			| {stop, Reason, Reply, NewStateData}
			| {stop, Reason, NewStateData},
	Reply :: term(),
	NextStateName :: atom(),
	NewStateData :: term(),
	Timeout :: non_neg_integer() | infinity,
	Reason :: term().
%% ====================================================================
%% handle_sync_event(Event, From, StateName, StateData) ->
%%     Reply = ok,
%%     {reply, Reply, StateName, StateData}.

handle_sync_event({outbound, ToMs}, _From, idle, Ms) ->
	case hlr:lookup_id(ToMs) of
		{error, invalid} ->
			io:format("ERROR, INVALID~n"),
			phone:reply(invalid, ToMs, Ms),
			{reply, {error, invalid}, idle, Ms};
		{ok, ToMsId} when is_pid(ToMsId) ->
			phone:reply(outbound, ToMs, Ms),
			phone_fsm:inbound(ToMsId),
			{reply, ok, calling, {Ms, ToMsId}}
	end;
handle_sync_event({outbound, _ToMSISDN}, _From, State, MSISDN) ->
	{reply, {error, busy}, State, MSISDN}.

%% handle_info/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:handle_info-3">gen_fsm:handle_info/3</a>
-spec handle_info(Info :: term(), StateName :: atom(), StateData :: term()) -> Result when
	Result :: {next_state, NextStateName, NewStateData}
			| {next_state, NextStateName, NewStateData, Timeout}
			| {next_state, NextStateName, NewStateData, hibernate}
			| {stop, Reason, NewStateData},
	NextStateName :: atom(),
	NewStateData :: term(),
	Timeout :: non_neg_integer() | infinity,
	Reason :: normal | term().
%% ====================================================================
handle_info(Info, StateName, StateData) ->
	{next_state, StateName, StateData}.


%% terminate/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:terminate-3">gen_fsm:terminate/3</a>
-spec terminate(Reason, StateName :: atom(), StateData :: term()) -> Result :: term() when
	Reason :: normal
			| shutdown
			| {shutdown, term()}
			| term().
%% ====================================================================
%% terminate(Reason, StateName, StatData) ->
%%     ok.
terminate(_Reason, idle, _Ms) ->
	hlr:detach();
terminate(_Reason, calling, {_Ms, CallingMsId}) ->
	phone_fsm:hangup(CallingMsId),
	hlr:detach();
terminate(_Reason, connected, {_Ms, OtherMsId, _Freq}) ->
	%% We hang up, We initated call
	phone_fsm:hangup(OtherMsId),
	hlr:detach();
terminate(_Reason, receiving, {_Ms, FromMsId}) ->
	phone_fsm:reject(FromMsId),
	hlr:detach().

%% code_change/4
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:code_change-4">gen_fsm:code_change/4</a>
-spec code_change(OldVsn, StateName :: atom(), StateData :: term(), Extra :: term()) -> {ok, NextStateName :: atom(), NewStateData :: term()} when
	OldVsn :: Vsn | {down, Vsn},
	Vsn :: term().
%% ====================================================================
code_change(OldVsn, StateName, StateData, Extra) ->
    {ok, StateName, StateData}.


%% ====================================================================
%% Internal functions
%% ====================================================================


