%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(coffee_fsm).
-behaviour(gen_fsm).

-export([init/1, terminate/3, code_change/4, 
		 handle_event/3, handle_sync_event/4, handle_info/3]).  %% Callback Functions
%% -export([state_name/2, state_name/3]).
-export([selection/2, payment/2, remove/2]). %% States


%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0,
		 stop/0]).
-export([americano/0,
		 cappuccino/0,
		 tea/0,
		 espresso/0,
		 pay/1,
		 cancel/0,
		 cup_removed/0]). %% Client Functions

start_link() -> 
	gen_fsm:start_link({local, ?MODULE}, ?MODULE, [], []).
stop() -> 
	gen_fsm:sync_send_all_state_event(?MODULE, stop).

americano() -> 
	gen_fsm:send_event(?MODULE, {selection, americano, 150}).
cappuccino() -> 
	gen_fsm:send_event(?MODULE, {selection, cappuccino, 150}).
tea() -> 
	gen_fsm:send_event(?MODULE, {selection, tea, 100}).
espresso() -> 
	gen_fsm:send_event(?MODULE, {selection, espresso, 100}).

pay(Coin) -> 
	gen_fsm:send_event(?MODULE, {pay, Coin}).
cancel() -> 
	gen_fsm:send_event(?MODULE, cancel).
cup_removed() -> 
	gen_fsm:send_event(?MODULE, cup_removed).

%% ====================================================================
%% Behavioural functions
%% ====================================================================
-record(state, {}).

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
init([]) ->
	hw:reboot(),
	hw:display("Make Your Selection", []),
	process_flag(trap_exit, true),
    {ok, selection, #state{}}.


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

selection({selection, Type, Price}, _StateData) ->
	hw:display("Please pay:~w", [Price]),
	{next_state, payment, {Type, Price, 0}};
selection({pay, Coin}, StateData) ->
	hw:return_change(Coin),
	{next_state, selection, StateData};
selection(_Other, StateData) ->
	{next_state, selection, StateData}.

payment({pay, Coin}, {Type, Price, Paid}) when Coin + Paid < Price ->
	NewPaid = Coin + Paid,
	hw:display("Please pay:~w", [Price-NewPaid]),
	{next_state, payment, {Type, Price, NewPaid}};
payment({pay, Coin}, {Type, Price, Paid}) when Coin+Paid >= Price ->
	NewPaid = Coin + Paid,
	hw:display("Preparing Drink.", []),
	hw:return_change(NewPaid - Price),
	hw:drop_cup(),
	hw:prepare(Type),
	hw:display("Remove Drink.", []),
	{next_state, remove, null};
payment(cancel, {_Type, _Price, Paid}) ->
	hw:display("Make Your Selection", []),
	hw:return_change(Paid),
	{next_state, selection, null};
payment(_Event, StateData) ->
    {next_state, payment, StateData}.

remove(cup_removed, StateData) ->
	hw:display("Make Your Selection", []),
	{next_state, selection, StateData};
remove({pay, Coin}, StateData) ->
	hw:return_change(Coin),
	{next_state, remove, StateData};
remove(_Event, StateData) ->
    {next_state, remove, StateData}.

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
handle_event(_Event, StateName, StateData) ->
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
handle_sync_event(stop, _From, _StateName, StateData) ->
    {stop, normal, StateData}.


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
handle_info(_Info, StateName, StateData) ->
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
terminate(_Reason, payment, {_Type, _Price, Paid}) ->
	hw:return_change(Paid);
terminate(_Reason, _StateName, _StatData) ->
    ok.


%% code_change/4
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_fsm.html#Module:code_change-4">gen_fsm:code_change/4</a>
-spec code_change(OldVsn, StateName :: atom(), StateData :: term(), Extra :: term()) -> {ok, NextStateName :: atom(), NewStateData :: term()} when
	OldVsn :: Vsn | {down, Vsn},
	Vsn :: term().
%% ====================================================================
code_change(_OldVsn, StateName, StateData, _Extra) ->
    {ok, StateName, StateData}.


%% ====================================================================
%% Internal functions
%% ====================================================================


