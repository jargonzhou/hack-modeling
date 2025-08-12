%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(frequency).
-behaviour(gen_server).
-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, code_change/3]).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/1,
		 start_link/0,
		 stop/0]).
-export([allocate/0,
		 deallocate/1]).

start(FreeFreqs) ->
	gen_server:start_link({local, ?MODULE}, ?MODULE, FreeFreqs, []).

start_link() ->
	start([1,2,3,4,5]).

stop() ->
	gen_server:cast(?MODULE, stop).

allocate() ->
	gen_server:call(?MODULE, {allocate, self()}).

deallocate(Freq) ->
	gen_server:cast(?MODULE, {deallocate, Freq}).



%% ====================================================================
%% Behavioural functions
%% ====================================================================
-record(state, {
				free, 		% [Frequency]
				allocated	% [{Frequency, Pid}]
				}).

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
init(FreeFreqs) ->
    {ok, #state{
				free=FreeFreqs,
				allocated=[]
				}}.


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
handle_call({allocate, Pid}, _From, State) ->
	{NewState, Reply} = allocate(State, Pid),
	{reply, Reply, NewState}.

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
handle_cast({deallocate, Freq}, State) ->
	NewState = deallocate(State, Freq),
	{noreply, NewState};
handle_cast(stop, State) ->
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
handle_info(Info, State) ->
	io:format("[DEBUG] Info=~p, State=~p~n", [Info, State]),
    {noreply, State}.


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
allocate(State = #state{free=[], allocated=_Allocated}, _Pid) ->
	freq_overload:frequency_denied(), 					% event
	{State, 
	 {error, no_frequency}};
allocate(State = #state{free=[Freq|Rest], allocated=Allocated}, Pid) ->
	case Rest of
		[] -> freq_overload:no_frequency(); 			% event
		_ -> ok
	end,
	{State#state{free=Rest, allocated=[{Freq, Pid} | Allocated]}, 
	 {ok, Freq}}.

deallocate(#state{free=Free, allocated=Allocated}, Freq) ->
	case Free of
		[] -> freq_overload:frequency_available(); 		% event
		_ -> ok
	end,
	NewAllocated = lists:keydelete(Freq, 1, Allocated),
	#state{free=[Freq|Free], allocated=NewAllocated}.





