%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(mylogger).
-behaviour(gen_event).
-export([init/1, handle_event/2, handle_call/2, handle_info/2, terminate/2, code_change/3]).

%% ====================================================================
%% API functions
%% ====================================================================
%% -export([]).



%% ====================================================================
%% Behavioural functions
%% ====================================================================
-record(state, {
				fd=standard_io,
				count=0}).

%% init/1
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_event.html#Module:init-1">gen_event:init/1</a>
-spec init(InitArgs) -> Result when
	InitArgs :: Args | {Args, Term :: term()},
	Args :: term(),
	Result :: {ok, State}
			| {ok, State, hibernate}
			| {error, Reason :: term()},
	State :: term().
%% ====================================================================
%% init([]) ->
%%     {ok, #state{}}.
% for add_handler
init(standard_io) ->
	{ok, #state{fd=standard_io, count=1}};
init({file, File}) ->
	{ok, Fd} = file:open(File, write),
	{ok, #state{fd=Fd, count=1}};
%% for swap handler
% => standard_io
init({standard_io, #state{fd=Fd, count=Count}}) -> % when is_pid(Fd)
	io:format("DEBUG: Close Fd=~p~n", [Fd]),
	file:close(Fd),
	{ok, #state{fd=standard_io, count=Count}};
% => File
init({File, #state{fd=standard_io, count=Count}}) when is_list(File) ->
	{ok, Fd} = file:open(File, write),
	io:format("DEBUG: Fd=~p~n", [Fd]),
	{ok, #state{fd=Fd, count=Count}};

init(Args) ->
	{error, {args, Args}}.

%% handle_event/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_event.html#Module:handle_event-2">gen_event:handle_event/2</a>
-spec handle_event(Event :: term(), State :: term()) -> Result when
	Result :: {ok, NewState}
			| {ok, NewState, hibernate}
			| {swap_handlers, Args1, NewState, Handler2, Args2}
			| remove_handler,
	NewState :: term(), Args1 :: term(), Args2 :: term(),
	Handler2 :: Module2 | {Module2, Id :: term()},
	Module2 :: atom().
%% ====================================================================
%% handle_event(Event, State) ->
%%     {ok, State}.
handle_event(Event, #state{fd=Fd, count=Count}) ->
	print(Fd, Count, Event, "Event"),
	{ok, #state{fd=Fd, count=Count+1}}.

%% handle_call/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_event.html#Module:handle_call-2">gen_event:handle_call/2</a>
-spec handle_call(Request :: term(), State :: term()) -> Result when
	Result :: {ok, Reply, NewState}
			| {ok, Reply, NewState, hibernate}
			| {swap_handler, Reply, Args1, NewState, Handler2, Args2}
			| {remove_handler, Reply},
	Reply :: term(),
	NewState :: term(), Args1 :: term(), Args2 :: term(),
	Handler2 :: Module2 | {Module2, Id :: term()},
	Module2 :: atom().
%% ====================================================================
handle_call(_Request, State) ->
    Reply = ok,
    {ok, Reply, State}.


%% handle_info/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_event.html#Module:handle_info-2">gen_event:handle_info/2</a>
%% -spec handle_info(Info :: term(), State :: term()) -> Result when
%% 	Result :: {ok, NewState}
%% 			| {ok, NewState, hibernate}
%% 			| {swap_handler, Args1, NewState, Handler2, Args2}
%% 			| remove_handler,
%% 	NewState :: term(), Args1 :: term(), Args2 :: term(),
%% 	Handler2 :: Module2 | {Module2, Id :: term()},
%% 	Module2 :: atom().
%% %% ====================================================================
%% handle_info(Info, State) ->
%%     {ok, State}.
handle_info(Event, #state{fd=Fd, count=Count}) ->
	print(Fd, Count, Event, "Event"),
	{ok, #state{fd=Fd, count=Count+1}}.

%% terminate/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_event.html#Module:terminate-2">gen_event:terminate/2</a>
-spec terminate(Arg, State :: term()) -> term() when
	Arg :: Args
		| {stop, Reason}
		| stop
		| remove_handler
		| {error, {'EXIT', Reason}}
		| {error, Term :: term()},
	Args :: term(), Reason :: term().
%% ====================================================================
%% terminate(Arg, State) ->
%%     ok.
terminate(swap, State=#state{fd=_Fd, count=_Count}) ->
	io:format("DEBUG: swap: ~p~n", [State]),
	State;
terminate(_Arg, #state{fd=standard_io, count=Count}) ->
	{count, Count};
terminate(_Arg, #state{fd=Fd, count=Count}) ->
	file:close(Fd),
	{count, Count}.


%% code_change/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_event.html#Module:code_change-3">gen_event:code_change/3</a>
-spec code_change(OldVsn, State :: term(), Extra :: term()) -> {ok, NewState :: term()} when
	OldVsn :: Vsn | {down, Vsn},
	Vsn :: term().
%% ====================================================================
code_change(_OldVsn, State, _Extra) ->
    {ok, State}.


%% ====================================================================
%% Internal functions
%% ====================================================================

print(Fd, Count, Event, Tag) ->
	io:format(Fd, "Id:~w, Time:~w Date: ~w~n"++Tag++":~w~n",
			  [Count, time(), date(), Event]).

