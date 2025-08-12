%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% mock generic server callbacks
%%% @end
%%%-------------------------------------------------------------------

-module(raw_behavior_frequency).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/0,
	stop/0,
	allocate/0,
	deallocate/1]).
-export([init/1,
	handle/2,
	terminate/1]).

start() ->
	?DEBUG(start, []),
	raw_behavior_server:start(?MODULE, []).

stop() ->
	?DEBUG(stop, []),
	raw_behavior_server:stop(?MODULE).

allocate() ->
	?DEBUG(allocate, []),
	raw_behavior_server:call(?MODULE, {allocate, self()}).

deallocate(Freq) ->
	?DEBUG(deallocate, Freq),
	raw_behavior_server:call(?MODULE, {deallocate, Freq}).

%%% callbacks

init(_Args) ->
	?DEBUG(init, _Args),
	% State: {Free=[Frequency], Allocated=[{Frequency, Pid}]}
	{[10,11,12,13,14,15], []}.

handle({allocate, From}, Frequencies) ->
	?DEBUG(handle, {{allocate, From}, Frequencies}),
	allocate(Frequencies, From);
handle({deallocate, Freq}, Frequencies) ->
	?DEBUG(handle, {{deallocate, Freq}, Frequencies}),
	deallocate(Frequencies, Freq).

terminate(_State) ->
	?DEBUG(terminate, _State),
	ok.

%% ====================================================================
%% Internal functions
%% ====================================================================

allocate({[], Allocated}, _Pid) ->
	{{[], Allocated}, {error, no_frequency}};
allocate({[Freq|Free], Allocated}, Pid) ->
	{{Free, [{Freq, Pid} | Allocated]}, {ok, Freq}}.

deallocate({Free, Allocated}, Freq) ->
	NewAllocated = lists:keydelete(Freq, 1, Allocated),
	{[Freq|Free], NewAllocated}.

