%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% mock generic server
%%% @end
%%%-------------------------------------------------------------------

-module(raw_behavior_server).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/2,
	stop/1,
	call/2]).
-export([init/2]).

start(Name, Args) ->
	?DEBUG(start, {Name, Args}),
	% Name equals Mod
	register(Name, spawn(?MODULE, init, [Name, Args])).


init(Mod, Args) ->
	?DEBUG(init, {Mod, Args}),
	State = Mod:init(Args), 								% callback: init
	loop(Mod, State).

stop(Name) ->
	?DEBUG(stop, Name),
	Name ! {stop, self()},
	receive 
		{reply, Reply} -> Reply 
	end.

call(Name, Msg) ->
	?DEBUG(call, {Name, Msg}),
	Name ! {request, self(), Msg},
	receive
		{reply, Reply} -> Reply
	end.


%% ====================================================================
%% Internal functions
%% ====================================================================

loop(Mod, State) ->
	receive 
		{request, From, Msg} ->	
			{NewState, Reply} = Mod:handle(Msg, State), 	% callback: handle
			reply(From, Reply),
			loop(Mod, NewState);
		{stop, From} ->	
			Reply = Mod:terminate(State), 					% callback: terminate
			reply(From, Reply)
	end.

reply(To, Reply) ->
	To ! {reply, Reply}.
