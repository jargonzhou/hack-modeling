%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(crash_example).
-behaviour(gen_event).
-export([init/1, handle_event/2, handle_call/2, handle_info/2, terminate/2, code_change/3]).

%% ====================================================================
%% API functions
%% ====================================================================
-export([]).



%% ====================================================================
%% Behavioural functions
%% ====================================================================
-record(state, {}).

init(normal) -> {ok, #state{}};
init(return) -> error;
init(ok) -> ok;
init(crash) -> exit(crash).

handle_event(crash, _State) -> 1/0;
handle_event(return, _State) -> error.


handle_call(_Request, State) ->
    Reply = ok,
    {ok, Reply, State}.

handle_info(_Info, State) ->
    {ok, State}.

terminate(_Arg, _State) ->
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.


%% ====================================================================
%% Internal functions
%% ====================================================================


