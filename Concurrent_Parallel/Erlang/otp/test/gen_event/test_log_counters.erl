%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_log_counters).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
	{ok, Pid} = gen_event:start(),
	gen_event:add_handler(Pid, log_counters, {}),
	gen_event:notify(Pid, {set_alarm, {no_frequency, self()}}),
	gen_event:notify(Pid, {event, {frequency_denied, self()}}),
	gen_event:notify(Pid, {event, {frequency_denied, self()}}),
	log_counters:get_counters(Pid),
	gen_event:stop(Pid).
	
%% ====================================================================
%% Internal functions
%% ====================================================================


