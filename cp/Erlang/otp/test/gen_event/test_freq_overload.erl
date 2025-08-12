%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_freq_overload).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
	{ok, _ServerPid} = frequency:start([1,2,3,4,5]),
	{ok, EventMPid} = freq_overload:start_link(),
	freq_overload:add(mylogger, standard_io),	

	frequency:allocate(),frequency:allocate(),frequency:allocate(),
	frequency:allocate(),frequency:allocate(),
	
	frequency:allocate(),
	frequency:allocate(),

	frequency:deallocate(1),

	timer:sleep(1000), % wait a second
	Reply = log_counters:get_counters(EventMPid),
	?DEBUG("Reply", Reply),
	
	timer:sleep(1000), % wait a second
	frequency:stop(),

	ok.

%% ====================================================================
%% Internal functions
%% ====================================================================


