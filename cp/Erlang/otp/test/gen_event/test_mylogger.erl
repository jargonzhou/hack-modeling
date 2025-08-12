%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_mylogger).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0,
		 test_swap_handler/0]).

run() ->
	{ok, Pid} = gen_event:start(),

	% add handler
	gen_event:add_handler(Pid, mylogger, {file, "alarmlog"}),
	gen_event:notify(Pid, {set_alarm, {no_frequency, self()}}),
	gen_event:sync_notify(Pid, {clear_alarm, no_frequency}),

	% add another handler
	gen_event:add_handler(Pid, mylogger, standard_io),
	Pid ! sending_junk,

	% remove handler
	{count, Count} = gen_event:delete_handler(Pid, mylogger, stop),
	?DEBUG("Count", Count),

	{ok, Bin} = file:read_file("alarmlog"),
	io:format(Bin),

	% stop gen_event
	ok = gen_event:stop(Pid),
	ok.

test_swap_handler() ->
	{ok, Pid} = gen_event:start(),
	sys:trace(Pid, true),
	gen_event:add_handler(Pid, mylogger, {file, "alarmlog"}),
	gen_event:notify(Pid, {set_alarm, {no_frequency, self()}}),
	% swap handler
	Swap_Result = gen_event:swap_handler(Pid, {mylogger, swap}, {mylogger, standard_io}),
	?DEBUG("Swap_Result", Swap_Result),
	gen_event:notify(Pid, {set_alarm, {no_frequency, self()}}),
	{ok, Bin} = file:read_file("alarmlog"),
	io:format(Bin),
	% swap handler again
	Swap_Result2 = gen_event:swap_handler(Pid, {mylogger, swap}, {mylogger, "alarmlog2"}),
	?DEBUG("Swap_Result2", Swap_Result2),
	gen_event:notify(Pid, {set_alarm, {no_frequency, self()}}),
	{ok, Bin2} = file:read_file("alarmlog2"),
	io:format(Bin2),
	sys:trace(Pid, false),
	ok.

%% ====================================================================
%% Internal functions
%% ====================================================================


