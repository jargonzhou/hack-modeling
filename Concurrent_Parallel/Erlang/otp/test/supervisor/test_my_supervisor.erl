%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_my_supervisor).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
	Name = coffee_sup,
	{ok, Pid} = my_supervisor:start(Name, [{coffee_fsm, start_link, []}]),
	?DEBUG("Pid", Pid),
	timer:sleep(1000),
	
	PidOfCoffeeFSM = whereis(coffee_fsm),
	?DEBUG("PidOfCoffeeFSM", PidOfCoffeeFSM),
	
	exit(PidOfCoffeeFSM, kill),
	timer:sleep(1000),
	
	PidOfCoffeeFSM2 = whereis(coffee_fsm),
	?DEBUG("PidOfCoffeeFSM2", PidOfCoffeeFSM2),
	
	my_supervisor:stop(Name),
	timer:sleep(1000),
	
	PidOfCoffeeFSM3 = whereis(coffee_fsm),
	?DEBUG("PidOfCoffeeFSM3", PidOfCoffeeFSM3), % undefined
	ok.

%% ====================================================================
%% Internal functions
%% ====================================================================


