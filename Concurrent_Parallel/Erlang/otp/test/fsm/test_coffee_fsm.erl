%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_coffee_fsm).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
	% 在Eshell中执行更清晰
	{ok, Pid} = coffee_fsm:start_link(),
	sys:trace(Pid, true),
	coffee_fsm:cancel(),
	coffee_fsm:tea(),
	coffee_fsm:cancel(),
	coffee_fsm:cappuccino(),
	coffee_fsm:pay(100),
	coffee_fsm:pay(100),
	coffee_fsm:pay(50),
	coffee_fsm:cup_removed(),
	sys:trace(Pid, false).

%% ====================================================================
%% Internal functions
%% ====================================================================


