%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_frequency).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
	raw_behavior_frequency:start(),
	{ok, Freq} = raw_behavior_frequency:allocate(),
	?DEBUG("allocated: ~p~n", Freq),
	raw_behavior_frequency:deallocate(Freq),
	raw_behavior_frequency:stop().
	
%% ====================================================================
%% Internal functions
%% ====================================================================


