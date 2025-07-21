%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_frequency_sup).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
	{ok, Pid} = frequency_sup:start_link(),
	timer:sleep(1000),
	?DEBUG("Pid", Pid),
	
	?DEBUG("whereis(freq_overload)", whereis(freq_overload)),
	?DEBUG("whereis(frequency)", whereis(frequency)),
	
	frequency:stop(),
	timer:sleep(1000),
	?DEBUG("whereis(frequency)", whereis(frequency)),
	
	exit(whereis(frequency), kill),
	timer:sleep(1000),
	?DEBUG("whereis(frequency)", whereis(frequency)),
	
	Children = supervisor:which_children(frequency_sup),
	?DEBUG("Children", Children),
	
	CountChildren = supervisor:count_children(frequency_sup),
	?DEBUG("CountChildren", CountChildren),
	
	frequency_sup:stop().

%% ====================================================================
%% Internal functions
%% ====================================================================


