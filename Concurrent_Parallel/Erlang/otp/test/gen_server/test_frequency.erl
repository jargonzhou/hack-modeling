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
	spawn(fun() -> 
				  ?DEBUG("[S]Current Pid", self()),
				  {ok, Pid} = frequency:start([1,2,3,4,5,6,7,8,9,10]),
				  ?DEBUG("[S]Server Pid", Pid)
				  end),
	spawn(fun() ->
				  ?DEBUG("[C]Current Pid", self()),

				  Reply1 = frequency:allocate(),
				  ?DEBUG("[C]Reply", Reply1),
%% 				  case Reply1 of
%% 					  {ok, Freq} -> ?DEBUG("[C]Reply Freq", Freq);
%% 					  {error, no_frequency} -> ?DEBUG("[C]Reply Freq", no_frequency)
%% 				  end,
				  Reply2 = frequency:allocate(),
				  ?DEBUG("[C]Reply", Reply2),
				  frequency:deallocate(1),
				  timer:sleep(500),
				  Reply3 = frequency:allocate(),
				  ?DEBUG("[C]Reply", Reply3)
		  end),
	timer:sleep(2000),
	frequency:stop()
	.

%% ====================================================================
%% Internal functions
%% ====================================================================


