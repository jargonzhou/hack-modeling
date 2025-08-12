%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_lib_chan_auth).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
  Challenge = lib_chan_auth:make_challenge(),
  Secret = "123456",
  Response = lib_chan_auth:make_response(Challenge, Secret),
  ?INFO("is correct", lib_chan_auth:is_response_correct(Challenge, Response, Secret))
.

%% ====================================================================
%% Internal functions
%% ====================================================================


