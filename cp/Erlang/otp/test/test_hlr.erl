%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_hlr).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
	hlr:new(),
	hlr:attach(12345),
	{ok, Phone} = hlr:lookup_phone(self()),
	?DEBUG("Phone", Phone),
	hlr:detach(),
	{error, invalid} = hlr:lookup_phone(self()),
	?DEBUG("Phone", invalid),
	hlr:destroy().

%% ====================================================================
%% Internal functions
%% ====================================================================


