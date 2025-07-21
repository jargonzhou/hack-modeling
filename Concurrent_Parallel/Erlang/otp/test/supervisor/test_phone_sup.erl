%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_phone_sup).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
	hlr:new(),
	phone_sup:start_link(),
	timer:sleep(500),
	
	phone_sup:attach_phone(1),
	phone_sup:attach_phone(2),
	timer:sleep(500),

	?DEBUG("supervisor:which_children(phone_sup)", supervisor:which_children(phone_sup)),
	
	phone_sup:detach_phone(2),
	timer:sleep(500),
	
	?DEBUG("supervisor:which_children(phone_sup)", supervisor:which_children(phone_sup)),
	
	
	
	ok.

%% ====================================================================
%% Internal functions
%% ====================================================================


