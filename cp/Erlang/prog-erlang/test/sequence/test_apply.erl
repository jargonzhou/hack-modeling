%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_apply).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).


run() ->
  ?INFO("start..."),
  ?INFO("apply(erlang, atom_to_list, [hello])",
    apply(erlang, atom_to_list, [hello])).

%% ====================================================================
%% Internal functions
%% ====================================================================

% deprecated:
% {Mod, P1, P2}:Func(A1, A2)
% Mod:Func(A1, A2, {Mod, P1, P2})
% render("{test_apply, 1}:read()", {test_apply, 1}:read())
%%bump(X, {test_apply, K}) ->
%%	{test_apply, X + K}.
%%read({test_apply, N}) ->
%%	N.


