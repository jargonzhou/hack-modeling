%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(lib_chan_auth).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([make_challenge/0,
  make_response/2,
  is_response_correct/3]).

%% 生成随机字符串
make_challenge() ->
  random_string(25).

%% 生成密钥
make_response(Challenge, Secret) ->
  crypto:hash(md5, Challenge ++ Secret).

%% 验证密钥
is_response_correct(Challenge, Response, Secret) ->
  case crypto:hash(md5, Challenge ++ Secret) of
    Response -> true;
    _ -> false
  end.

%% ====================================================================
%% Internal functions
%% ====================================================================

random_string(N) ->
  random_seed(), random_string(N, []).

random_string(0, D) ->
  D;
random_string(N, D) ->
  random_string(N - 1, [rand:uniform(26) - 1 + $a | D]).

random_seed() ->
  {_, _, X} = erlang:timestamp(),
  {H, M, S} = time(),
  H1 = H * X rem 32767,
  M1 = M * X rem 32767,
  S1 = S * X rem 32767,
  put(random_seed, {H1, M1, S1}).
