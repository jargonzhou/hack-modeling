%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_nano_service).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0,
  run_seq/0,
  run_par/0,
  run_active1/0,
  run_active2/0,
  run_active3/0]).

run() ->
  spawn(fun() ->
    nano_service:start_nano_server(2345)
        end),
  spawn(fun() ->
    Str = "list_to_tuple([2+3*4, 10+20]).",
    nano_service:nano_client_eval(2345, Str)
        end).

run_seq() ->
  spawn(fun() ->
    nano_server_seq:start_nano_server(2345)
        end),
  spawn(fun() ->
    Str = "list_to_tuple([2+3*4, 10+20]).",
    nano_service:nano_client_eval(2345, Str)
        end).

run_par() ->
  spawn(fun() ->
    nano_server_par:start_nano_server(2345)
        end),
  spawn(fun() ->
    Str = "list_to_tuple([2+3*4, 10+20]).",
    nano_service:nano_client_eval(2345, Str)
        end).

run_active1() ->
  spawn(fun() ->
    nano_service_active:start_nano_server1(2345)
        end),
  spawn(fun() ->
    Str = "list_to_tuple([2+3*4, 10+20]).",
    nano_service:nano_client_eval(2345, Str)
        end).

run_active2() ->
  spawn(fun() ->
    nano_service_active:start_nano_server2(2345)
        end),
  spawn(fun() ->
    Str = "list_to_tuple([2+3*4, 10+20]).",
    nano_service:nano_client_eval(2345, Str)
        end).

run_active3() ->
  spawn(fun() ->
    nano_service_active:start_nano_server3(2345)
        end),
  spawn(fun() ->
    Str = "list_to_tuple([2+3*4, 10+20]).",
    nano_service:nano_client_eval(2345, Str)
        end).
%% ====================================================================
%% Internal functions
%% ====================================================================


