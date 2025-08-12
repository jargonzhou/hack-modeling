%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_fac_service_udp).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0,
  run_with_ref/0]).

run() ->
  Port = 1234,
  fac_service_udp:start_server(Port),
  %timer:sleep(1000), % wait a second
  fac_service_udp:client("127.0.0.1", Port, 10).

run_with_ref() ->
  Port = 1234,
  fac_service_udp:start_server(Port),
  %timer:sleep(1000), % wait a second
  fac_service_udp:client_with_ref("127.0.0.1", Port, 10).

%% ====================================================================
%% Internal functions
%% ====================================================================


