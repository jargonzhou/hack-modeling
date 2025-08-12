%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(test_usr_db).

-include("common.hrl").
-include("usr.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
  usr_db:create_tables("UsrTableFile"),
  ?INFO("id is 1", usr_db:lookup_id(1)),
  batch_add(),
  query_and_update(),

  usr_db:restore_backup(),

  ?INFO("info of usrRam", ets:info(usrRam)),
  delete_op(),
  ?INFO("info of usrRam", ets:info(usrRam)),

  ok.

batch_add() ->
  Seq = lists:seq(1, 100000),
  Add = fun(Id) ->
    usr_db:add_usr(
      #usr{msisdn = 700000000 + Id, id = Id, plan = prepay, services = [data, sms, lbs]})
        end,
  lists:foreach(Add, Seq),
  ok.

query_and_update() ->
  {ok, Usr} = usr_db:lookup_msisdn(700000000 + 1),
  ?INFO("Usr", Usr),

  usr_db:update_usr(Usr#usr{services = [data, sms], status = disabled}),

  {ok, Usr2} = usr_db:lookup_msisdn(700000000 + 1),
  ?INFO("Usr2", Usr2),
  ok.

delete_op() ->
  usr_db:delete_disabled(),
  ok.


%% ====================================================================
%% Internal functions
%% ====================================================================


