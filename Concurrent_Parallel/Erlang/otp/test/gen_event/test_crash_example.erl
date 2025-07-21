%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_crash_example).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

%%% Run in Bash Shell:
%% 1> {ok, Pid} = gen_event:start().
%% {ok,<0.79.0>}
%% 2> gen_event:which_handlers(Pid).
%% []
%% 3> gen_event:add_handler(Pid, crash_example, normal).
%% ok
%% 4> gen_event:which_handlers(Pid).
%% [crash_example]
%% 5> gen_event:notify(Pid, return).
%% =ERROR REPORT==== 25-Feb-2019::00:11:28.722610 ===
%% ** gen_event handler crash_example crashed.
%% ** Was installed in <0.79.0>
%% ** Last event was: return
%% ** When handler state == {state}
%% ** Reason == error
%% 
%% ok
%% 6> gen_event:add_handler(Pid, crash_example, normal).
%% ok
%% 7> gen_event:notify(Pid, crash).
%% ok
%% =ERROR REPORT==== 25-Feb-2019::00:12:08.842124 ===
%% ** gen_event handler crash_example crashed.
%% ** Was installed in <0.79.0>
%% ** Last event was: crash
%% ** When handler state == {state}
%% ** Reason == {badarith,
%%                  [{crash_example,handle_event,2,
%%                       [{file,"crash_example.erl"},{line,57}]},
%%                   {gen_event,server_update,4,
%%                       [{file,"gen_event.erl"},{line,577}]},
%%                   {gen_event,server_notify,4,
%%                       [{file,"gen_event.erl"},{line,559}]},
%%                   {gen_event,handle_msg,6,[{file,"gen_event.erl"},{line,300}]},
%%                   {proc_lib,init_p_do_apply,3,
%%                       [{file,"proc_lib.erl"},{line,249}]}]}
%% 
%% 8> application:which_applications().
%% [{stdlib,"ERTS  CXC 138 10","3.6"},
%%  {kernel,"ERTS  CXC 138 10","6.1.1"}]
run() ->
	{ok, Pid} = gen_event:start(),
	?DEBUG("Handlers", gen_event:which_handlers(Pid)),
	gen_event:add_handler(Pid, crash_example, return),
	?DEBUG("Handlers", gen_event:which_handlers(Pid)),
	gen_event:add_handler(Pid, crash_example, normal),
	?DEBUG("Handlers", gen_event:which_handlers(Pid)),
	gen_event:notify(Pid, crash),
	?DEBUG("Handlers", gen_event:which_handlers(Pid)),
	gen_event:add_handler(Pid, crash_example, normal),
	?DEBUG("Handlers", gen_event:which_handlers(Pid)),
	gen_event:notify(Pid, return),
	?DEBUG("Handlers", gen_event:which_handlers(Pid)),
	ok.
	

%% ====================================================================
%% Internal functions
%% ====================================================================


