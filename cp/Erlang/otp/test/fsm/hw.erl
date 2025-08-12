%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 模拟咖啡自动售卖机.
%%% @end
%%%-------------------------------------------------------------------

-module(hw).

%% ====================================================================
%% API functions
%% ====================================================================
-export([display/2,
		 return_change/1,
		 drop_cup/0,
		 prepare/1,
		 reboot/0]).

display(Str, Arg) -> io:format("Display:" ++ Str ++ ".~n", Arg).
return_change(Payment) -> io:format("Machine:Returned ~w in change.~n", [Payment]).
drop_cup() -> io:format("Machine:Dropped Cup.~n").
prepare(Type) -> io:format("Machine:Preparing ~p.~n", [Type]).
reboot() -> io:format("Machine:Rebooted Hardware.~n").

%% ====================================================================
%% Internal functions
%% ====================================================================


