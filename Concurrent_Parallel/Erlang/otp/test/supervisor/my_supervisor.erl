%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(my_supervisor).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start/2,
		 stop/1,
		 init/1]).

start(Name, ChildSpecList) ->
	register(Name, Pid = spawn(?MODULE, init, [ChildSpecList])),
	{ok, Pid}.

stop(Name) ->
	Name ! stop.

init(ChildSpecList) ->
	process_flag(trap_exit, true),
	loop(start_children(ChildSpecList)).

%% ====================================================================
%% Internal functions
%% ====================================================================

% ChildSpecList: [{M,F,A}]
start_children(ChildSpecList) ->
	[{element(2, apply(M, F, A)), {M, F, A}} || {M, F, A} <- ChildSpecList].

% ChildList: [{
%				element 2 of M:F(A), % Pid
%				{M,F,A} 
%			}]
loop(ChildList) ->
	receive
		{'EXIT', Pid, normal} ->
			loop(lists:delete(Pid, 1, ChildList));
		{'EXIT', Pid, _Reason} ->
			NewChildList = restart_child(Pid, ChildList),
			loop(NewChildList);
		stop ->
			terminate(ChildList)
	end.

restart_child(Pid, ChildList) ->
	{Pid, {M,F,A}} = lists:keyfind(Pid, 1, ChildList),
	{ok, NewPid} = apply(M,F,A),
	lists:keyreplace(Pid, 1, ChildList, {NewPid, {M,F,A}}).

terminate(ChildList) ->
	lists:foreach(fun({Pid, _}) -> exit(Pid, kill) end, ChildList).
