%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 给"gen_server/frequency.erl"添加事件处理器功能.
%%% @end
%%%-------------------------------------------------------------------

-module(freq_overload).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0, 
		 add/2,
		 delete/2]).
-export([no_frequency/0,
		 frequency_available/0,
		 frequency_denied/0]).

start_link() ->
	case gen_event:start({local, ?MODULE}) of
		{ok, Pid} ->
			add(log_counters, {}),
			add(mylogger, {file, "log"}),
			{ok, Pid};
		Error -> Error
	end.


add(M, A) -> gen_event:add_sup_handler(?MODULE, M, A).
delete(M, A) -> gen_event:delete_handler(?MODULE, M, A).

% 无频道警报
no_frequency() ->
	gen_event:notify(?MODULE, {set_alarm, {no_frequency, self()}}).
% 有频道可用, 清除'无频道警报'
frequency_available() ->
	gen_event:notify(?MODULE, {clear_alarm, no_frequency}).
% 被拒绝分配频道警报
frequency_denied() ->
	gen_event:notify(?MODULE, {event, {frequency_denied, self()}}).


%% ====================================================================
%% Internal functions
%% ====================================================================




