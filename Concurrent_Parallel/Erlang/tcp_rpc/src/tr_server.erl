%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% TCP RPC Server based on gen_server.
%%%
%%% 运行: > tr_server:start_link().
%%% $ telnet localhost 1055
%%% io:format("~p~n", ["Hello, world!"]).
%%% init:stop().
%%% @end
%%%-------------------------------------------------------------------


-module(tr_server).
-behaviour(gen_server).
-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, code_change/3]).

-define(SERVER, ?MODULE).		% 进程注册名
-define(DEFAULT_PORT, 1055). 	% 默认的TCP端口

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0, start_link/1, get_count/0, stop/0]).

start_link() ->
	start_link(?DEFAULT_PORT).

start_link(Port) ->
    gen_server:start_link({local, ?SERVER}, ?MODULE, [Port], []).

get_count() ->
	gen_server:call(?SERVER, get_count).

stop() ->
	gen_server:cast(?SERVER, stop).

%% ====================================================================
%% Behavioural functions
%% ====================================================================
% 进程状态: {TCP端口, 监听的Socket, 请求数量}
-record(state, {port, lsock, request_count = 0}).

%% init/1
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:init-1">gen_server:init/1</a>
-spec init(Args :: term()) -> Result when
	Result :: {ok, State}
			| {ok, State, Timeout}
			| {ok, State, hibernate}
			| {stop, Reason :: term()}
			| ignore,
	State :: term(),
	Timeout :: non_neg_integer() | infinity.
%% ====================================================================
init([Port]) ->
	{ok, LSocket} = gen_tcp:listen(Port, [{active, true}]), % TCP监听
    {ok, #state{port=Port, lsock=LSocket}, 0}.	% 0: 触发立即超时


%% handle_call/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:handle_call-3">gen_server:handle_call/3</a>
-spec handle_call(Request :: term(), From :: {pid(), Tag :: term()}, State :: term()) -> Result when
	Result :: {reply, Reply, NewState}
			| {reply, Reply, NewState, Timeout}
			| {reply, Reply, NewState, hibernate}
			| {noreply, NewState}
			| {noreply, NewState, Timeout}
			| {noreply, NewState, hibernate}
			| {stop, Reason, Reply, NewState}
			| {stop, Reason, NewState},
	Reply :: term(),
	NewState :: term(),
	Timeout :: non_neg_integer() | infinity,
	Reason :: term().
%% ====================================================================
handle_call(get_count, _From, State) ->
    Reply = {ok, State#state.request_count},
    {reply, Reply, State}.


%% handle_cast/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:handle_cast-2">gen_server:handle_cast/2</a>
%% 停止gen_server.
-spec handle_cast(Request :: term(), State :: term()) -> Result when
	Result :: {noreply, NewState}
			| {noreply, NewState, Timeout}
			| {noreply, NewState, hibernate}
			| {stop, Reason :: term(), NewState},
	NewState :: term(),
	Timeout :: non_neg_integer() | infinity.
%% ====================================================================
handle_cast(stop, State) ->
    {stop, normal, State}.


%% handle_info/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:handle_info-2">gen_server:handle_info/2</a>
%% 处理带外消息, 这里是TCP数据.
-spec handle_info(Info :: timeout | term(), State :: term()) -> Result when
	Result :: {noreply, NewState}
			| {noreply, NewState, Timeout}
			| {noreply, NewState, hibernate}
			| {stop, Reason :: term(), NewState},
	NewState :: term(),
	Timeout :: non_neg_integer() | infinity.
%% ====================================================================
handle_info({tcp, Socket, RawData}, State) ->
	do_rpc(Socket, RawData),
	RequestCount = State#state.request_count,
	{noreply, State#state{request_count = RequestCount + 1}}; % 增加进程状态中请求数量
handle_info(timeout, #state{lsock=LSocket}=State) ->
	{ok, _Sock} = gen_tcp:accept(LSocket),
	{noreply, State}.

%% terminate/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:terminate-2">gen_server:terminate/2</a>
-spec terminate(Reason, State :: term()) -> Any :: term() when
	Reason :: normal
			| shutdown
			| {shutdown, term()}
			| term().
%% ====================================================================
terminate(_Reason, _State) ->
    ok.


%% code_change/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:code_change-3">gen_server:code_change/3</a>
-spec code_change(OldVsn, State :: term(), Extra :: term()) -> Result when
	Result :: {ok, NewState :: term()} | {error, Reason :: term()},
	OldVsn :: Vsn | {down, Vsn},
	Vsn :: term().
%% ====================================================================
code_change(_OldVsn, State, _Extra) ->
    {ok, State}.


%% ====================================================================
%% Internal functions
%% ====================================================================

%% 执行实际RPC操作
%% TODO(zhoujiagen) figure it out how it works.
do_rpc(Socket, RawData) ->
	try
		{M, F, A} = split_out_mfa(RawData),
		Result = apply(M, F, A), % 执行MFA
		gen_tcp:send(Socket, io_lib:fwrite("~p~n", [Result]))
	catch
		_ExceptionType:Err -> gen_tcp:send(Socket, io_lib:fwrite("~p~n", [Err]))
	end.

%% 将原始数据拆分为MFA, 格式: `
%% <MODULE>:<FUNCTION>(<Arg1, ..., ArgN>).
%% `.
split_out_mfa(RawData) ->
	MFA = re:replace(RawData, "\r\n$", "", [{return, list}]),
	{match, [M, F, A]} = re:run(MFA,
								"(.*):(.*)\s*\\((.*)\s*\\)\s*.\s*$",
								[{capture, [1,2,3], list}, ungreedy]),
	{list_to_atom(M), list_to_atom(F), args_to_terms(A)}.

%% 提取参数项 
args_to_terms(RawArgs) ->
	{ok, Toks, _Line} = erl_scan:string("["++RawArgs++"].", 1),
	{ok, Args} = erl_parse:parse_term(Toks),
	Args.




