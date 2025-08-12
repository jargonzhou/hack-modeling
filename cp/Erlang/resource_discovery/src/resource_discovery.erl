%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 资源发现服务器.
%%% @end
%%%-------------------------------------------------------------------


-module(resource_discovery).
-behaviour(gen_server).
-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, code_change/3]).

-define(SERVER, ?MODULE).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0,
	add_target_resource_type/1,
	add_local_resource/2,
	fetch_resources/1,
	trade_resources/0
]).

%% 启动服务器
start_link() ->
	gen_server:start_link({local, ?SERVER}, ?MODULE, [], []).

%% 添加所需资源类型
add_target_resource_type(ResType) ->
	gen_server:cast(?SERVER, {add_target_resource_type, ResType}).

%% 添加本地的资源元组
add_local_resource(ResType, ResInstance) ->
	gen_server:cast(?SERVER, {add_local_resource, {ResType, ResInstance}}).

%% 获取指定资源类型的所有资源
fetch_resources(ResType) ->
	gen_server:call(?SERVER, {fetch_resources, ResType}). % 同步调用

%% 资源交换
trade_resources() ->
	gen_server:cast(?SERVER, trade_resources).

%% ====================================================================
%% Behavioural functions
%% ====================================================================
%% 资源元组=(资源类型, 资源)
%% 例: (simple_cache, simple_cache_instance_1@node_a)
-record(state, {
	target_resource_types,	% 所需资源类型的列表
	local_resource_tuples,	% 本地的资源元组列表
	found_resource_tuples	% 探测到的资源元组列表
}).

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
init([]) ->
    {ok, #state{
				target_resource_types = [],
				local_resource_tuples = dict:new(),
				found_resource_tuples = dict:new()
				}
	}.


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
handle_call({fetch_resources, ResType}, _From, State) ->
    Reply = dict:find(ResType, State#state.found_resource_tuples),
    {reply, Reply, State}.


%% handle_cast/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:handle_cast-2">gen_server:handle_cast/2</a>
-spec handle_cast(Request :: term(), State :: term()) -> Result when
	Result :: {noreply, NewState}
			| {noreply, NewState, Timeout}
			| {noreply, NewState, hibernate}
			| {stop, Reason :: term(), NewState},
	NewState :: term(),
	Timeout :: non_neg_integer() | infinity.
%% ====================================================================
handle_cast({add_target_resource_type, ResType}, State) ->
	TargetResType = State#state.target_resource_types,
	NewTargetResType = [ResType | lists:delete(ResType, TargetResType)],
    {noreply, State#state{target_resource_types=NewTargetResType}};

handle_cast({add_local_resource, {ResType, ResInstance}}, State) ->
	ResTuples = State#state.local_resource_tuples,
	NewResTuples = add_resource(ResType, ResInstance, ResTuples),
	{noreply, State#state{local_resource_tuples=NewResTuples}};

handle_cast(trade_resources, State) ->
	ResTuples = State#state.local_resource_tuples, % 本地已有的资源元组
	AllNodes = [node() | nodes()],
	% 向所有互连节点发起资源探测
	lists:foreach(
	  fun(Node) ->
			  gen_server:cast({?SERVER, Node}, {trade_resources, {node(), ResTuples}})
	  end, 
	  AllNodes),
	{noreply, State};
%% ReplyTo: 远程节点, 或者noreply
handle_cast({trade_resources, {ReplyTo, RemoteResTuples}}, 
			#state{target_resource_types=TargetResTypes,
				   local_resource_tuples=LocalResTuples,
				   found_resource_tuples=FoundResTupes} = State) ->
	% 筛选出所需的资源元组
	FilteredRemoteTupes = resouces_for_types(TargetResTypes, RemoteResTuples),
	% 添加到已知的资源元组中
	NewFoundResTuples = add_resources(FilteredRemoteTupes, FoundResTupes),
	case ReplyTo of
		noreply -> ok;
		_ 		-> gen_server:cast({?SERVER, ReplyTo}, 
								   {trade_resources, {noreply, LocalResTuples}})
	end,
	{noreply, State#state{found_resource_tuples=NewFoundResTuples}}.
	
	

%% handle_info/2
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:handle_info-2">gen_server:handle_info/2</a>
-spec handle_info(Info :: timeout | term(), State :: term()) -> Result when
	Result :: {noreply, NewState}
			| {noreply, NewState, Timeout}
			| {noreply, NewState, hibernate}
			| {stop, Reason :: term(), NewState},
	NewState :: term(),
	Timeout :: non_neg_integer() | infinity.
%% ====================================================================
handle_info(Info, State) ->
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
terminate(Reason, State) ->
    ok.


%% code_change/3
%% ====================================================================
%% @doc <a href="http://www.erlang.org/doc/man/gen_server.html#Module:code_change-3">gen_server:code_change/3</a>
-spec code_change(OldVsn, State :: term(), Extra :: term()) -> Result when
	Result :: {ok, NewState :: term()} | {error, Reason :: term()},
	OldVsn :: Vsn | {down, Vsn},
	Vsn :: term().
%% ====================================================================
code_change(OldVsn, State, Extra) ->
    {ok, State}.


%% ====================================================================
%% Internal functions
%% ====================================================================
%% 添加资源类型ResType和资源ResInstance到资源元组ResTuples中
add_resource(ResType, ResInstance, ResTuples) ->
	% 字典中查找
	case dict:find(ResType, ResTuples) of
		{ok, ResInstanceList} -> 
			NewList = [ResInstance | lists:delete(ResInstance, ResInstanceList)],
			dict:store(ResType, NewList, ResTuples);% 返回新的字典
		error ->
			dict:store(ResType, [ResInstance], ResTuples)
	end.

%% add_resource的批量形式
add_resources([{ResType, ResInstance} | T], ResTupes) ->
	add_resources(T, add_resource(ResType, ResInstance, ResTuples));
add_resources([], ResTupes) ->
	ResTupes.

%% 获取资源元组ResTuples中隶属于资源类型ResTypes的资源元组列表
resouces_for_types(ResTypes, ResTuples) ->
	Fun = 
		fun(ResType, ListAcc) ->
				case dict:find(ResType, ResTuples) of
					{ok, List} -> [{ResType, ResInstance} || ResInstance <- List] ++ ListAcc;
					error -> ListAcc
				end
		end,
	lists:foldl(Fun, [], ResTypes)