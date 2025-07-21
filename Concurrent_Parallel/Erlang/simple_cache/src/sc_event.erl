%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 缓存事件API.
%%% @end
%%%-------------------------------------------------------------------


-module(sc_event).

%% ====================================================================
%% API functions
%% ====================================================================
-export([start_link/0,
		 add_handler/2,
		 delete_handler/2,
		 lookup/1,
		 create/2,
		 replace/2,
		 delete/1]).

-define(SERVER, ?MODULE).

%% 启动gen_event容器(事件管理器)
start_link() -> 
	gen_event:start_link({local, ?SERVER}).

%% 添加事件处理器
add_handler(Handler, Args) -> 
	gen_event:add_handler(?SERVER, Handler, Args).
%% 移除事件处理器
delete_handler(Handler, Args) -> 
	gen_event:delete_handler(?SERVER, Handler, Args).

%% 生成按键查找事件
lookup(Key) -> 
	gen_event:notify(?SERVER, {lookup, Key}).
%% 生成创建键值对事件
create(Key, Value) -> 
	gen_event:notify(?SERVER, {create, {Key, Value}}).
%% 生成按键替换值事件
replace(Key, Value) -> 
	gen_event:notify(?SERVER, {replace, {Key, Value}}).
%% 生成按键移除事件
delete(Key) -> 
	gen_event:notify(?SERVER, {delete, Key}).


%% ====================================================================
%% Internal functions
%% ====================================================================


