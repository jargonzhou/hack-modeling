%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(test_record).
-include("common.hrl").
-include("todo.hrl"). % 包含文件

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
  R1 = #todo{}, % 创建记录
  ?INFO("R1", R1),

  R2 = #todo{status = urgent, text = "Fix errata in book"}, % 按名指定值
  ?INFO("R2", R2),

  R3 = R2#todo{status = done}, % 拷贝
  ?INFO("R3", R3),


  % 提取记录中值
  #todo{status = Status, who = Who} = R3,
  ?INFO("Status", Status),
  ?INFO("Who", Who),

  % 访问记录的字段
  A = R3#todo.text,
  ?INFO("A", A),

  R4 = #todo{text = "something"},
  R5 = clear_status(R4),
  ?INFO("R4", R4),
  ?INFO("R5", R5)
.

% 将状态设置为finished
clear_status(#todo{status = Status, who = _Who} = R) -> % 使用了函数参数变量绑定
  case Status of
    reminder -> R#todo{status = finished}
  end.


%% ====================================================================
%% Internal functions
%% ====================================================================

