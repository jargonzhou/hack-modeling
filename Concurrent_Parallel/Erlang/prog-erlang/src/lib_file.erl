%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(lib_file).

%% ====================================================================
%% API functions
%% ====================================================================
-export([records_in_file/1,
  lines_in_file/1,
  unconsult/2]).

%% 读取文件中Erlang数据类型记录
records_in_file(File) ->
  case file:consult(File) of
    {ok, DataList} ->
      DataList;
    {error, Reason} ->
      {error, Reason}
  end.

%% 按行读取文件
lines_in_file(File) ->
  {ok, FH} = file:open(File, read),
  read_file_line_by_line(FH).

%% file:consult的逆操作: 即将Erlang数据类型记录写入文件
unconsult(File, L) ->
  {ok, FH} = file:open(File, write),
  lists:foreach(fun(X) -> io:format(FH, "~p.~n", [X]) end, L),
  file:close(FH).


%% ====================================================================
%% Internal functions
%% ====================================================================


read_file_line_by_line(FileHandle) ->
  case io:get_line(FileHandle, '') of
    eof -> [];
    Line -> [Line | read_file_line_by_line(FileHandle)]
  end.