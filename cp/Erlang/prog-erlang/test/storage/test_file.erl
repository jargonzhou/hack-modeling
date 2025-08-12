%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------

-module(test_file).
-include_lib("kernel/include/file.hrl"). % file_info记录的定义
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([test_read_file1/0,
  test_read_file2/0,
  test_read_file3/0,
  read_file_by_line/1,
  test_read_file4/0,
  test_write_file1/0,
  test_write_file2/0,
  test_write_file3/0,
  test_write_file4/0,
  test_dir/0,
  test_file_info/0,
  test_file_copy_delete/0]).
%%-compile(export_all).


%% ====================================================================
%% Internal functions
%% ====================================================================

%% 读取记录: 返回Erlang数据类型组成的序列
test_read_file1() ->
  case file:consult("test_file/data1.dat") of
    {ok, DataList} ->
      io:format("~p~n", [DataList]);
    {error, Reason} ->
      io:format("~p~n", [{error, Reason}])
  end.

%% 依次读取文件中记录
test_read_file2() ->
  {ok, S} = file:open("test_file/data1.dat", read),
  {ok, Person} = io:read(S, ''),
  io:format("~p~n", [Person]),

  {ok, Cat} = io:read(S, ''),
  io:format("~p~n", [Cat]),

  file:close(S).

%% 按行读取文件
test_read_file3() ->
  {ok, FileHandle} = file:open("test_file/data1.dat", read),
  %Line1 = io:get_line(FileHandle, ''),
  Lines = read_file_by_line(FileHandle),
  io:format("~p~n", [Lines]),
  file:close(FileHandle).

read_file_by_line(FileHandle) ->
  case io:get_line(FileHandle, '') of
    eof -> [];
    Line -> [Line | read_file_by_line(FileHandle)]
  end.

%% 随机读取文件
test_read_file4() ->
  {ok, FH} = file:open("test_file/data1.dat", [read, binary, raw]),
  RawData1 = file:pread(FH, 22, 46),
  io:format("~w~n", [RawData1]),
  RawData2 = file:pread(FH, 0, 10), % 从0开始
  io:format("~w~n", [RawData2]),
  RawData3 = file:pread(FH, 1, 10),
  io:format("~w~n", [RawData3]),
  file:close(FH).

%% 写Erlang数据类型记录到文件中
test_write_file1() ->
  L = [{cats, ["zorrow", "daisy"]},
    {weather, snowing}],
  lib_file:unconsult("test_file/out-data2.dat", L).

%% 按行写入文件
test_write_file2() ->
  {ok, FH} = file:open("test_file/out-data3.dat", write),
  io:format(FH, "~s~n", ["Hello readers"]),
  io:format(FH, "~w~n", [123]),
  io:format(FH, "~s~n", ["that's it"]),
  file:close(FH).

%% 一次性写入文件
test_write_file3() ->
  L = ["Hello readers", $\n, integer_to_list(123), "that's it"],
  file:write_file("test_file/out-data4.dat", L).

%% 随机写入文件
test_write_file4() ->
  {ok, FH} = file:open("test_file/out-data5.dat", [raw, write, binary]),
  L = ["Hello readers", $\n, integer_to_list(123), "that's it"],
  file:pwrite(FH, 10, L).

%% 目录操作
test_dir() ->
  {ok, Files} = file:list_dir("test_file"),
  lists:foreach(fun(File) -> io:format("~p~n", [File]) end, Files).

%% 文件信息
test_file_info() ->
  case file:read_file_info("test_file/data1.dat") of
    {ok, FileInfo} ->
      {FileInfo#file_info.type, FileInfo#file_info.size};
    _ -> error
  end.

%% 文件拷贝和删除
test_file_copy_delete() ->
  Source = "test_file/data1.dat",
  Destination = "test_file/data1.dat.copy",
  file:copy(Source, Destination),
  io:format("~p~n", [lib_file:lines_in_file(Destination)]),
  file:delete(Destination).

