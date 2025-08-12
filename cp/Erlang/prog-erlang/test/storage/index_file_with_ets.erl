%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 索引文本文档.
%%% 
%%% 单词在文件中出现的行号, 例: 
%%% apple 	1.
%%% banana 	1,2.
%%% ...
%%% 长度>= MIN_LEN 的单词被忽略, 所有单词小写标准化.
%%% @end
%%%-------------------------------------------------------------------


-module(index_file_with_ets).

-define(MIN_LEN, 3).
-define(TEMP_TABLE, temp_table).      % 临时表
-define(INDEX_TABLE, final_index_table).  % 索引表

% 连接符的模式
-define(PUNCTUATION, "(\\ |\\,|\\.|\\;|\\:|\\?|\\!|\\'|\\t|\\n|\\(|\\)|\\{|\\}|\\[|\\]|\")+").


%% ====================================================================
%% API functions
%% ====================================================================
-export([index/1]).

index(File) ->
  ets:new(?TEMP_TABLE, [ordered_set, named_table]),  % 创建ETS表
  ets:new(?INDEX_TABLE, [ordered_set, named_table]),

  process_file(File),
  construct_index(),
  ets:delete(?TEMP_TABLE) % 删除临时表
.

%% ====================================================================
%% Internal functions
%% ====================================================================
process_file(File) ->
  {ok, IoDevice} = file:open(File, [read]),
  process_lines(IoDevice, 1).

process_lines(IoDevice, N) ->
  case io:get_line(IoDevice, "") of
    eof ->
      %io:format("meet eof~n"),
      ok;
    Line ->
      %io:format("~p ~p~n", [N, Line]),
      process_line(Line, N),
      process_lines(IoDevice, N + 1)
  end.


process_line(Line, N) ->
  case re:split(Line, ?PUNCTUATION, [{return, list}]) of
    Words when length(Words) > 0 ->
      %io:format("~p~n", [Words]),
      process_words(Words, N);
    _ ->
      %io:format("line[~p] no words~n", [Line]),
      []
  end.

process_words(Words, N) ->
  %io:format("~p~p~n", [N, Words]),
  case Words of
    [] -> ok;
    [Word | Rest] ->
      if
        length(Word) >= ?MIN_LEN ->
          Normalise = string:to_lower(Word),
          ets:insert(?TEMP_TABLE, {{Normalise, N}});  % 向ETS表中插入记录
        true -> ok
      end,
      process_words(Rest, N)
  end.



construct_index() ->
  io:format("construct index~n"),
  case ets:first(?TEMP_TABLE) of
    '$end_of_table' -> ok;
    First ->
      case First of
        {Word, N} ->
          IndexEntry = {Word, N},
          construct_index_next(First, IndexEntry)
      end
  end.

construct_index_next(Entry, {Word, LineNo} = IndexEntry) ->
  Next = ets:next(?TEMP_TABLE, Entry),

  case Next of
    '$end_of_table' -> render_entry(IndexEntry);
    {NextWord, M} ->
      if
        NextWord == Word ->
          construct_index_next(Next, {Word, [M | LineNo]});
        true ->
          render_entry(IndexEntry),
          construct_index_next(Next, {NextWord, [M]})
      end
  end.

render_entry({_Word, _LineNo} = IndexEntry) ->
  %io:format("~p:~w ~n", [Word, LineNo]),
  ets:insert(?INDEX_TABLE, IndexEntry),
  ok.
