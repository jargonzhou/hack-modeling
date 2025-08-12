%%%-------------------------------------------------------------------
%%% @author  zhoujiagen@gmail.com
%%% @copyright MIT
%%% @doc
%%% 
%%% @end
%%%-------------------------------------------------------------------


-module(test_binaries_bitsyntax).
-include("common.hrl").

%% ====================================================================
%% API functions
%% ====================================================================
-export([run/0]).

run() ->
  test_binaries_demo(),
  test_bit_syntax_demo(),
  test_bitstring_demo(),
  test_more_bit_syntax_demo()
.

%% ====================================================================
%% Internal functions
%% ====================================================================

% 二进制型示例
test_binaries_demo() ->
  A = <<5, 10, 12>>,
  B = <<"hello">>,
  C = <<65, 66, 67>>,
  ?INFO("A", A), ?INFO("B", B), ?INFO("C", C),

  % 列表转为二进制型
  Bin1 = <<1, 2, 3>>,
  Bin2 = <<4, 5>>,
  Bin3 = <<6>>,
  D = list_to_binary([Bin1, 1, [2, 3, Bin2], 4 | Bin3]),
  ?INFO("D", D)
.

% 位语法示例
% <<>>
% <<Ei, ...>>
% Ei为Value[:Size][/TypeSpecifierList]
test_bit_syntax_demo() ->
  Red = 2, Green = 61, Blue = 20,
  Mem = <<Red:5, Green:6, Blue:5>>,
  ?INFO("Mem", Mem),

  % 模式匹配
  <<R:5, G:6, B:5>> = Mem,
  ?INFO("R", R), ?INFO("G", G), ?INFO("B", B)
.

% 位串示例
test_bitstring_demo() ->
  B1 = <<1:8>>,
  ?INFO("B1", B1),
  ?INFO("byte_size(B1)", byte_size(B1)),
  ?INFO("is_binary(B1)", is_binary(B1)),
  ?INFO("is_bitstring(B1)", is_bitstring(B1)),

  B2 = <<1:17>>, % 位串长度不是8的整数倍
  ?INFO("B2", B2),
  ?INFO("byte_size(B2)", byte_size(B2)),
  ?INFO("is_binary(B2)", is_binary(B2)),
  ?INFO("is_bitstring(B2)", is_bitstring(B2)),

  % 位推导(bit comprehension)
  B = <<16#5f>>,
  BB = [X || <<X:1>> <= B], % 列表推导
  BBB = <<<<X>> || <<X:1>> <= B>>, % 位推导
  ?INFO("B", B), ?INFO("BB", BB), ?INFO("BBB", BBB)
.

test_more_bit_syntax_demo() ->
  Bin = <<16:8, 1:8, 0:3>>,
  ?INFO("Bin", Bin),

  <<A:1/integer-unit:8, B:1/integer-unit:8, C/bitstring>> = Bin,
  ?INFO("A", A), ?INFO("B", B), ?INFO("C", C),

  <<D:8/bitstring, E:1/bitstring, F/bitstring>> = Bin,
  ?INFO("D", D), ?INFO("E", E), ?INFO("F", F).
