# 2. The module system

- `fifo.ml`
```shell
# #use "fifo.ml";;
module Fifo :
  sig
    type 'a queue = { front : 'a list; rear : 'a list; }
    val make : 'a list -> 'a list -> 'a queue
    val empty : 'a queue
    val is_empty : 'a queue -> bool
    val add : 'a -> 'a queue -> 'a queue
    exception Empty
    val top : 'a queue -> 'a
    val pop : 'a queue -> 'a queue
  end
# Fifo.add "hello" Fifo.empty;;
- : string Fifo.queue = {Fifo.front = ["hello"]; rear = []}
# open Fifo;;
# add "hello" empty;;
- : string Fifo.queue = {front = ["hello"]; rear = []}
# let empty = []
  open Fifo;;
val empty : 'a list = []
# let x = 1 :: empty;;
Error: This expression has type 'a Fifo.queue
       but an expression was expected of type int list
```

TODO: restart from P.36
