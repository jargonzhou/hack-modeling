# 5 Records

```shell
➜  ch05 git:(main) ✗ dune utop
──────────────────────────────────────────────────────
lcome to utop version 2.14.0 (using OCaml version 5.2.
──────────────────────────────────────────────────────

Type #utop_help for help about using utop.

─( 18:02:27 )─< command 0 >──────────────────────────────────────{ counter: 0 }─
utop # parse_lines service_info_of_string
  "rtmp              1/ddp     # Routing Table Maintenance Protocol
   tcpmux            1/udp     # TCP Port Service Multiplexer
   tcpmux            1/tcp     # TCP Port Service Multiplexer";;
Error: Unbound value parse_lines
─( 18:02:27 )─< command 1 >──────────────────────────────────────{ counter: 0 }─
utop # open Ch05.Service_info;;
─( 18:02:57 )─< command 2 >──────────────────────────────────────{ counter: 0 }─
utop # parse_lines service_info_of_string
  "rtmp              1/ddp     # Routing Table Maintenance Protocol
   tcpmux            1/udp     # TCP Port Service Multiplexer
   tcpmux            1/tcp     # TCP Port Service Multiplexer";;
- : service_info with_line_num list =
[{item = {service_name = "rtmp"; port = 1; protocol = "ddp"}; line_num = 1};
 {item = {service_name = "tcpmux"; port = 1; protocol = "udp"}; line_num = 2};
 {item = {service_name = "tcpmux"; port = 1; protocol = "tcp"}; line_num = 3}]
─( 18:03:12 )─< command 3 >──────────────────────────────────────{ counter: 0 }─
utop # parse_lines Int.of_string "1\n10\n100\n1000";;
- : int with_line_num list =
[{item = 1; line_num = 1};
 {item = 10; line_num = 2};
 {item = 100; line_num = 3};
 {item = 1000; line_num = 4}]
─( 18:03:16 )─< command 4 >─{ cou
utop # 
```