Code of Programming Erlang

1. Introducing Concurrency
2. A Whirlwind Tour of Erlang
3. Basic Concepts
4. Modules and Functions
5. Records and Maps
6. Error Handling in Sequential Programs
7. Binaries and the Bit Syntax
8. The Rest of Sequential Erlang
9. Types
10. Compiling and Running Your Program
11. Real-World Concurrency
12. Concurrent Programming
13. Errors in Concurrent Programs
14. Distributed Programming
15. Interfacing Techniques
16. Programming with Files
17. Programming with Sockets
18. Browsing with Websockets and Erlang
19. Storing Data with ETS and DETS
20. Mnesia: The Erlang Database
21. Profiling, Debugging, and Tracing
22. Introducing OTP
23. Making a System with OTP
24. Programming Idioms
25. Third-Party Programs
26. Programming Multicore CPUs
27. Sherlock’s Last Case


1. Cannot run in IDEA

message:

/usr/local/Cellar/erlang/25.1.1/lib/erlang/bin/erl -pa /Users/zhang/workspace/gitlab/snippets/codes/erlang/prog-erlang/out/test/prog-erlang -pa /Users/zhang/workspace/gitlab/snippets/codes/erlang/prog-erlang -eval hello:start(). -s init stop -noshell
init terminating in do_boot ({undef,[{hello,start,[],[]},{erl_eval,do_apply,7,[{_},{_}]},{init,start_it,1,[]},{init,start_em,1,[]},{init,do_boot,3,[]}]})

Crash dump is being written to: erl_crash.dump...{"init terminating in do_boot",{undef,[{hello,start,[],[]},{erl_eval,do_apply,7,[{file,"erl_eval.erl"},{line,744}]},{init,start_it,1,[]},{init,start_em,1,[]},{init,do_boot,3,[]}]}}
done

solution:

'Build' -> 'Build Project'
Remove 'Build' from 'Before launch' in 'Run/Debug Configuration'
