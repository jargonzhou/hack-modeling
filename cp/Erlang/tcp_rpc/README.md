tcp_rpc
=====

An OTP application: TCP RPC.

	├── tr_app.erl				- (application)
	├── tr_sup.erl				- (supervisor)
	├── tr_server.erl			- (gen_server)


Build
-----

    # 编译
    $ rebar3 compile
    
    # 查看
    $ rebar3 deps
    
Run
-----
	
	$ rebar3 shell
	# 启动应用
	1> application:start(tcp_rpc).
	ok
	# 观察应用中进程
	2> observer:start().
	ok
	
	# 模拟请求
	$ telnet localhost 1055
	io:format("~p~n", ["Hello, world!"]).
	init:stop().
	