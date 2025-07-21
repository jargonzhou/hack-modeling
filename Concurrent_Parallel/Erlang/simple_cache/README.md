simple_cache
=====

An OTP application: Simple Cache System.

	├── simple_cache.erl		- 缓存API
	
	├── sc_app.erl				- (application)
	├── sc_sup.erl				- (supervisor)
	
	├── sc_element_sup.erl		- (supervisor)
	├── sc_element.erl			- (gen_server)
	
	├── sc_event.erl			- 缓存事件API
	├── sc_event_logger.erl		- 事件处理器(gen_event)


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
	1> application:start(simple_cache).
	ok
	# 观察应用中进程
	2> observer:start().
	ok
	
	# 模拟请求

	添加缓存
	> simple_cache:insert(hello, "hello").
	true
	查找缓存
	> simple_cache:lookup(hello2).
	{error,not_found}
	> simple_cache:lookup(hello). 
	删除缓存
	{ok,"hello"}
	> simple_cache:delete(hello).
	ok
	确认删除
	> simple_cache:lookup(hello).
	{error,not_found}
	
	注册事件处理器
	> sc_event_logger:add_handler().
	解注册事件处理器
	> sc_event_logger:delete_handler().
	
	模拟大量缓存值, 依赖参见https://hex.pm/packages/erlang_commons
	> erlang_commons:for(1, 1000, fun(I) -> simple_cache:insert(I,I) end).
	> erlang_commons:for(1, 1000, fun(I) -> simple_cache:delete(I) end).
