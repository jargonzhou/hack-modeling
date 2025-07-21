% usage: c(<module>, {d, debug_flag}).
%% -ifdef(debug_flag).
%% -compile(export_all).
%% -define(DEBUG(Description, X), io:format("DEBUG ~p:~p ~p ~p~n", [?MODULE, ?LINE, Description, X])).
%% -else.
%% -define(DEBUG(Description, X), void).
%% -endif.

%% DEBUG output
-define(DEBUG(Description, X), 
		io:format("[DEBUG] ~-30w:~-4w ~p ~w~n", [?MODULE, ?LINE, Description, X])).

%% not yet implemented
-define(NYI(X), 
		(begin
			 io:format("*** NYI ~p ~p ~p~n", [?MODULE, ?LINE, X]),
			 exit(nyi)
		 end)).

%% output
-define(INFO(Name, R),
		io:format(
		  string:concat(string:concat("[INFO] ~p:~p ", Name), "=~p~n"), 
		  [?MODULE, ?LINE, R])).
-define(INFO(Description),
		io:format("[INFO] ~p:~p ~p~n", [?MODULE, ?LINE, Description])).
