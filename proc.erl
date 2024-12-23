-module(proc).

-export([eval_main/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Eval with Processes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eval_main(_, _) ->
    {error, "Not implemented yet."}.

% eval_main(Processes, Scheduler)
% where Processes is #{Pid => Process}
%       Process is {Callstack, Status, Inbox}
%       Callstack is {AST, Bindings, World}
%       Status is one of ????
%       Inbox is [{Pid, MessageValue}]
%       returns {ok, Processes'}

% call scheduler
% deliver messages in scheduler's order
% call eval_proc with the scheduler's chosen process
% recurse until scheduler returns errot, deadlock or termination
% {ok, Processes'} | {dead, Processes'} | {error, ErrorMessage}

% eval_proc({AST, Bindings, World, Inbox}) -> 
% {ok, AST, Messages, Children} 

% calls to
% !
% self()   -> rturn self pid
% spawn() -> 
% receive -> pattern match from Inbox
% something to kill a process


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Scheduler
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Scheduler is fun(Processes, Network) -> Schedule
%  Schedule is #{deliver => Messages, run => Pid}
%  Messages is [{Pid, Pid}] ?? shouldn't the messages be included here
%  Network is ???


%%% Questions
%%% 
%%% Fun : {fun, Name}  store({{Name, Arity}, {{clauses, AST}, {bindings, Bindings}}}),
%%% 1 - do I even need arity since each fun already has a unique name
%%% 2 - maybe I should store a map: #{clauses => AST, bindings => Bindings}
%%% 
%%% %%% eval_main (Processes, Scheduler) -> {ok, Processes'} | {error, ErrorMessage}
%%%  
%%% I might have to change the return type of eval_expr
%%% from {ok, Value, Bindings} to {Status, Value, Bindings, World, Out}
%%% Status is 'ok' (terminated), 'yield' (reached a receive, Value would be the ASTs left), or 'error'
%%% 
%%% also maybe have an 'active' staus for processes that have not been run yet?
%%% 
%%% Status
%%% Network
%%% 
%%% How to represent a Pid {pid, integer()}?