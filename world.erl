-module(world).

% helpers to load/purge worlds
-export([
    world_init/0,
    world_add_module/3,
    world_purge_module/2
]).
% helpers to load/purge modules
-export([
    module_add_function_string/4, 
    module_add_function_AST/4, 
    module_purge_function/3
]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% World Specification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The World reprsenets the modules and functions the evaluator is aware of.
% world(): #{atom() => module()}
% module(): #{{atom(), integer()} => [ASTs]}

% Returns an empty world
world_init() -> #{}.

% Add a module to the given world.
world_add_module(World, ModuleName, Module) ->
    World#{ModuleName => Module}.

% Remove the given Module from the world.
world_purge_module(World, ModuleName) when is_map(World) ->
    maps:remove(ModuleName, World).

% Add the given function in string form to the module.
module_add_function_string(Module, FunctionName, 
    FunctionArity, FunctionString) when is_map(Module) ->
    {function, _, _, _, FunctionDef} = eval:get_AST_form(FunctionString),
    Module#{{FunctionName, FunctionArity} => FunctionDef}.

% Add the given function in AST form to the module.
module_add_function_AST(Module, FunctionName, FunctionArity, 
    {function, _, _, _, FunctionDef}) ->
    Module#{{FunctionName, FunctionArity} => FunctionDef};
module_add_function_AST(Module, FunctionName, 
    FunctionArity, FunctionDef) ->
    Module#{{FunctionName, FunctionArity} => FunctionDef}.

% Remove the function with the given name and arity from the module.
module_purge_function(Module, FunctionName, Arity) when is_map(Module) ->
    maps:remove({FunctionName, Arity}, Module).