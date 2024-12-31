-module(world).

% helpers to load/purge worlds
-export([world_init/0, local_module/0, world_add_module/3, world_purge_module/2]).
% helpers to load/purge modules
-export([module_add_function_string/4, module_add_function_AST/4, module_purge_function/3]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% World Specification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% World is a map Mod_Atom -> Module_Map
% Module_Map is map {Fun_Atom, Arity} -> FunDefForm
% FunDefForm is the AST returned by erl_pare:parse_form()

% returns a world with the local module that contains built in erlang functions
% TODO : purpose statement

local_module() ->
    Local_Module_temp1 = module_add_function_string(#{}, is_integer, 1,
        "is_integer(X) -> try X =:= X div 1 catch error:E -> false end."),
    Local_Module_temp2 = module_add_function_string(Local_Module_temp1, hd, 1,
        "hd([Hd | Tl]) -> Hd."),
    module_add_function_string(Local_Module_temp2, tl, 1,
        "tl([Hd | Tl]) -> Tl.").
world_init() -> #{local => local_module()}.


% Add a binding from the name to the module into the world.
world_add_module(World, Module_Name, Module) ->
    New_World = World#{Module_Name => Module},
    New_World.

% Remove the module with the given name from the world
world_purge_module(World, Module_Name) when is_map(World) ->
    New_World = maps:remove(Module_Name, World),
    New_World.

% Add the function description described by the String to to the module.
module_add_function_string(Module, Function_Name, Function_Arity, Function_String) when is_map(Module) ->
    {function, _, _, _, Function_Def} = eval:get_AST_form(Function_String),
    New_Module = Module#{{Function_Name, Function_Arity} => Function_Def},
    New_Module.

% Add the function description described by the AST to the module.
module_add_function_AST(Module, Function_Name, Function_Arity, {function, _, _, _, Function_Def}) ->
    New_Module = Module#{{Function_Name, Function_Arity} => Function_Def},
    New_Module;
module_add_function_AST(Module, Function_Name, Function_Arity, Function_Def) ->
    New_Module = Module#{{Function_Name, Function_Arity} => Function_Def},
    New_Module.

% Remove the function with the given name and arity from the module.
module_purge_function(Module, Function_Name, Arity) when is_map(Module) ->
    New_Module = maps:remove({Function_Name, Arity}, Module),
    New_Module.