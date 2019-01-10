theory Main_Simpset
imports Main
begin

  ML \<open>
    val HOL_Main_ss = simpset_of @{context}
    
    val onlyMain_mod =  Args.$$$ "only_main" -- Args.colon >>
    K {init = Raw_Simplifier.put_simpset HOL_Main_ss, attribute = Simplifier.simp_add, pos = \<^here>}
  \<close>

  (* TODO/FIXME/XXX: Is this the intended way how to add an attribute to simp?*)
  setup "Simplifier.method_setup (onlyMain_mod :: Splitter.split_modifiers)"
  
end
