section \<open>The LLVM Imperative Isabelle Collection Framework\<close>
theory IICF
imports 
  (* Sets *)
  "Intf/IICF_Set"

  (* Multisets *)
  "Intf/IICF_Multiset"
  "Intf/IICF_Prio_Bag"

  "Impl/Heaps/IICF_Impl_Heap"
  

  (* Maps *)
  "Intf/IICF_Map"
  "Intf/IICF_Prio_Map"

  "Impl/IICF_Array_Map"
  "Impl/IICF_Array_Map_Total"

  
  "Impl/Heaps/IICF_Impl_Heapmap"
    
  (* Lists *)
  "Intf/IICF_List"

  "Impl/IICF_Array"
  "Impl/IICF_Array_List"
  "Impl/IICF_Array_of_Array_List"
  (* Matrix *)
  (*"Intf/IICF_Matrix"*)


begin

subsection \<open>Regression Tests\<close>  
experiment
begin
  (* TODO: Augment! *)

  text \<open>Free parameter\<close>
  sepref_definition test_free1 is "\<lambda>xs. doN { 
    ASSERT(length xs = 10); 
    r \<leftarrow> mop_list_get xs 1;
    mop_free xs;
    RETURN r
  }" :: "(array_assn bool1_assn)\<^sup>d \<rightarrow>\<^sub>a bool1_assn"
    apply (annot_snat_const "TYPE(64)")
    by sepref

  
  text \<open>Free bound var before it goes out of scope\<close>
  sepref_definition test_free2 is "\<lambda>N. doN { 
    ASSERT(N>10); 
    xs \<leftarrow> mop_array_custom_replicate N False;
    xs \<leftarrow> mop_list_set xs 3 True;
    r1 \<leftarrow> mop_list_get xs 2;
    r2 \<leftarrow> mop_list_get xs 3;
    mop_free xs;
    xs \<leftarrow> mop_array_custom_replicate N False;
    RETURN (r1 \<and> r2) 
  }" :: "(snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    apply (annot_snat_const "TYPE(64)")
    by sepref
    
  text \<open>Free bound var + parameter\<close>
  sepref_definition test_free3 is "\<lambda>xs. doN { 
    ASSERT(length xs = 10); 
    xs2 \<leftarrow> mop_array_custom_replicate 10 False;
    xs2 \<leftarrow> mop_list_set xs2 3 True;
    r1 \<leftarrow> mop_list_get xs2 1;
    mop_free xs2;
    r2 \<leftarrow> mop_list_get xs 1;
    mop_free xs;
    RETURN (r1 \<and> r2) 
  }" :: "(array_assn bool1_assn)\<^sup>d \<rightarrow>\<^sub>a bool1_assn"
    apply (annot_snat_const "TYPE(64)")
    by sepref
  


end



end
