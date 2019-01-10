section \<open>Array-Blocks\<close>
theory Sep_Array_Block
imports Sep_Lift Sep_Block_Allocator
begin

text \<open>This theory specifies the concept of blocks that are arrays of values. 
  It is parameterized over values.
\<close>

subsection \<open>Blocks and Block Addresses\<close>

text \<open>A block is modeled as list of values\<close>
type_synonym 'val block = "'val list" 

text \<open>An address into a block is an index into the list, and an address into the value.
  Note that, for technical reasons, we model the index into the list by an integer, instead of a 
  nat.\<close>
datatype 'vaddr baddr = BADDR int 'vaddr
(* TODO: Can we use nat here? *)


text \<open>The base address of a block points to its first index.\<close>
instantiation baddr :: (this_addr) this_addr begin
  definition "this_addr \<equiv> BADDR 0 this_addr"
  instance ..
end

subsection \<open>Memory and Pointer Operations\<close>

locale array_block1 =
  fixes static_err :: 'err
    and mem_err :: 'err
    and vload :: "'vaddr::this_addr \<Rightarrow> ('val,_,'val,'err) M"
    and vstore :: "'val \<Rightarrow> 'vaddr \<Rightarrow> (unit,_,'val,'err) M"
    and vgep :: "'vaddr \<Rightarrow> 'vidx \<Rightarrow> ('vaddr,_,'val,'err) M"
begin
  definition load :: "'vaddr baddr \<Rightarrow> ('val,_,'val block,'err) M" where
    "load \<equiv> \<lambda>BADDR i va \<Rightarrow> fcheck mem_err (i\<ge>0) \<then> zoom (lift_lens mem_err (idx\<^sub>L (nat i))) (vload va)"

  definition store :: "'val \<Rightarrow> 'vaddr baddr \<Rightarrow> (unit,_,'val block,'err) M" where
    "store \<equiv> \<lambda>x. \<lambda>BADDR i va \<Rightarrow> fcheck mem_err (i\<ge>0) \<then> zoom (lift_lens mem_err (idx\<^sub>L (nat i))) (vstore x va)" 

  text \<open>Check that a block address is in range, i.e., at most one past the end of the actual block.\<close>
  definition check_addr :: "'vaddr baddr \<Rightarrow> (unit,_,'val block,'err) M" where
    "check_addr \<equiv> \<lambda>BADDR i va \<Rightarrow> doM {blk\<leftarrow>Monad.get; fcheck mem_err (0\<le>i \<and> i\<le>int (length blk))}"

  text \<open>Index (offset) an address. It must point to the start of a value.\<close>  
  definition checked_idx_baddr :: "'vaddr baddr \<Rightarrow> int \<Rightarrow> ('vaddr baddr, _, 'val list, 'err) M" where 
  "checked_idx_baddr \<equiv> \<lambda>BADDR i va \<Rightarrow> \<lambda>j. doM {
    fcheck mem_err (va = this_addr);
    let r = BADDR (i+j) va;
    check_addr r;
    return r
  }"

  text \<open>Advance an address into the structure of a value.\<close>
  definition checked_gep_addr :: "'vaddr baddr \<Rightarrow> 'vidx \<Rightarrow> ('vaddr baddr, _, 'val list, 'err) M"
    where
    "checked_gep_addr \<equiv> \<lambda>BADDR i va \<Rightarrow> \<lambda>vi. doM {
      fcheck mem_err  (i\<ge>0);
      va \<leftarrow> zoom (lift_lens mem_err (idx\<^sub>L (nat i))) (vgep va vi); 
      return (BADDR i va)
      }"
    
          
  subsection \<open>Lifting of Pointer Operations to Block Allocator\<close>
      
  sublocale ba: block_allocator1 static_err mem_err load store check_addr .
  
  definition init :: "'val \<Rightarrow> nat \<Rightarrow> 'val list" where "init v n \<equiv> replicate n v"
     

  definition "ba_allocn v n \<equiv> ba.alloc (init v n)"
  
  definition "checked_idx_ptr \<equiv> 
    \<lambda>RP_NULL \<Rightarrow> \<lambda>_. fail mem_err 
  | RP_ADDR (ADDR bi ba) \<Rightarrow> \<lambda>i. zoom (ba.elens_of_bi bi) (doM { ba\<leftarrow>checked_idx_baddr ba i; return (RP_ADDR (ADDR bi ba))})"

  definition "checked_gep_ptr \<equiv> 
    \<lambda>RP_NULL \<Rightarrow> \<lambda>_. fail mem_err 
  | RP_ADDR (ADDR bi ba) \<Rightarrow> \<lambda>vi. zoom (ba.elens_of_bi bi) (doM { ba\<leftarrow>checked_gep_addr ba vi; return (RP_ADDR (ADDR bi ba))})
  "
    
    
end


subsection \<open>Isabelle Code Generator Setup\<close>

lemmas array_block1_code[code] = 
  array_block1.load_def 
  array_block1.store_def
  array_block1.check_addr_def
  array_block1.checked_idx_baddr_def
  
  array_block1.checked_gep_addr_def
  array_block1.init_def
  array_block1.ba_allocn_def
  array_block1.checked_idx_ptr_def
  array_block1.checked_gep_ptr_def

end

