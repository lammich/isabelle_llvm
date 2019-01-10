section \<open>Generic Block Allocator\<close>
theory Sep_Block_Allocator
imports Sep_Lift
begin

  text \<open>This theory specifies the concepts of memory allocation and deallocation.
    It is parameterized over the actual type of blocks.
  \<close>

  subsection \<open>Memory and Addresses\<close>

  text \<open>A memory is a list of allocated or already freed blocks.
    Allocated blocks are modeled by @{term \<open>Some blk\<close>}, 
    freed blocks are modeled by @{term \<open>None\<close>}
  \<close>  
  datatype 'blk memory = MEMORY (the_memory: "'blk option list")
  define_lenses memory

  text \<open>An address indexes a block, and then addresses into the value of this block.\<close>
  datatype 'baddr addr = ADDR nat 'baddr

  text \<open>A pointer is either \<open>null\<close>, or an address\<close>
  datatype 'addr rptr = RP_NULL | RP_ADDR (the_addr: "'addr")
  hide_const (open) the_addr

  text \<open>Type-class to model that there is a base address.\<close>  
  (* TODO: Remove from semantics, move to reasoning infrastructure? *)
  class this_addr = fixes this_addr :: 'a  
    
  text \<open>We immediately show that the typeclass is not empty. 
    This avoids confusion of the code generator with lemmas depending on this typeclass.\<close>
  typedecl this_addr_witness
  instantiation this_addr_witness :: this_addr begin
    instance ..
  end
  
  
  subsection \<open>Memory Functions\<close>
    
  text \<open>
    We specify the standard functions \<open>alloc\<close>, \<open>free\<close>, \<open>load\<close>, and \<open>store\<close>. 
    They are parameterized over load and store functions for blocks.
    
    Additionally, we specify a \<open>check_ptr\<close> function, that asserts that a pointer is valid,
    i.e., is either \<open>null\<close>, or points to an allocated block, and its block address is valid 
    for this block.
  \<close>
  
  locale block_allocator1 =
    fixes static_err :: 'err
      and mem_err :: 'err
      and bload :: "'baddr::this_addr \<Rightarrow> ('val,_,'block,'err) M"
      and bstore :: "'val \<Rightarrow> 'baddr \<Rightarrow> (unit,_,'block,'err) M"
      and bcheck_addr :: "'baddr \<Rightarrow> (unit,_,'block,'err) M"
  begin

    text \<open>Allocate a new block, and a pointer to its start\<close>
    definition alloc :: "'block \<Rightarrow> ('baddr addr rptr,_,'block memory,'err) M"
    where "alloc init \<equiv> zoom (lift_lens static_err the_memory\<^sub>L) (doM {
      blocks \<leftarrow> Monad.get;
      let bi = length blocks;
      let blocks = blocks @ [Some init];
      Monad.set blocks;
      return (RP_ADDR (ADDR bi this_addr))
    })"

    text \<open>Free a block, specified by a pointer to its start\<close>    
    definition free :: "'baddr addr rptr \<Rightarrow> (unit,_,'block memory,'err) M"
    where "free \<equiv> 
      \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> doM {
          fcheck mem_err (ba=this_addr);
          (* TODO: Use load here! *)
          let L = lift_lens static_err the_memory\<^sub>L \<bullet> (lift_lens mem_err (idx\<^sub>L bi));
          blk \<leftarrow> use L;
          fcheck mem_err (blk \<noteq> None);
          L ::= None
        } 
      | _ \<Rightarrow> fail mem_err"
      
    text \<open>We define a lens that focuses a block index. \<close>  
    (* TODO: Can we define lenses to focus addresses/pointers instead? *)
    definition "lens_of_bi bi \<equiv> the_memory\<^sub>L \<bullet>\<^sub>L idx\<^sub>L bi \<bullet>\<^sub>L the\<^sub>L"
    abbreviation "elens_of_bi bi \<equiv> lift_lens mem_err (lens_of_bi bi)"
    lemma lens_of_bi[simp, intro!]: "hlens (lens_of_bi bi)"
      unfolding lens_of_bi_def by auto
    
    text \<open>Load from an address\<close>  
    definition "load \<equiv> \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> zoom (elens_of_bi bi) (bload ba) | _ \<Rightarrow> fail mem_err"
    text \<open>Store at an address\<close>  
    definition "store \<equiv> \<lambda>x. \<lambda>RP_ADDR (ADDR bi ba) \<Rightarrow> zoom (elens_of_bi bi) (bstore x ba) | _ \<Rightarrow> fail mem_err"
    
    text \<open>Check that pointer is valid\<close>
    definition "check_ptr \<equiv> \<lambda>RP_NULL \<Rightarrow> return () | RP_ADDR (ADDR bi ba) \<Rightarrow> zoom (elens_of_bi bi) (bcheck_addr ba)"
    
    text \<open>The empty memory\<close>
    definition "empty_memory \<equiv> MEMORY []"
    
  end    

  subsection \<open>Isabelle Code Generator Setup\<close>
  text \<open>Setup to make the semantics executable inside Isabelle/HOL\<close>
  
  lemmas block_allocator1_code[code] =
    block_allocator1.alloc_def 
    block_allocator1.free_def
    block_allocator1.lens_of_bi_def
    block_allocator1.load_def
    block_allocator1.store_def
    block_allocator1.check_ptr_def
    block_allocator1.empty_memory_def
  
  
end
