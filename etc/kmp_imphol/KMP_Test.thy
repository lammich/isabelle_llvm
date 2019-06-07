theory KMP_Test
imports "Knuth_Morris_Pratt.KMP" "Native_Word.Uint8"
begin

find_consts "uint8 \<Rightarrow> nat"

instance uint8 :: heap apply standard apply (rule exI[where x=nat_of_uint8])
  apply transfer
  apply (auto simp: inj_def)
  done

definition "kmp_char8_impl \<equiv> kmp_impl :: (uint8 array \<times> nat) \<Rightarrow> _"

ML_val File.read
ML_val String.explode

ML_val \<open>open Time\<close>

ML_val \<open>open Array\<close>

ML_val \<open>open Word8Vector\<close>

ML_val \<open>Byte.bytesToString\<close>
ML_val \<open>Byte.bytesToString o BinIO.inputAll\<close>

ML_val \<open>
  fun vector arr = Vector.tabulate (Array.length arr, fn i => Array.sub (arr, i))
  fun array vec = Array.tabulate (Word8Vector.length vec, fn i => Word8Vector.sub (vec, i))
  val read_file = array o BinIO.inputAll

\<close>

ML_val \<open>(I : Word8Vector.elem -> Word8.word)\<close>

ML_val \<open>
  val string_to_word8array = Array.fromList o map (Word8.fromInt o Char.ord) o String.explode 

  fun string_to_arl s = (string_to_word8array s, @{code nat_of_integer} (String.size s))
  
  fun read_file name = let
    fun array vec = Array.tabulate (Word8Vector.length vec, fn i => Word8Vector.sub (vec, i))
    val f = BinIO.openIn name;
    val r = array (BinIO.inputAll f)
    val _ = BinIO.closeIn f
  in (r,@{code nat_of_integer} (Array.length r)) end
  
  fun kmp s t = @{code kmp_char8_impl} s t () |> map_option @{code integer_of_nat}
  
  val s = string_to_arl "nodes"
  val t = string_to_arl "od"
  val t = read_file "/home/lammich/MASC-3.0.0/data/spoken/court-transcript/Day3PMSession-ptb.xml"
  
  fun iterate 0 _ _ = ()
    | iterate n f x = (f x; iterate (n-1) f x)
  
  val start = Time.now ()
  
  val test1 = kmp s t
  
  val duration = Time.now() - start |> Time.toMilliseconds
  
  val _ = Int.toString duration
  
  
\<close>


export_code 
  kmp_char8_impl integer_of_nat nat_of_integer
  in SML_imp module_name KMP
  file "KMP_Code_Export.sml"


