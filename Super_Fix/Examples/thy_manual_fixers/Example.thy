theory Example  
  imports 
    Complex_Main
    Super_Fix.Super_Fix
begin

ML \<open>
val read_thy_path = "/path/to/this/repo/Super_Fix/Examples/thys_with_errors/Example.thy";
val write_thy_name = "Example.thy";
val write_dir = "/path/to/this/repo/Super_Fix/Examples/thy_manual_fixed/";
Fixer.fix_end_to_end {strategy="sledgehammer"} \<^theory> read_thy_path write_thy_name write_dir
\<close>

end