(*  Title:      Apply_Inspect.thy

Diagnostic variant of "apply" that reports the theorems used during a
failed proof method application.
*)

theory Apply_Inspect
  imports Main
  keywords "apply_inspect" :: prf_script % "proof"
begin

ML_file \<open>apply_inspect.ML\<close>

end
