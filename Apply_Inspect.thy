(*  Title:      Apply_Inspect.thy

Diagnostic variant of "apply" that reports the theorems used during a
failed proof method application.
*)

theory Apply_Inspect
  imports Main
  keywords "apply_inspect" :: prf_script % "proof"
begin

ML_file \<open>apply_inspect.ML\<close>

declare eq_reflection [apply_inspect_hide] and TrueI [apply_inspect_hide]
  and Eq_TrueI [apply_inspect_hide] and Eq_FalseI [apply_inspect_hide]
  and simp_thms [apply_inspect_hide]

end
