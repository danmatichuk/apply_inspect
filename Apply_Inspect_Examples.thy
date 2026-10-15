(*  Title:      Apply_Inspect_Examples.thy

Examples for "apply_inspect". Open this theory in the Prover IDE and look at the output of the
apply_inspect commands. The examples of failing methods are errors on purpose, so the theory is
not part of the session in ROOT.
*)

theory Apply_Inspect_Examples
  imports Apply_Inspect
begin

section \<open>Successful methods\<close>

text \<open>
  If the method succeeds, \<^theory_text>\<open>apply_inspect\<close> behaves like \<^theory_text>\<open>apply\<close>.
\<close>

lemma "rev (rev xs) = xs \<and> xs @ [] = xs"
  apply_inspect (rule conjI)
   apply_inspect simp
  apply_inspect simp
  done


section \<open>Failed methods\<close>

text \<open>
  If the method fails, the command fails like \<^theory_text>\<open>apply\<close>, but it first lists the
  theorems that the method used before it gave up, with the attributes under which they are
  declared (e.g. \<open>[simp]\<close>). Here \<^theory_text>\<open>fastforce\<close> rewrites with
  @{thm length_append} but cannot prove \<open>xs = ys\<close>.
\<close>

lemma "length (xs @ ys) = length xs + length ys \<and> xs = ys"
  apply_inspect fastforce
  oops

text \<open>
  Facts and assumptions of the proof context are reported as such, e.g. the assumption \<open>P\<close>
  and the fact \<open>nonzero\<close> here.
\<close>

lemma
  fixes h :: "nat \<Rightarrow> nat"
  assumes P: "h x < h y"
  shows "h x < h y \<and> h y \<noteq> h x \<and> x = 0"
proof -
  have nonzero: "h y \<noteq> h x" using P by simp
  show ?thesis
    apply_inspect (fastforce simp: P nonzero)
    oops


subsection \<open>Filtering the report\<close>

text \<open>
  A list of @{command find_theorems} criteria in brackets restricts the report to the theorems
  that meet them.
\<close>

lemma "length (xs @ ys) = length xs + length ys \<and> xs = ys"
  apply_inspect [name: List] fastforce
  oops

text \<open>
  By default, each theorem is reported once. With @{attribute apply_inspect_every_use}, every use
  is reported as it happens, here both uses of @{thm conjI}.
\<close>

lemma "((xs::nat list) = ys \<and> ys = zs) \<and> zs = xs"
  using [[apply_inspect_every_use]]
  apply_inspect (rule conjI, rule conjI, fail)
  oops


section \<open>Methods that do not terminate\<close>

definition f :: "nat \<Rightarrow> nat" where "f x = x"
definition g :: "nat \<Rightarrow> nat" where "g x = x"

lemma f_g: "f x = g x" and g_f: "g x = f x"
  by (simp_all add: f_def g_def)

definition Q :: "nat \<Rightarrow> bool" where "Q n \<longleftrightarrow> True"

lemma Q_step: "Q (Suc n) \<Longrightarrow> Q n"
  by (simp add: Q_def)

text \<open>
  Theorems are reported as they are used, so a method that does not terminate still shows what
  it is doing. If the simplifier, the classical reasoner or a repeated method keeps applying the
  same rules, a warning names them.

  With a time limit (@{attribute apply_inspect_timeout}, in milliseconds), the method is paused
  when the limit is reached, and the command continues with the goal state that the method has
  reached, as a skipped proof (like \<^theory_text>\<open>sorry\<close>). Each \<^theory_text>\<open>back\<close> continues
  the method for another @{attribute apply_inspect_step_time} milliseconds (default 100),
  lists the theorems used in that step, and shows the goal state that it has reached then.
  Both are declaration attributes, e.g. for a whole theory with
  \<^theory_text>\<open>declare [[apply_inspect_timeout = 1000]]\<close>. Here the classical reasoner applies
  @{thm Q_step} again and again: each \<^theory_text>\<open>back\<close> shows a larger goal.
\<close>

lemma "Q 0"
  using [[apply_inspect_timeout = 1000, apply_inspect_step_time = 200]]
  apply_inspect (fast intro: Q_step)
  back
  back
  oops

text \<open>
  The method pauses only where it calls the instrumentation (method and classical steps,
  rewrites, simprocs), and the goal state is the one after its last method or classical step. A
  looping simplifier is paused in the middle of its work, so the goal state is the one before it
  was called: here the two subgoals of @{thm conjI}, and a warning about the loop between
  @{thm f_g} and @{thm g_f}.
\<close>

lemma "f 0 = 1 \<and> Q 0"
  using [[apply_inspect_timeout = 1000]]
  apply_inspect (rule conjI, simp add: f_g g_f)
  txt \<open>The goal state can be worked on as usual, e.g. to look at the other subgoal.\<close>
  prefer 2
  apply (simp add: Q_def)
  oops

end
