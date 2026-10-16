(*  Title:      Apply_Inspect_Examples.thy

Examples for "apply_inspect". Open this theory in the Prover IDE and look at the output of the
apply_inspect commands. The theory is not part of the session in ROOT: it is meant to be read in
the Prover IDE, and its examples of time limits take a few seconds.
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
  If the method fails, the command lists the theorems that the method used before it gave up,
  with the attributes under which they are declared (e.g. \<open>[simp]\<close>) and how often they
  were used. It then continues with the goal state that the method reached last, as a skipped
  proof, and warns about it; only if the method got nowhere does the command fail like
  \<^theory_text>\<open>apply\<close>. Here \<^theory_text>\<open>fastforce\<close> rewrites with
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
  Infrastructure is left out of the report: theorems of Pure, class axioms (including class
  relations and arities, e.g. @{thm [source] arity_type_nat}), locale axioms, and theorems
  declared with the attribute @{attribute apply_inspect_hide}, such as
  @{thm [source] eq_reflection}. With @{attribute apply_inspect_show_infrastructure}, they are
  reported as well.
\<close>

lemma "length (xs @ ys) = length xs + length ys \<and> xs = ys"
  using [[apply_inspect_show_infrastructure]]
  apply_inspect fastforce
  oops

declare length_append [apply_inspect_hide]

lemma "length (xs @ ys) = length xs + length ys \<and> xs = ys"
  apply_inspect fastforce
  oops

declare length_append [apply_inspect_hide del]

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

  With a time limit (@{attribute apply_inspect_timeout}, in milliseconds), the method is stopped
  when the limit is reached, and the command shows the goal states that it reached on the way, as
  skipped proofs (like \<^theory_text>\<open>sorry\<close>): from @{attribute apply_inspect_trace_start}
  on (default 0), every @{attribute apply_inspect_trace_interval} milliseconds (default 100). The
  command shows the first of them, and each \<^theory_text>\<open>back\<close> the next one, up to the state
  at the time limit, with the theorems used since the previous one. All of them are declaration
  attributes, e.g. for a whole theory with
  \<^theory_text>\<open>declare [[apply_inspect_timeout = 1000]]\<close>. Here the classical reasoner applies
  @{thm Q_step} again and again: each \<^theory_text>\<open>back\<close> shows a larger goal.
\<close>

lemma "Q 0"
  using [[apply_inspect_timeout = 1000, apply_inspect_trace_start = 500,
    apply_inspect_trace_interval = 200]]
  apply_inspect (fast intro: Q_step)
  back
  back
  oops

text \<open>
  Each goal state is computed by running the method again and stopping it at the point that it
  had reached: the simplifier then returns the term that it has rewritten so far, so its progress
  shows within the goal state, also when it is called by another method, e.g.
  \<^theory_text>\<open>auto\<close>.
\<close>

axiomatization grow :: "nat \<Rightarrow> nat" where grow_Suc: "grow n = grow (Suc n)"

lemma "grow 0 = 1 \<and> Q 0"
  using [[apply_inspect_timeout = 500]]
  apply_inspect (auto simp add: grow_Suc)
  back
  back
  oops

text \<open>
  The goal state can be worked on as usual: here the two subgoals of @{thm conjI}, after a warning
  about the loop between @{thm f_g} and @{thm g_f}.
\<close>

lemma "f 0 = 1 \<and> Q 0"
  using [[apply_inspect_timeout = 1000]]
  apply_inspect (rule conjI, simp add: f_g g_f)
  txt \<open>For example, to look at the other subgoal.\<close>
  prefer 2
  apply (simp add: Q_def)
  oops

end
