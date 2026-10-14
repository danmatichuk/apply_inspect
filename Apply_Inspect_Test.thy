theory Apply_Inspect_Test
  imports Apply_Inspect
begin

ML \<open>
(*run a method given as source text on the current proof state, without changing it*)
fun inspect_test state src =
  let
    val proof_state = Toplevel.proof_of state;
    val ctxt = Proof.context_of proof_state;
    val (text, _) = Method.read_closure_input ctxt (Input.string src);
    val {succeeded, deps} = Apply_Inspect.inspect (K ()) text proof_state;
    val _ = Pretty.writeln (Apply_Inspect.pretty_deps ctxt deps);
  in (succeeded, map (#1 o #1) deps) end;

fun expect_failed_with state src names =
  let val (succeeded, deps) = inspect_test state src in
    if succeeded then error ("Method succeeded: " ^ src)
    else
      (case filter_out (member (op =) deps) names of
        [] => ()
      | missing => error ("Missing dependencies for " ^ src ^ ": " ^ commas missing))
  end;
\<close>

definition P :: "nat \<Rightarrow> bool" where "P x \<longleftrightarrow> x > 0"

lemma P_nonzero: "P x \<Longrightarrow> x \<noteq> 0"
  by (simp add: P_def)

lemma Q_rev: "rev (rev xs) = xs"
  by simp


text \<open>Success: behaves like \<^theory_text>\<open>apply\<close>.\<close>

lemma "rev (rev xs) = xs \<and> xs @ [] = xs"
  apply_inspect (rule conjI)
   apply_inspect simp
  apply_inspect simp
  done


text \<open>Failure at the end of a sequence of methods.\<close>

lemma "rev (rev xs) = xs \<and> xs = ys"
  ML_val \<open>expect_failed_with @{Isar.state} "(rule conjI, simp only: Q_rev, blast)"
    ["HOL.conjI", "Apply_Inspect_Test.Q_rev"]\<close>
  oops


text \<open>Failure within the search of the classical reasoner.\<close>

lemma "length (xs @ ys) = length xs + length ys \<and> xs = ys"
  ML_val \<open>expect_failed_with @{Isar.state} "fastforce" ["List.length_append"]\<close>
  ML_val \<open>expect_failed_with @{Isar.state} "force" ["List.length_append"]\<close>
  oops

lemma "P x \<Longrightarrow> x \<noteq> 0 \<and> x = y"
  ML_val \<open>expect_failed_with @{Isar.state} "(fastforce dest: P_nonzero)"
    ["Apply_Inspect_Test.P_nonzero"]\<close>
  ML_val \<open>expect_failed_with @{Isar.state} "(fast dest: P_nonzero)"
    ["Apply_Inspect_Test.P_nonzero"]\<close>
  oops


text \<open>Theorems are reported as they are used, even if the method does not terminate.\<close>

axiomatization Q :: "nat \<Rightarrow> bool" where Q_step: "Q (Suc n) \<Longrightarrow> Q n"

lemma "Q 0"
  ML_val \<open>
    let
      val state = Toplevel.proof_of @{Isar.state};
      val (text, _) =
        Method.read_closure_input (Proof.context_of state) (Input.string "(fast intro: Q_step)");
      val used = Synchronized.var "used" [];
      fun on_use (thm_name, _) = Synchronized.change used (cons (#1 thm_name));
      val _ =
        (Timeout.apply (seconds 2.0) (Apply_Inspect.inspect on_use text) state;
          error "Method terminated")
        handle Timeout.TIMEOUT _ => ();
    in
      if member (op =) (Synchronized.value used) "Apply_Inspect_Test.Q_step" then ()
      else error "Q_step not reported before timeout"
    end\<close>
  oops


text \<open>Rewrite rules are reported as they are tried, even if the simplifier loops.\<close>

axiomatization f g :: "nat \<Rightarrow> nat" where f_g: "f x = g x" and g_f: "g x = f x"

lemma "f 0 = 1"
  ML_val \<open>
    let
      val state = Toplevel.proof_of @{Isar.state};
      val (text, _) =
        Method.read_closure_input (Proof.context_of state) (Input.string "(simp add: f_g g_f)");
      val used = Synchronized.var "used" [];
      fun on_use (thm_name, _) = Synchronized.change used (cons (#1 thm_name));
      val _ =
        (Timeout.apply (seconds 2.0) (Apply_Inspect.inspect on_use text) state;
          error "Method terminated")
        handle Timeout.TIMEOUT _ => ();
    in
      (case filter_out (member (op =) (Synchronized.value used))
          ["Apply_Inspect_Test.f_g", "Apply_Inspect_Test.g_f"] of
        [] => ()
      | missing => error ("Not reported before timeout: " ^ commas missing))
    end\<close>
  oops

axiomatization h :: "nat \<Rightarrow> nat" where h_cond: "Q x \<Longrightarrow> h x = 0"

lemma "h y = 0"
  ML_val \<open>expect_failed_with @{Isar.state} "(simp add: h_cond)"
    ["Apply_Inspect_Test.h_cond"]\<close>
  oops


text \<open>Local contexts and nested goals.\<close>

context
  fixes z :: nat
  assumes z: "z = f 0"
begin

lemma "z = 1"
  ML_val \<open>expect_failed_with @{Isar.state} "(simp add: z f_g, fail)" ["Apply_Inspect_Test.f_g"]\<close>
  oops

lemma "z = g 0 \<and> rev (rev xs) = xs"
proof -
  have "h z = 0 \<or> True"
    ML_val \<open>expect_failed_with @{Isar.state} "(rule disjI1, simp add: h_cond)"
      ["Apply_Inspect_Test.h_cond"]\<close>
    apply_inspect simp
    done
  show ?thesis
    apply_inspect (simp add: z f_g)
    done
qed

end


text \<open>Dependencies of the goal state itself are not reported.\<close>

lemma "xs = ys \<and> rev (rev xs) = xs"
  apply (rule conjI)
  ML_val \<open>
    let val (succeeded, deps) = inspect_test @{Isar.state} "(rule Q_rev)" in
      if succeeded orelse member (op =) deps "HOL.conjI" then error "Bad result" else ()
    end\<close>
  oops

end
