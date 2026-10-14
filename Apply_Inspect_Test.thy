theory Apply_Inspect_Test
  imports Apply_Inspect Apply_Inspect_Unrelated
begin

ML \<open>
fun use_name (Apply_Inspect.Theorem ((name, _), _)) = name
  | use_name (Apply_Inspect.Fact thm_name) = "fact " ^ Thm_Name.print thm_name
  | use_name (Apply_Inspect.Assumption (thm_name, _)) = "assumption " ^ Thm_Name.print thm_name
  | use_name (Apply_Inspect.Rule _) = "rule";

(*run a method given as source text on the current proof state, without changing it*)
fun inspect_test state src =
  let
    val proof_state = Toplevel.proof_of state;
    val ctxt = Proof.context_of proof_state;
    val (text, _) = Method.read_closure_input ctxt (Input.string src);
    val params = {every_use = false, on_use = K (K ()), on_loop = K (K ())};
    val {succeeded, uses, ...} = Apply_Inspect.inspect params text proof_state;
    val _ = Pretty.writeln (Apply_Inspect.pretty_uses ctxt uses);
  in (succeeded, map use_name uses) end;

(*number of times each theorem is reported, in the given mode*)
fun count_uses every_use state src =
  let
    val proof_state = Toplevel.proof_of state;
    val (text, _) = Method.read_closure_input (Proof.context_of proof_state) (Input.string src);
    val used = Synchronized.var "used" [];
    fun on_use _ u = Synchronized.change used (cons (use_name u));
    val params = {every_use = every_use, on_use = on_use, on_loop = K (K ())};
    val _ = Apply_Inspect.inspect params text proof_state;
  in fn name => length (filter (equal name) (Synchronized.value used)) end;

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
      fun on_use _ u = Synchronized.change used (cons (use_name u));
      val params = {every_use = false, on_use = on_use, on_loop = K (K ())};
      val _ =
        (Timeout.apply (seconds 0.5) (Apply_Inspect.inspect params text) state;
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
      fun on_use _ u = Synchronized.change used (cons (use_name u));
      val params = {every_use = false, on_use = on_use, on_loop = K (K ())};
      val _ =
        (Timeout.apply (seconds 0.5) (Apply_Inspect.inspect params text) state;
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
  ML_val \<open>expect_failed_with @{Isar.state} "(simp add: z f_g, fail)"
    ["Apply_Inspect_Test.f_g", "assumption local.z"]\<close>
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


text \<open>Every use of a theorem can be reported, not just the first one.\<close>

lemma "((xs::nat list) = ys \<and> ys = zs) \<and> zs = xs"
  ML_val \<open>
    let
      fun counts src =
        (count_uses false @{Isar.state} src "HOL.conjI",
          count_uses true @{Isar.state} src "HOL.conjI");
      val sequential = counts "(rule conjI, rule conjI, fail)";
      val branches = counts "((rule conjI, fail) | (rule conjI, fail))";
    in
      (case (sequential, branches) of
        ((1, 2), (1, 2)) => ()
      | ((a, b), (c, d)) => error ("Bad counts: " ^ commas (map string_of_int [a, b, c, d])))
    end\<close>
  oops

lemma "Q 0"
  ML_val \<open>
    let
      val state = Toplevel.proof_of @{Isar.state};
      val (text, _) =
        Method.read_closure_input (Proof.context_of state) (Input.string "(fast intro: Q_step)");
      val used = Synchronized.var "used" [];
      fun on_use _ u = Synchronized.change used (cons (use_name u));
      val params = {every_use = true, on_use = on_use, on_loop = K (K ())};
      val _ =
        (Timeout.apply (seconds 0.5) (Apply_Inspect.inspect params text) state;
          error "Method terminated")
        handle Timeout.TIMEOUT _ => ();
      val n = length (filter (equal "Apply_Inspect_Test.Q_step") (Synchronized.value used));
    in if n >= 10 then () else error ("Too few uses of Q_step: " ^ string_of_int n) end\<close>
  oops

lemma "rev (rev (rev (rev xs))) = ys"
  ML_val \<open>
    let
      val src = "(simp only: rev_rev_ident, fail)";
      val first = count_uses false @{Isar.state} src "List.rev_rev_ident";
      val every = count_uses true @{Isar.state} src "List.rev_rev_ident";
    in
      if first = 1 andalso every >= 2 then ()
      else error ("Bad counts: " ^ string_of_int first ^ ", " ^ string_of_int every)
    end\<close>
  oops


text \<open>Suspected simplifier loops are reported while the method runs.\<close>

ML \<open>
(*rules reported as looping before the timeout, or NONE if the method terminated*)
fun loop_rules state src =
  let
    val proof_state = Toplevel.proof_of state;
    val (text, _) = Method.read_closure_input (Proof.context_of proof_state) (Input.string src);
    val loops = Synchronized.var "loops" [];
    fun on_loop _ rules = Synchronized.change loops (cons (map use_name rules));
    val params = {every_use = false, on_use = K (K ()), on_loop = on_loop};
  in
    (Timeout.apply (seconds 0.5) (Apply_Inspect.inspect params text) proof_state; NONE)
      handle Timeout.TIMEOUT _ => SOME (Synchronized.value loops)
  end;

fun expect_loop state src names =
  (case loop_rules state src of
    NONE => error "Method terminated"
  | SOME [] => error "No loop reported"
  | SOME (rules :: _) =>
      if eq_set (op =) (rules, names) then ()
      else error ("Bad loop report: " ^ commas (map quote rules)));
\<close>

lemma "f 0 = 1"
  ML_val \<open>expect_loop @{Isar.state} "(simp add: f_g g_f)"
    ["Apply_Inspect_Test.f_g", "Apply_Inspect_Test.g_f"]\<close>
  oops

axiomatization k :: "nat \<Rightarrow> nat" where k_Suc: "k n = k (Suc n)"

lemma "k 0 = 1"
  ML_val \<open>expect_loop @{Isar.state} "(simp add: k_Suc)" ["Apply_Inspect_Test.k_Suc"]\<close>
  oops

lemma "f x = g x \<Longrightarrow> g x = f x \<Longrightarrow> f x = 0"
  ML_val \<open>expect_loop @{Isar.state} "(simp (no_asm_simp))" ["rule"]\<close>
  oops

ML \<open>
fun expect_no_loop state src =
  let
    val proof_state = Toplevel.proof_of state;
    val (text, _) = Method.read_closure_input (Proof.context_of proof_state) (Input.string src);
    val loops = Synchronized.var "loops" [];
    fun on_loop _ rules = Synchronized.change loops (cons (map use_name rules));
    val params = {every_use = false, on_use = K (K ()), on_loop = on_loop};
    val {succeeded, ...} = Apply_Inspect.inspect params text proof_state;
  in
    if not succeeded then error "Method failed"
    else if not (null (Synchronized.value loops)) then
      error ("False loop report: " ^ commas (map commas (Synchronized.value loops)))
    else ()
  end;
\<close>

lemma "length [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
      x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24] = 24 \<and>
    map Suc [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
      x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24] \<noteq> []"
  ML_val \<open>expect_no_loop @{Isar.state} "simp"\<close>
  oops


text \<open>Suspected loops of classical search and of repeated proof methods.\<close>

ML \<open>
fun expect_step_loop state src source names =
  let
    val proof_state = Toplevel.proof_of state;
    val (text, _) = Method.read_closure_input (Proof.context_of proof_state) (Input.string src);
    val loops = Synchronized.var "loops" [];
    fun on_loop source' rules =
      Synchronized.change loops (cons (source', map use_name rules));
    val params = {every_use = false, on_use = K (K ()), on_loop = on_loop};
    val terminated =
      (Timeout.apply (seconds 0.5) (Apply_Inspect.inspect params text) proof_state; true)
        handle Timeout.TIMEOUT _ => false;
  in
    if terminated then error "Method terminated"
    else
      (case AList.lookup (op =) (Synchronized.value loops) source of
        NONE =>
          error ("No loop reported for " ^ source ^ ", only for: " ^
            commas (map #1 (Synchronized.value loops)))
      | SOME rules =>
          if eq_set (op =) (rules, names) then ()
          else error ("Bad loop report: " ^ commas (map quote rules)))
  end;
\<close>

lemma "Q 0"
  ML_val \<open>expect_step_loop @{Isar.state} "(fast intro: Q_step)" "classical"
    ["Apply_Inspect_Test.Q_step"]\<close>
  ML_val \<open>expect_step_loop @{Isar.state} "(rule Q_step)+" "rule"
    ["Apply_Inspect_Test.Q_step"]\<close>
  oops

axiomatization R :: "nat \<Rightarrow> nat \<Rightarrow> bool" where R_sym: "R x y \<Longrightarrow> R y x"

lemma "R 0 1"
  ML_val \<open>expect_step_loop @{Isar.state} "(fast intro: R_sym)" "classical"
    ["Apply_Inspect_Test.R_sym"]\<close>
  oops

lemma "(2::nat) ^ 20 = 1048576"
  ML_val \<open>expect_no_loop @{Isar.state} "simp"\<close>
  oops

lemma "sum_list [1..<30] = (435::nat)"
  ML_val \<open>expect_no_loop @{Isar.state} "(simp add: upt_rec)"\<close>
  oops

lemma "rev (rev (rev (rev (rev (rev (rev (rev (rev (rev (rev (rev (rev (rev (rev (rev (rev (rev
    (rev (rev (rev (rev (rev (rev xs))))))))))))))))))))))) = xs"
  ML_val \<open>expect_no_loop @{Isar.state} "simp"\<close>
  oops


text \<open>Assumptions of the proof context are reported as such.\<close>

lemma
  assumes a: "P x" and b: "x = y"
  shows "x \<noteq> 0 \<and> x = y \<and> x = z"
  ML_val \<open>
    let
      val prefix = "rule conjI, rule P_nonzero, rule a, rule conjI, ";
      (*assumptions are hypotheses, which form a set: reported once per branch*)
      val same_branch = "(" ^ prefix ^ "rule b, rule b, fail)";
      val two_branches = "(" ^ prefix ^ "((rule b, fail) | (rule b, fail)))";
      fun counts src =
        (count_uses false @{Isar.state} src "assumption local.b",
          count_uses true @{Isar.state} src "assumption local.b");
      val (_, uses) = inspect_test @{Isar.state} same_branch;
    in
      (case (counts same_branch, counts two_branches) of
        ((1, 1), (1, 2)) =>
          if member (op =) uses "assumption local.a" then ()
          else error ("Missing assumption a: " ^ commas uses)
      | ((a, b), (c, d)) => error ("Bad counts: " ^ commas (map string_of_int [a, b, c, d])))
    end\<close>
  oops

lemma
  assumes step: "\<And>n. Q (Suc n) \<Longrightarrow> Q n"
  shows "Q 0"
  ML_val \<open>expect_step_loop @{Isar.state} "(fast intro: step)" "classical"
    ["assumption local.step"]\<close>
  oops


text \<open>Local facts of the proof context are reported by name, not by the theorems behind
  them.\<close>

lemma "rev (rev xs) = xs \<and> xs = (ys::nat list)"
proof -
  have c: "rev (rev xs) = xs" by simp
  note e = c[symmetric]
  have "rev (rev xs) = xs \<and> rev (rev xs) = xs \<and> xs = ys"
    ML_val \<open>
      let
        val src = "(rule conjI, rule c, rule conjI, fail)";
        val (_, uses) = inspect_test @{Isar.state} src;
        val every = count_uses true @{Isar.state} "(rule conjI, rule c, rule conjI, rule c, fail)"
          "fact local.c";
      in
        if not (member (op =) uses "fact local.c") then error ("Missing fact c: " ^ commas uses)
        else if member (op =) uses "List.rev_rev_ident" then
          error ("Theorem behind fact c reported: " ^ commas uses)
        else if every <> 2 then error ("Bad count: " ^ string_of_int every)
        else ()
      end\<close>
    oops

lemma "Q 0"
proof -
  have step: "\<And>n. Q (Suc n) \<Longrightarrow> Q n" by (rule Q_step)
  show "Q 0"
    ML_val \<open>expect_step_loop @{Isar.state} "(fast intro: step)" "classical"
      ["fact local.step"]\<close>
    oops


text \<open>Reported uses can be filtered with find_theorems criteria.\<close>

ML \<open>
fun filtered_uses state src criteria =
  let
    val proof_state = Toplevel.proof_of state;
    val (text, _) = Method.read_closure_input (Proof.context_of proof_state) (Input.string src);
    val params = {every_use = false, on_use = K (K ()), on_loop = K (K ())};
    val {uses, ...} = Apply_Inspect.inspect params text proof_state;
    val printed =
      Apply_Inspect.use_filter proof_state (Find_Theorems.read_query Position.none criteria);
  in map use_name (filter printed uses) end;
\<close>

lemma
  assumes a: "P x"
  shows "x \<noteq> 0 \<and> length (xs @ ys) = length xs + length ys \<and> xs = ys"
proof -
  have c: "rev (rev xs) = xs" by simp
  show ?thesis
    ML_val \<open>
      let
        val src =
          "(rule conjI, rule P_nonzero, rule a, rule conjI, simp, subst c[symmetric], fail)";
        fun check criteria expected =
          let val uses = filtered_uses @{Isar.state} src criteria in
            if eq_set (op =) (uses, expected) then ()
            else
              error ("Filter " ^ quote criteria ^ ": " ^ commas uses ^ "; all: " ^
                commas (#2 (inspect_test @{Isar.state} src)))
          end;
      in
        check "name: length_append" ["List.length_append"];
        check "name: P_nonzero" ["Apply_Inspect_Test.P_nonzero"];
        check "name: local.a" ["assumption local.a"];
        check "name: local.c" ["fact local.c"];
        check "\"_ \<and> _\" name: conjI" ["HOL.conjI"];
        check "-name: HOL -name: Pure -name: Nat -name: List -name: Groups"
          ["Apply_Inspect_Test.P_nonzero", "assumption local.a", "fact local.c"]
      end\<close>
    oops

lemma "length (xs @ ys) = length xs + length ys"
  apply_inspect [name: length_append] simp
  done


text \<open>Instrumentation does not change whether a method succeeds.\<close>

ML \<open>
fun expect_same_outcome state srcs =
  let
    val proof_state = Toplevel.proof_of state;
    val ctxt = Proof.context_of proof_state;
    fun check src =
      let
        val (text, _) = Method.read_closure_input ctxt (Input.string src);
        (*NONE: timeout*)
        fun outcome f =
          SOME (Timeout.apply (seconds 3.0) (fn () => the_default false (try f ())) ())
            handle Timeout.TIMEOUT _ => NONE;
        val plain =
          outcome (fn () =>
            Proof.apply (text, Position.no_range) proof_state
            |> Seq.filter_results |> Seq.pull |> is_some);
        val loops = Synchronized.var "loops" [];
        fun on_loop source _ = Synchronized.change loops (cons source);
        val params = {every_use = false, on_use = K (K ()), on_loop = on_loop};
        val inspected =
          outcome (fn () => #succeeded (Apply_Inspect.inspect params text proof_state));
      in
        (case (plain, inspected) of
          (SOME b1, SOME b2) =>
            if b1 <> b2 then
              error ("Different outcome for " ^ src ^ ": " ^ Bool.toString b1 ^ " vs. " ^
                Bool.toString b2)
            else if not (null (Synchronized.value loops)) then
              error ("False loop report for " ^ src ^ ": " ^ commas (Synchronized.value loops))
            else ()
        | _ => ())
      end;
  in List.app check srcs end;

val outcome_methods =
  ["auto", "simp", "clarsimp", "fastforce", "force", "blast", "fast", "best", "safe", "clarify",
   "(auto simp: P_def)", "(fastforce simp: P_def)", "(rule exI, rule refl)", "(rule exI)",
   "(rule conjI, auto)", "(intro allI impI, auto)", "(auto intro: P_nonzero)", "metis"];
\<close>

lemma "\<forall>x. P x \<longrightarrow> x \<noteq> 0"
  ML_val \<open>expect_same_outcome @{Isar.state} outcome_methods\<close>
  oops

lemma "\<exists>x::nat. x = Suc 0 \<and> P x"
  ML_val \<open>expect_same_outcome @{Isar.state} outcome_methods\<close>
  oops

lemma "(\<forall>x. x \<in> A \<longrightarrow> x \<in> B) \<Longrightarrow> A \<inter> C \<subseteq> B \<inter> C"
  ML_val \<open>expect_same_outcome @{Isar.state} outcome_methods\<close>
  oops

lemma "length (xs @ ys) = length xs + length ys \<and> xs = ys"
  ML_val \<open>expect_same_outcome @{Isar.state} outcome_methods\<close>
  oops

lemma
  assumes "P x" and "x = y"
  shows "y \<noteq> 0 \<and> P y"
  ML_val \<open>expect_same_outcome @{Isar.state}
    (outcome_methods @
      ["(simp add: assms)", "(auto intro: assms P_nonzero)", "(insert assms, auto)",
       "(insert assms, fastforce dest: P_nonzero)", "(insert assms, blast dest: P_nonzero)",
       "(use assms in \<open>force dest: P_nonzero\<close>)", "(metis assms P_nonzero)",
       "(rule conjI, insert assms, simp_all, fail)"])\<close>
  oops

lemma "\<exists>f. \<forall>x::nat. f x = Suc x"
  ML_val \<open>expect_same_outcome @{Isar.state} outcome_methods\<close>
  oops


text \<open>Goals from theories that do not import Apply_Inspect.\<close>

ML \<open>
fun unrelated_state goal =
  let
    val ctxt = Proof_Context.init_global \<^theory>\<open>Apply_Inspect_Unrelated\<close>;
  in Proof.theorem NONE (K I) [[(Syntax.read_prop ctxt goal, [])]] ctxt end;

fun check_unrelated goal src expected =
  let
    val state = unrelated_state goal;
    val (text, _) = Method.read_closure_input (Proof.context_of state) (Input.string src);
    val plain =
      the_default false (try (fn () =>
        Proof.apply (text, Position.no_range) state |> Seq.filter_results |> Seq.pull |> is_some) ());
    val params = {every_use = false, on_use = K (K ()), on_loop = K (K ())};
    val result = Apply_Inspect.inspect params text state;
    val uses = map use_name (#uses result);
  in
    if is_some (#error result) then error ("Error for " ^ src ^ ": " ^ the (#error result))
    else if #succeeded result <> plain then
      error ("Different outcome for " ^ src ^ ": " ^ Bool.toString plain ^ " vs. " ^
        Bool.toString (#succeeded result))
    else if exists (fn name => not (member (op =) uses name)) expected then
      error ("Missing uses for " ^ src ^ ": " ^ commas uses)
    else ()
  end;
\<close>

ML_val \<open>
  check_unrelated "rev (rev xs) = xs \<and> (xs::nat list) = ys" "(rule conjI, auto)" ["HOL.conjI"];
  check_unrelated "rev (rev xs) = xs \<and> (xs::nat list) = ys" "(rule conjI, auto, fail)"
    ["HOL.conjI", "List.rev_rev_ident"];
  check_unrelated "rev (rev xs) = xs \<and> (xs::nat list) = ys" "(rule conjI, force)" ["HOL.conjI"];
  check_unrelated "\<exists>x::nat. x = Suc 0" "(rule exI, rule refl)" ["HOL.exI"];
  check_unrelated "length (xs @ ys) = length xs + length ys \<and> xs = ys" "fastforce"
    ["List.length_append"]
\<close>


text \<open>Dependencies of the goal state itself are not reported.\<close>

lemma "xs = ys \<and> rev (rev xs) = xs"
  apply (rule conjI)
  ML_val \<open>
    let val (succeeded, deps) = inspect_test @{Isar.state} "(rule Q_rev)" in
      if succeeded orelse member (op =) deps "HOL.conjI" then error "Bad result" else ()
    end\<close>
  oops

end
