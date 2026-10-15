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


text \<open>
  After a timeout, the goal states that the method reached are shown: from the start of the
  trace on, in the given intervals, up to the time limit. Each one is a refinement of the goal by
  oracle, including the subgoals hidden by goal restriction, computed by replaying the method and
  freezing it at that point.
\<close>

ML \<open>
val trace_limits = {timeout = seconds 0.5, trace_start = seconds 0.1, trace_interval = seconds 0.1};

(*the goal states recorded after the timeout*)
fun traced_states state src =
  let
    val proof_state = Toplevel.proof_of state;
    val (text, _) = Method.read_closure_input (Proof.context_of proof_state) (Input.string src);
    val params = {every_use = false, on_use = K (K ()), on_loop = K (K ())};
  in
    (case Apply_Inspect.inspect_limited params trace_limits text proof_state of
      {error = SOME msg, partial, ...} =>
        (case Seq.list_of partial of
          [] => error ("No goal states: " ^ msg)
        | states => states)
    | _ => error "Method terminated")
  end;

fun subgoals_of ({state, ...}: {time: Time.time, state: Proof.state, uses: Apply_Inspect.use list}) =
  Thm.prems_of (#goal (Proof.simple_goal state));
val traced_subgoals = map subgoals_of oo traced_states;
val first_subgoals = hd oo traced_subgoals;

fun suc_depth \<^Const_>\<open>Suc for t\<close> = suc_depth t + 1
  | suc_depth _ = 0;

(*n for a goal state with the single subgoal Q (Suc^n 0)*)
fun q_depth [\<^Const_>\<open>Trueprop for \<open>\<^Const_>\<open>Q for t\<close>\<close>\<close>] = suc_depth t
  | q_depth _ = error "Bad goal state";

fun strictly_increasing (x :: (rest as y :: _)) = x < y andalso strictly_increasing rest
  | strictly_increasing _ = true;

fun sleep_method t =
  "(tactic \<open>fn st => (if Thm.nprems_of st > 0 then OS.Process.sleep (seconds " ^ t ^
    ") else (); all_tac st)\<close>)";
\<close>

text \<open>The goal states proceed with the method.\<close>

lemma "Q 0"
  ML_val \<open>
    let val depths = map q_depth (traced_subgoals @{Isar.state} "(fast intro: Q_step)") in
      if length depths >= 3 andalso strictly_increasing depths then ()
      else error ("Bad goal states: " ^ commas (map string_of_int depths))
    end\<close>
  oops

lemma "Q 0 \<and> True"
  ML_val \<open>
    (case first_subgoals @{Isar.state} "(rule conjI, fast intro: Q_step)" of
      [\<^Const_>\<open>Trueprop for \<open>\<^Const_>\<open>Q for _\<close>\<close>\<close>, \<^prop>\<open>True\<close>] => ()
    | _ => error "Bad goal state")\<close>
  oops

text \<open>A looping simplifier shows the term that it has reached, also within other methods.\<close>

axiomatization grow :: "nat \<Rightarrow> nat" where grow_Suc: "grow n = grow (Suc n)"

ML \<open>
fun grow_depth \<^Const_>\<open>Trueprop for \<open>\<^Const_>\<open>HOL.eq _ for \<open>\<^Const_>\<open>grow for t\<close>\<close> _\<close>\<close>\<close> =
      suc_depth t
  | grow_depth \<^Const_>\<open>Trueprop for \<open>\<^Const_>\<open>conj for
        \<open>\<^Const_>\<open>HOL.eq _ for \<open>\<^Const_>\<open>grow for t\<close>\<close> _\<close>\<close> _\<close>\<close>\<close> =
      suc_depth t
  | grow_depth _ = error "Bad goal state";
\<close>

lemma "grow 0 = 1 \<and> Q 0"
  ML_val \<open>
    let
      val states = traced_subgoals @{Isar.state} "(rule conjI, simp add: grow_Suc)";
      val depths = states |> map (fn [t, \<^prop>\<open>Q 0\<close>] => grow_depth t
        | _ => error "Bad goal state");
    in
      if length depths >= 3 andalso hd depths > 0 andalso strictly_increasing depths then ()
      else error ("Bad goal states: " ^ commas (map string_of_int depths))
    end\<close>
  ML_val \<open>
    let
      val states = traced_subgoals @{Isar.state} "(auto simp add: grow_Suc)";
      val depths = states |> map (fn [t] => grow_depth t | _ => error "Bad goal state");
    in
      if length depths >= 3 andalso hd depths > 0 andalso strictly_increasing depths then ()
      else error ("Bad goal states: " ^ commas (map string_of_int depths))
    end\<close>
  oops

text \<open>Each goal state comes with the theorems used since the previous one.\<close>

lemma "Q 0"
  ML_val \<open>
    let val uses = map (map use_name o #uses) (traced_states @{Isar.state} "(fast intro: Q_step)")
    in
      if length uses >= 3 andalso
        forall (fn names => member (op =) names "Apply_Inspect_Test.Q_step") uses
      then () else error "Q_step not reported for each goal state"
    end\<close>
  oops

text \<open>Without progress, the goal is unchanged.\<close>

lemma "f 0 = 1"
  ML_val \<open>
    if first_subgoals @{Isar.state} (sleep_method "1.0") = [\<^prop>\<open>f 0 = 1\<close>] then ()
    else error "Bad goal state"\<close>
  oops

text \<open>A method that finishes within the time limit is not traced.\<close>

lemma "rev (rev xs) = xs"
  ML_val \<open>
    let
      val proof_state = Toplevel.proof_of @{Isar.state};
      val (text, _) =
        Method.read_closure_input (Proof.context_of proof_state) (Input.string "simp");
      val params = {every_use = false, on_use = K (K ()), on_loop = K (K ())};
    in
      (case Apply_Inspect.inspect_limited params trace_limits text proof_state of
        {succeeded = true, error = NONE, partial, ...} =>
          if is_none (Seq.pull partial) then () else error "Traced"
      | _ => error "Method failed")
    end\<close>
  oops

text \<open>
  The command continues with the first recorded goal state; \<^theory_text>\<open>back\<close> shows the
  later ones.
\<close>

ML \<open>val first_depth = Unsynchronized.ref 0\<close>

lemma "Q 0"
  using [[apply_inspect_timeout = 600, apply_inspect_trace_start = 200]]
  apply_inspect (fast intro: Q_step)
  ML_val \<open>first_depth := q_depth (Thm.prems_of (#goal (Proof.simple_goal
    (Toplevel.proof_of @{Isar.state}))))\<close>
  back
  ML_val \<open>
    if q_depth (Thm.prems_of (#goal (Proof.simple_goal (Toplevel.proof_of @{Isar.state}))))
      > ! first_depth then ()
    else error "back did not step forwards"\<close>
  oops

lemma "grow 0 = 1 \<and> Q 0"
  using [[apply_inspect_timeout = 300, apply_inspect_trace_interval = 50]]
  apply_inspect (rule conjI, simp add: grow_Suc)
  ML_val \<open>
    (case Thm.prems_of (#goal (Proof.simple_goal (Toplevel.proof_of @{Isar.state}))) of
      [t, \<^prop>\<open>Q 0\<close>] => if grow_depth t > 0 then () else error "Simplifier result not kept"
    | _ => error "Bad goal state")\<close>
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


text \<open>
  Infrastructure is not shown by default: theorems of Pure, class axioms, locale axioms, and
  theorems declared with @{attribute apply_inspect_hide}.
\<close>

locale inf_base =
  fixes u :: "nat \<Rightarrow> nat"
  assumes u0: "u 0 = 0"

locale inf_ext = inf_base +
  assumes u1: "u 1 = 1"

class inf_class = plus +
  assumes inf_comm: "x + y = y + (x::'a)"

lemma inf_hidden: "rev (rev xs) = xs" by simp

declare inf_hidden [apply_inspect_hide]

ML_val \<open>
  let
    val ctxt = \<^context>;
    val infrastructure = Apply_Inspect.infrastructure ctxt;
    fun theorem name i = Apply_Inspect.Theorem ((name, i), Position.none);
    val hidden =
      [theorem "Pure.protectI" 0, theorem "Pure.conjunctionI" 0,
       theorem "HOL.eq_reflection" 0, theorem "Apply_Inspect_Test.inf_hidden" 0,
       theorem "Nat.arity_type_nat" 0,
       theorem "Apply_Inspect_Test.inf_class_class_def" 0,
       theorem "Apply_Inspect_Test.inf_class_class.intro" 0,
       theorem "Apply_Inspect_Test.inf_class_class.axioms" 0,
       theorem "Apply_Inspect_Test.inf_class_class.super" 0,
       theorem "Apply_Inspect_Test.class.inf_class_def" 0,
       theorem "Apply_Inspect_Test.class.inf_class.intro" 0,
       theorem "Apply_Inspect_Test.inf_base_def" 0,
       theorem "Apply_Inspect_Test.inf_base.intro" 0,
       theorem "Apply_Inspect_Test.inf_ext_axioms_def" 0,
       theorem "Apply_Inspect_Test.inf_ext_axioms.intro" 0,
       theorem "Apply_Inspect_Test.inf_ext_def" 0,
       theorem "Apply_Inspect_Test.inf_ext.intro" 0,
       theorem "Apply_Inspect_Test.inf_ext.axioms" 1,
       theorem "Apply_Inspect_Test.inf_ext.axioms" 2];
    val shown =
      [theorem "HOL.conjI" 0, theorem "List.length_append" 0, theorem "Apply_Inspect_Test.Q_rev" 0,
       theorem "Apply_Inspect_Test.inf_base.u0" 0, theorem "Apply_Inspect_Test.inf_ext.u1" 0,
       theorem "Apply_Inspect_Test.inf_comm" 0, Apply_Inspect.Fact ("local.c", 0)];
    val name = Thm_Name.print o (fn Apply_Inspect.Theorem (thm_name, _) => thm_name
      | Apply_Inspect.Fact thm_name => thm_name | _ => Thm_Name.empty);
    val _ =
      (case filter_out infrastructure hidden of
        [] => ()
      | us => error ("Not infrastructure: " ^ commas (map name us)));
    val _ =
      (case filter infrastructure shown of
        [] => ()
      | us => error ("Infrastructure: " ^ commas (map name us)));
  in () end\<close>

text \<open>The attribute can be undone.\<close>

declare inf_hidden [apply_inspect_hide del]

ML_val \<open>
  if Apply_Inspect.infrastructure \<^context>
    (Apply_Inspect.Theorem (("Apply_Inspect_Test.inf_hidden", 0), Position.none))
  then error "Still hidden" else ()\<close>

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

text \<open>
  Method text that is read without closure is closed during the run: exceptions raised while
  reading the method are reported as errors, and the dummy goal state of the closure is not
  inspected.
\<close>

ML \<open>
fun read_text ctxt src =
  Parse.read_embedded ctxt (Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt))
    (Scan.many Token.not_eof) (Input.string src)
  |> Method.read ctxt;

fun inspect_unclosed state src =
  let
    val proof_state = Toplevel.proof_of state;
    val text = read_text (Proof.context_of proof_state) src;
    val params = {every_use = false, on_use = K (K ()), on_loop = K (K ())};
  in Apply_Inspect.inspect params text proof_state end;
\<close>

lemma "xs = ys"
  ML_val \<open>
    (case inspect_unclosed @{Isar.state} "(tactic \<open>fn _ => error \"boom\"\<close>)" of
      {succeeded = false, error = SOME msg, ...} =>
        if String.isSubstring "boom" msg then () else error ("Bad error: " ^ msg)
    | _ => error "No error reported")\<close>
  oops

lemma "rev (rev xs) = xs \<and> (xs::nat list) = ys"
  ML_val \<open>
    let
      val {succeeded, error = err, uses} =
        inspect_unclosed @{Isar.state} "(rule conjI, auto, fail)";
    in
      if succeeded orelse is_some err then error "Bad result"
      else
        (case filter_out (member (op =) (map use_name uses)) ["HOL.conjI", "List.rev_rev_ident"] of
          [] => ()
        | missing => error ("Missing: " ^ commas missing))
    end\<close>
  oops

text \<open>Uses are annotated with their declarations in the context.\<close>

lemma decl_intro [intro]: "x = y \<Longrightarrow> y = x" by simp
lemma decl_dest [dest]: "x = Suc y \<Longrightarrow> 0 < x" by simp
lemma decl_simp_elim [simp, elim]: "x < 0 \<Longrightarrow> thesis" for x :: nat by simp

ML \<open>
fun expect_declarations ctxt use attribs =
  let
    val declared = Apply_Inspect.declarations ctxt use;
    val printed = Pretty.unformatted_string_of (Apply_Inspect.pretty_use ctxt use);
    val suffix = if null attribs then "" else " [" ^ commas attribs ^ "]";
  in
    if declared <> attribs then
      error (printed ^ ": expected " ^ commas attribs ^ ", got " ^ commas declared)
    else if not (String.isSuffix suffix printed) then error ("Bad output: " ^ printed)
    else ()
  end;

fun theorem name = Apply_Inspect.Theorem ((name, 0), Position.none);
\<close>

ML_val \<open>
  expect_declarations \<^context> (theorem "List.rev_rev_ident") ["simp"];
  expect_declarations \<^context> (theorem "HOL.conjI") ["intro!"];
  expect_declarations \<^context> (theorem "HOL.conjE") ["elim!"];
  expect_declarations \<^context> (theorem "Apply_Inspect_Test.decl_intro") ["intro"];
  expect_declarations \<^context> (theorem "Apply_Inspect_Test.decl_dest") ["dest"];
  expect_declarations \<^context> (theorem "Apply_Inspect_Test.decl_simp_elim") ["simp", "elim"];
  expect_declarations \<^context> (theorem "Apply_Inspect_Test.P_nonzero") [];
  expect_declarations \<^context> (Apply_Inspect.Rule @{thm conjI}) ["intro!"]
\<close>

text \<open>The theorems behind uses.\<close>

ML \<open>
fun expect_use_thm ctxt use thm =
  (case Apply_Inspect.use_thm ctxt use of
    SOME thm' =>
      if Thm.eq_thm_prop (thm, thm') then ()
      else error ("Wrong theorem: " ^ Thm.string_of_thm ctxt thm')
  | NONE => error "No theorem")
\<close>

ML_val \<open>
  expect_use_thm \<^context> (theorem "List.rev_rev_ident") @{thm rev_rev_ident};
  expect_use_thm \<^context> (Apply_Inspect.Theorem (("HOL.simp_thms", 2), Position.none))
    (nth @{thms simp_thms} 1);
  expect_use_thm \<^context> (Apply_Inspect.Rule @{thm conjI}) @{thm conjI};
  expect_use_thm \<^context> (Apply_Inspect.Assumption (Thm_Name.empty, \<^prop>\<open>x = y\<close>))
    (Thm.assume \<^cprop>\<open>x = y\<close>);
  if is_some (Apply_Inspect.use_thm \<^context> (theorem "List.no_such_fact")) then
    error "Theorem for undefined fact"
  else ()
\<close>

lemma "P a"
proof -
  have local_rule [simp, intro]: "P b \<longleftrightarrow> 0 < b" for b by (simp add: P_def)
  ML_val \<open>
    expect_declarations \<^context> (Apply_Inspect.Fact ("local.local_rule", 0))
      ["simp", "intro"];
    expect_use_thm \<^context> (Apply_Inspect.Fact ("local.local_rule", 0)) @{thm local_rule}\<close>
  oops

text \<open>
  A failed proof of an earlier theorem does not affect the inspection of later goals, as in PIDE,
  where a failed proof does not stop the theory. The failed proof is simulated by a fact with a
  failed proof promise, in a theory that is not committed.
\<close>

ML_val \<open>
  let
    val failed = Thm.future (Future.value_result (Exn.Exn (ERROR "Failed proof"))) \<^cprop>\<open>False\<close>;
    val (_, thy) = Global_Theory.store_thm (\<^binding>\<open>failed_fact\<close>, failed) \<^theory>;
    val _ =
      if can Global_Theory.get_thm_names thy then error "Failed proof not simulated" else ();
    val state =
      Proof.theorem NONE (K I) [[(\<^prop>\<open>(n::nat) + 1 < n\<close>, [])]]
        (Proof_Context.init_global thy);
    val ctxt = Proof.context_of state;
    val text = read_text ctxt "simp";
    val params = {every_use = false, on_use = K (K ()), on_loop = K (K ())};
  in
    (case Apply_Inspect.inspect params text state of
      {succeeded = true, error = NONE, uses} =>
        if null uses then error "No uses reported" else ()
    | {error = SOME msg, ...} => error ("Error: " ^ msg)
    | _ => error "Method failed")
  end\<close>

text \<open>
  An unfinished proof of an earlier theorem (e.g. a forked proof that is stuck) delays the
  inspection of later goals by at most the join timeout per step, and its dependencies are left
  out. The proof is simulated by a fact with a promise that is fulfilled only afterwards.
\<close>

ML_val \<open>
  let
    val stuck = Future.promise I;
    val stuck_thm = Thm.future stuck \<^cprop>\<open>\<forall>n::nat. n + 1 < n\<close>;
    val (_, thy) = Global_Theory.store_thm (\<^binding>\<open>stuck_fact\<close>, stuck_thm) \<^theory>;
    val ctxt = Proof_Context.init_global thy;
    fun check src prop =
      let
        val state = Proof.theorem NONE (K I) [[(prop, [])]] ctxt;
        val params = {every_use = false, on_use = K (K ()), on_loop = K (K ())};
        val start = Time.now ();
        val result =
          Timeout.apply (seconds 20.0)
            (Apply_Inspect.inspect params (read_text (Proof.context_of state) src)) state;
        val time = Time.now () - start;
      in
        (case result of
          {succeeded = true, error = NONE, ...} =>
            if time > seconds 5.0 then error (src ^ ": took " ^ Time.message time) else ()
        | {error = SOME msg, ...} => error (src ^ ": " ^ msg)
        | _ => error (src ^ ": method failed"))
      end;
    val result =
      Exn.capture (fn () =>
        (check "simp" \<^prop>\<open>(n::nat) < n + 2\<close>;
         check "(rule stuck_fact)" \<^prop>\<open>\<forall>n::nat. n + 1 < n\<close>)) ();
    val _ = Future.fulfill_result stuck (Exn.Exn (Fail "Test finished"));
  in Exn.release result end\<close>

end
