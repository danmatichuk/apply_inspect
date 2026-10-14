(*  Title:      apply_inspect.ML

Diagnostic variant of "apply": if the proof method fails, report the
theorems that were used during the failed attempt.

The method is first run on a copy of the goal state that is produced by an
oracle (so that it has no theorem dependencies of its own), in a context
where the classical reasoner and the simplifier record every intermediate
goal state they see, and the simplifier records every rewrite rule it
tries. Before each method or classical step, the goal state is copied again
in the same way, so that the result of the step depends on exactly the
theorems that the step used. The results of that run are always discarded:
if the method succeeds, it is run again without instrumentation.
*)

signature APPLY_INSPECT =
sig
  val every_use: bool Config.T
  datatype use =
    Theorem of Thm_Name.P |
    Assumption of Thm_Name.T * term |
    Rule of thm
  val pretty_use: Proof.context -> use -> Pretty.T
  type params =
   {every_use: bool,
    on_use: string -> use -> unit,
    on_loop: string -> use list -> unit}
  val inspect: params -> Method.text -> Proof.state -> {succeeded: bool, uses: use list}
  val pretty_uses: Proof.context -> use list -> Pretty.T
  val apply_inspect: Method.text_range -> Proof.state -> Proof.state Seq.result Seq.seq
end;

structure Apply_Inspect: APPLY_INSPECT =
struct

(*report every use of a theorem, not just the first one*)
val every_use =
  Attrib.setup_config_bool \<^binding>\<open>apply_inspect_every_use\<close> (K false);


(* uses *)

datatype use =
  Theorem of Thm_Name.P |  (*global theorem*)
  Assumption of Thm_Name.T * term |  (*assumption of the proof context, possibly unnamed*)
  Rule of thm;  (*other rule, e.g. premise of a subgoal*)

fun pretty_use ctxt (Theorem (thm_name, _)) = Global_Theory.pretty_thm_name ctxt thm_name
  | pretty_use ctxt (Assumption (thm_name, prop)) =
      Pretty.block [Pretty.str "assumption ",
        if Thm_Name.is_empty thm_name then Pretty.quote (Syntax.pretty_term ctxt prop)
        else Proof_Context.pretty_thm_name ctxt thm_name]
  | pretty_use ctxt (Rule thm) = Pretty.block [Pretty.str "rule ", Thm.pretty_thm ctxt thm];

(*names of the assumptions of a proof context, as local facts*)
fun assumption_names ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val local_facts =
      Facts.dest_static false [Global_Theory.facts_of thy] (Proof_Context.facts_of ctxt)
      |> filter_out (fn (name, _) => Long_Name.base_name name = "this");
    (*facts that state a single assumption, possibly with its parameters as schematic
      variables*)
    fun add (thm_name, thm) =
      (case Thm.chyps_of thm of
        [chyp] =>
          let
            val hyp = Thm.term_of chyp;
            val exact = hyp aconv Thm.prop_of thm;
            fun generic () =
              Thm.equiv_thm thy
                (Thm.forall_elim_vars (Thm.maxidx_of thm + 1) (Thm.assume chyp), thm);
          in
            if exact orelse try generic () = SOME true then cons (hyp, (thm_name, exact)) else I
          end
      | _ => I);
    val candidates = fold (fold add o Thm_Name.make_list) local_facts [];
    (*prefer the assumption itself, and single facts*)
    fun rank (((_, i), exact)) = (if exact then 0 else 2) + (if i = 0 then 0 else 1);
  in
    Termtab.build (fold (fn (hyp, candidate) =>
      Termtab.map_default (hyp, candidate) (fn candidate' =>
        if rank candidate < rank candidate' then candidate else candidate')) candidates)
    |> Termtab.map (K #1)
  end;


(* fresh goal state without dependencies *)

val (_, fresh_state) =
  Context.>>> (Context.map_theory_result (Thm.add_oracle (\<^binding>\<open>apply_inspect\<close>, I)));

(*copy of the goal state without dependencies, with the same hypotheses, unless the copy would
  differ in flex-flex constraints or sort hypotheses (which would affect the behaviour of
  tactics)*)
fun refresh_state st =
  let
    fun copy () =
      let val hyps = Thm.chyps_of st in
        Drule.implies_elim_list (fresh_state (Drule.list_implies (hyps, Thm.cprop_of st)))
          (map Thm.assume hyps)
      end;
  in
    (case try copy () of
      SOME st' => if Thm.eq_thm (st, st') then st' else st
    | NONE => st)
  end;


(* loop detection *)

(*A sequence of steps (simplifier rewrites, classical steps, or method applications) is
  suspected to loop if it keeps working on its own output with a periodic sequence of rules,
  without making terms smaller: for some period p, each of the last loop_repetitions * p
  steps uses the same rules as the step p steps before, on a term that is at least as large,
  and continues from the output of the preceding step. Terminating evaluation of recursive
  functions and terminating proof search usually make terms smaller.*)

val loop_max_period = 8;
val loop_repetitions = 10;

(*rule: what the step used,
  size: size of the term that the step works on,
  follows: whether the step continues from the given output of the preceding step,
  output: output of the step, if any*)
type ('a, 'b) loop_step = {rule: 'a, size: int, follows: 'b -> bool, output: 'b option};

type ('a, 'b) loop_state =
 {recent: ('a * int) list,  (*rules and sizes of previous steps, most recent first*)
  runs: int list,  (*for each period: number of consecutive steps that repeat its rules
                      without shrinking*)
  chain: int,  (*number of consecutive steps that continue from the preceding output*)
  last: 'b option,  (*output of the preceding step*)
  reported: 'a list list};  (*rules of cycles reported so far*)

fun init_loop_state () : ('a, 'b) loop_state =
  {recent = [], runs = replicate loop_max_period 0, chain = 0, last = NONE, reported = []};

(*result: rules of a newly suspected cycle*)
fun add_loop_step eq ({rule, size, follows, output}: ('a, 'b) loop_step)
    ({recent, runs, chain, last, reported}: ('a, 'b) loop_state) =
  let
    val chain' =
      (case last of
        SOME prev => if follows prev then chain + 1 else 0
      | NONE => 0);
    val runs' =
      runs |> map_index (fn (k, run) =>
        (case try (nth recent) k of
          SOME (rule', size') => if eq (rule, rule') andalso size >= size' then run + 1 else 0
        | NONE => 0));
    val steps = (rule, size) :: recent;

    fun periodic (k, run) =
      let val n = (k + 1) * (loop_repetitions - 1)
      in run >= n andalso chain' >= n end;
    val new_cycle =
      (case find_index periodic (map_index I runs') of
        ~1 => NONE
      | k =>
          let val rules = distinct eq (rev (map #1 (take (k + 1) steps))) in
            if exists (fn rules' => eq_set eq (rules, rules')) reported then NONE
            else SOME rules
          end);
    val reported' = (case new_cycle of SOME rules => rules :: reported | NONE => reported);
    val state' =
     {recent = take loop_max_period steps, runs = runs', chain = chain', last = output,
      reported = reported'};
  in (new_cycle, state') end;


(* collect dependencies *)

(*named theorems behind dependency nodes, without those already seen;
  see also Thm_Deps.thm_deps*)
fun resolve_deps lookup seen thms =
  let
    fun deps (i, thm_node) tab =
      if Inttab.defined seen i orelse Inttab.defined tab i then tab
      else
        (case lookup (Proofterm.thm_id (i, thm_node)) of
          SOME thm_name => Inttab.update (i, SOME thm_name) tab
        | NONE =>
            Inttab.update (i, NONE) tab
            |> fold deps (Proofterm.thm_node_thms thm_node));
  in Inttab.build (fold deps thms) end;

fun names_of tab = Inttab.fold_rev (fn (_, SOME thm_name) => cons thm_name | _ => I) tab [];

(*events reported by the instrumentation:
    observe -- goal state seen at some point,
    step -- inference step: original input state, input state that the step was actually
      applied to, output state, and size of the term that the step works on,
    rewrite -- rewrite rule tried by the simplifier*)
type events =
 {observe: string -> thm -> unit,
  step: string -> {input: thm, start: thm, output: thm, size: int} -> unit,
  rewrite: {instance: thm, rule: thm, name: Thm_Name.T, redex: term, result: term option} ->
    unit};

type params =
 {every_use: bool,
  on_use: string -> use -> unit,
  on_loop: string -> use list -> unit};

(*collector: serial of each dependency seen so far, with its name if it is a named theorem;
  hyps_collector: hypotheses seen so far*)
fun make_events ctxt collector hyps_collector ({every_use, on_use, on_loop}: params) : events =
  let
    val thy = Proof_Context.theory_of ctxt;
    val lookup = Global_Theory.lookup_thm_id thy;
    val facts = Global_Theory.facts_of thy;
    val assumption_name =
      the_default Thm_Name.empty o Termtab.lookup (assumption_names ctxt);
    fun assumption hyp = Assumption (assumption_name hyp, hyp);

    (*hypotheses that are assumptions of the proof context, not e.g. premises of a subgoal
      that are assumed temporarily by the simplifier*)
    val context_assms = Termtab.make_set (map Thm.term_of (Assumption.all_assms_of ctxt));
    val context_hyps = filter (Termtab.defined context_assms);

    fun add (i, entry) (names, seen) =
      if Inttab.defined seen i then (names, seen)
      else (the_list entry @ names, Inttab.update (i, entry) seen);
    fun add_deps tab = rev (Synchronized.change_result collector (Inttab.fold add tab o pair []));
    fun add_hyp hyp (hyps, seen) =
      if Termtab.defined seen hyp then (hyps, seen)
      else (hyp :: hyps, Termtab.update (hyp, ()) seen);
    fun add_hyps hyps =
      rev (Synchronized.change_result hyps_collector (fold add_hyp hyps o pair []));

    fun emit source names hyps =
      (List.app (on_use source o Theorem) names; List.app (on_use source o assumption) hyps);

    (*first uses*)
    fun observe source st =
      let
        val names =
          (case try Thm.thm_deps st of
            SOME thms => add_deps (resolve_deps lookup (Synchronized.value collector) thms)
          | NONE => []);
        val hyps = add_hyps (context_hyps (Thm.hyps_of st));
      in if every_use then () else emit source names hyps end;

    (*every use*)
    fun use source thms hyps =
      let val tab = resolve_deps lookup Inttab.empty thms
      in add_deps tab; add_hyps hyps; emit source (names_of tab) hyps end;


    (* steps *)

    val step_loops = Synchronized.var "apply_inspect_step_loops" Symtab.empty;

    fun step source {input, start, output, size} =
      let
        val used =
          (case (try Thm.thm_deps start, try Thm.thm_deps output) of
            (SOME thms, SOME thms') =>
              let
                val tab =
                  resolve_deps lookup Inttab.empty (Ord_List.subtract Proofterm.thm_ord thms thms');
                val hyps =
                  context_hyps (subtract (op aconv) (Thm.hyps_of start) (Thm.hyps_of output));
              in SOME (tab, hyps) end
          | _ => NONE);
        val _ =
          (case used of
            SOME (tab, hyps) =>
              if every_use then (add_deps tab; add_hyps hyps; emit source (names_of tab) hyps)
              else observe source output
          | NONE => observe source output);
        val rule =
          (case used of
            SOME (tab, hyps) =>
              (sort_distinct Thm_Name.ord (map #1 (names_of tab)),
                sort_distinct Term_Ord.fast_term_ord hyps)
          | NONE => ([], []));
        val loop_step =
          {rule = rule, size = size, output = SOME output,
            follows = fn prev => pointer_eq (prev, input) orelse Thm.eq_thm (prev, input)};
        val new_cycle =
          Synchronized.change_result step_loops (fn tab =>
            let
              val state = the_default (init_loop_state ()) (Symtab.lookup tab source);
              val (new_cycle, state') = add_loop_step (op =) loop_step state;
            in (new_cycle, Symtab.update (source, state') tab) end);
      in
        new_cycle |> Option.app (fn rules =>
          let
            val names = distinct (op =) (maps #1 rules);
            (*assumptions are only reported on first use on a branch, so fall back to those
              that the branch uses*)
            val hyps =
              (case distinct (op aconv) (maps #2 rules) of
                [] => if null names then context_hyps (Thm.hyps_of output) else []
              | hyps => hyps);
          in
            on_loop source
              (map (fn name => Theorem (name, Position.none)) names @ map assumption hyps)
          end)
      end;


    (* rewrites *)

    val rewrite_loops = Synchronized.var "apply_inspect_rewrite_loops" (init_loop_state ());

    fun rule_use (name, rule) =
      if Facts.defined facts (#1 name) then Theorem (name, Position.none)
      else
        (case Thm.hyps_of rule of
          [hyp] =>
            if hyp aconv Thm.prop_of rule andalso Termtab.defined context_assms hyp
            then assumption hyp else Rule rule
        | _ => Rule rule);

    fun rewrite {instance, rule, name, redex, result} =
      let
        val _ =
          if every_use andalso Facts.defined facts (#1 name) then
            (observe "simp" instance; on_use "simp" (Theorem (name, Position.none)))
          else if every_use then
            use "simp" (the_default [] (try Thm.thm_deps instance))
              (context_hyps (Thm.hyps_of instance))
          else observe "simp" instance;
        val loop_step =
          {rule = (name, rule), size = size_of_term redex, output = result,
            follows = exists_subterm (fn t => t aconv redex)};
      in
        Synchronized.change_result rewrite_loops
          (add_loop_step (Thm.eq_thm_prop o apply2 #2) loop_step)
        |> Option.app (on_loop "simp" o map rule_use)
      end;
  in {observe = observe, step = step, rewrite = rewrite} end;

fun collected_uses ctxt collector hyps_collector =
  let val name = the_default Thm_Name.empty o Termtab.lookup (assumption_names ctxt) in
    map Theorem (names_of (Synchronized.value collector)) @
      map (fn hyp => Assumption (name hyp, hyp)) (Termtab.keys (Synchronized.value hyps_collector))
  end;


(* instrumentation *)

val hook_name = "apply_inspect";

fun instrument_context ({observe, step, ...}: events) ctxt =
  let
    fun wrapper _ tac i st =
      let
        val _ = observe "classical" st;
        val st0 = refresh_state st;
        val size =
          (case try (Thm.cprem_of st) i of
            SOME ct => size_of_term (Thm.term_of ct)
          | NONE => 0);
        fun step_output st' =
          step "classical" {input = st, start = st0, output = st', size = size};
      in Seq.map (tap step_output) (tac i st0) end;
    fun observe_tac (_: Proof.context) (_: int) st = (observe "simp" st; Seq.empty);
    val solver = Simplifier.mk_solver hook_name observe_tac;
  in
    ctxt
    |> (fn ctxt => Classical.addSWrapper (ctxt, (hook_name, wrapper)))
    |> (fn ctxt => Classical.addWrapper (ctxt, (hook_name, wrapper)))
    |> Simplifier.add_loop (hook_name, observe_tac)
    |> Simplifier.add_unsafe_solver solver
    |> Simplifier.add_safe_solver solver
  end;

fun simp_trace_ops ({rewrite, ...}: events) : Raw_Simplifier.trace_ops =
 {trace_invoke = K I,
  trace_rrule = fn {thm, rrule = {thm = rule, name, ...}, cterm, ...} => fn ctxt => fn cont =>
    let
      val res = cont ctxt;
      val result = Option.map (Thm.term_of o Thm.rhs_of o #1) res;
      val _ =
        rewrite {instance = thm, rule = rule, name = name, redex = Thm.term_of cterm,
          result = result};
    in res end,
  trace_simproc = K (fn ctxt => fn cont => cont ctxt)};

fun instrument_text ({observe, step, ...}: events) =
  let
    fun wrap_method source (m: Method.method) : Method.method = fn facts => fn (ctxt, st) =>
      let
        val _ = observe source st;
        val st0 = refresh_state st;
      in
        m facts (ctxt, st0) |> Seq.map (fn result =>
          ((case result of
              Seq.Result (_, st') =>
                step source
                  {input = st, start = st0, output = st', size = size_of_term (Thm.prop_of st)}
            | Seq.Error _ => ());
            result))
      end;
    fun method_name ctxt src =
      Name_Space.extern_shortest ctxt (Method.method_space (Context.Proof ctxt))
        (#1 (Token.name_of_src src));
    fun wrap (Method.Source src) =
          Method.Basic (fn ctxt =>
            wrap_method (method_name ctxt src) (Method.method_cmd ctxt src ctxt))
      | wrap (Method.Basic m) = Method.Basic (wrap_method "method" o m)
      | wrap (Method.Combinator (info, comb, txts)) =
          Method.Combinator (info, comb, map wrap txts);
  in wrap end;


(* inspect *)

fun run params text state =
  let
    val _ = Proof.assert_backward state;
    val ctxt = Proof.context_of state;
    val {context = goal_ctxt, facts = using, goal} = Proof.raw_goal state;

    val collector = Synchronized.var "apply_inspect" Inttab.empty;
    val hyps_collector = Synchronized.var "apply_inspect_hyps" Termtab.empty;
    val events = make_events ctxt collector hyps_collector params;

    (*the results of the run are discarded, so its contexts may live in a private theory*)
    val thy' = Raw_Simplifier.set_trace_ops (simp_trace_ops events) (Proof_Context.theory_of ctxt);
    val instrument = Proof_Context.transfer thy' #> instrument_context events;

    val result =
      Exn.result (fn () =>
        (instrument goal_ctxt, fresh_state (Thm.cprop_of goal))
        |> Method.evaluate (instrument_text events text) (instrument ctxt) using
        |> Seq.filter_results
        |> Seq.pull
        |> is_some) ();
  in (result, collected_uses ctxt collector hyps_collector) end;

fun inspect params text state =
  let val (result, uses) = run params text state
  in {succeeded = (case result of Exn.Res b => b | Exn.Exn _ => false), uses = uses} end;

fun pretty_uses ctxt uses =
  let
    val items =
      uses
      |> map (fn u => (Pretty.unformatted_string_of (pretty_use ctxt u), u))
      |> sort_by #1
      |> map (fn (_, u) => Pretty.item [pretty_use ctxt u]);
  in
    Pretty.big_list
      ("theorems used in failed method application: " ^ string_of_int (length items)) items
  end;


(* command *)

fun apply_inspect (text, range as (pos, _)) state =
  let
    val ctxt = Proof.context_of state;
    fun on_use source u =
      writeln (Pretty.string_of (Pretty.block [Pretty.str ("used (" ^ source ^ "): "),
        pretty_use ctxt u]));
    fun on_loop source rules =
      let
        val what =
          (case source of
            "simp" => "Simplifier"
          | "classical" => "Classical reasoner"
          | _ => "Proof method " ^ quote source);
        val items =
          if null rules then [Pretty.item [Pretty.str "(no named theorems)"]]
          else map (Pretty.item o single o pretty_use ctxt) rules;
      in
        warning (Pretty.string_of
          (Pretty.big_list (what ^ " may be looping, repeatedly using:") items))
      end;
    val params = {every_use = Config.get ctxt every_use, on_use = on_use, on_loop = on_loop};
  in
    (case run params text state of
      (Exn.Res true, _) => Proof.apply (text, range) state
    | (result, uses) =>
        (Pretty.writeln (pretty_uses ctxt uses);
         (case result of
           Exn.Exn exn => Exn.reraise exn
         | Exn.Res _ => Seq.single (Proof_Display.method_error "" pos (Proof.raw_goal state)))))
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply_inspect\<close>
    "initial goal refinement step (unstructured), reporting theorems used if it fails"
    (Method.parse >> (fn m => (Method.report m; Toplevel.proofs (apply_inspect m))));

end;
