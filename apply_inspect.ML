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
  type params =
   {every_use: bool,
    on_use: string -> Thm_Name.P -> unit,
    on_loop: (Thm_Name.T * thm) list -> unit}
  val inspect: params -> Method.text -> Proof.state -> {succeeded: bool, deps: Thm_Name.P list}
  val pretty_deps: Proof.context -> Thm_Name.P list -> Pretty.T
  val apply_inspect: Method.text_range -> Proof.state -> Proof.state Seq.result Seq.seq
end;

structure Apply_Inspect: APPLY_INSPECT =
struct

(*report every use of a theorem, not just the first one*)
val every_use =
  Attrib.setup_config_bool \<^binding>\<open>apply_inspect_every_use\<close> (K false);


(* fresh goal state without dependencies *)

val (_, fresh_state) =
  Context.>>> (Context.map_theory_result (Thm.add_oracle (\<^binding>\<open>apply_inspect\<close>, I)));

(*copy of the goal state without dependencies, unless the copy would differ in hypotheses or
  flex-flex constraints (which would affect the behaviour of tactics)*)
fun refresh_state st =
  (case try fresh_state (Thm.cprop_of st) of
    SOME st' => if Thm.eq_thm (st, st') then st' else st
  | NONE => st);


(* loop detection *)

(*The simplifier is suspected to loop if it keeps rewriting its own output with a periodic
  sequence of rules, without making terms smaller: for some period p, each of the last
  loop_repetitions * p rewrite steps tries the same rule as the step p steps before, on a
  term that is at least as large, and that is a subterm of the result of the preceding
  step. Terminating evaluation of recursive functions usually makes terms smaller.*)

val loop_max_period = 8;
val loop_repetitions = 10;

type rewrite_step =
  {rule: thm, name: Thm_Name.T, redex: term, redex_size: int, result: term option};

type loop_state =
 {recent: rewrite_step list,  (*previous steps, most recent first*)
  runs: int list,  (*for each period: number of consecutive steps that repeat its rules
                      without shrinking*)
  chain: int,  (*number of consecutive steps that rewrite the preceding result*)
  reported: thm list list};  (*rules of cycles reported so far*)

val init_loop_state: loop_state =
  {recent = [], runs = replicate loop_max_period 0, chain = 0, reported = []};

(*result: rules of a newly suspected cycle*)
fun add_rewrite_step (step: rewrite_step) ({recent, runs, chain, reported}: loop_state) =
  let
    val chain' =
      (case recent of
        {result = SOME result, ...} :: _ =>
          if exists_subterm (fn t => t aconv #redex step) result then chain + 1 else 0
      | _ => 0);
    val runs' =
      runs |> map_index (fn (k, run) =>
        (case try (nth recent) k of
          SOME step' =>
            if Thm.eq_thm_prop (#rule step, #rule step') andalso
              #redex_size step >= #redex_size step'
            then run + 1 else 0
        | NONE => 0));
    val steps = step :: recent;

    fun periodic (k, run) =
      let val n = (k + 1) * (loop_repetitions - 1)
      in run >= n andalso chain' >= n end;
    val new_cycle =
      (case find_index periodic (map_index I runs') of
        ~1 => NONE
      | k =>
          let
            val rules =
              rev (take (k + 1) steps)
              |> map (fn {name, rule, ...} => (name, rule))
              |> distinct (Thm.eq_thm_prop o apply2 #2);
          in
            if exists (fn rules' => eq_set Thm.eq_thm_prop (map #2 rules, rules')) reported
            then NONE else SOME rules
          end);
    val reported' =
      (case new_cycle of SOME rules => map #2 rules :: reported | NONE => reported);
    val state' =
      {recent = take loop_max_period steps, runs = runs', chain = chain', reported = reported'};
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
    step -- goal state before and after an inference step,
    rewrite -- rewrite rule tried by the simplifier*)
type events =
 {observe: string -> thm -> unit,
  step: string -> thm -> thm -> unit,
  rewrite: {instance: thm, rule: thm, name: Thm_Name.T, redex: term, result: term option} ->
    unit};

type params =
 {every_use: bool,
  on_use: string -> Thm_Name.P -> unit,
  on_loop: (Thm_Name.T * thm) list -> unit};

(*collector: serial of each dependency seen so far, with its name if it is a named theorem*)
fun make_events thy collector ({every_use, on_use, on_loop}: params) : events =
  let
    val loop_state = Synchronized.var "apply_inspect_loop" init_loop_state;

    val lookup = Global_Theory.lookup_thm_id thy;
    val facts = Global_Theory.facts_of thy;

    fun add (i, entry) (names, seen) =
      if Inttab.defined seen i then (names, seen)
      else (the_list entry @ names, Inttab.update (i, entry) seen);
    fun add_deps tab = rev (Synchronized.change_result collector (Inttab.fold add tab o pair []));

    fun observe_deps source thms =
      let val new = add_deps (resolve_deps lookup (Synchronized.value collector) thms)
      in if every_use then () else List.app (on_use source) new end;
    fun use_deps source thms =
      let val tab = resolve_deps lookup Inttab.empty thms
      in add_deps tab; List.app (on_use source) (names_of tab) end;

    fun observe source st = Option.app (observe_deps source) (try Thm.thm_deps st);
    fun step source st st' =
      if every_use then
        (case (try Thm.thm_deps st, try Thm.thm_deps st') of
          (SOME thms, SOME thms') =>
            use_deps source (Ord_List.subtract Proofterm.thm_ord thms thms')
        | _ => observe source st')
      else observe source st';
    fun rewrite {instance, rule, name, redex, result} =
      (if every_use andalso Facts.defined facts (#1 name) then
        (observe "simp" instance; on_use "simp" (name, Position.none))
       else if every_use then Option.app (use_deps "simp") (try Thm.thm_deps instance)
       else observe "simp" instance;
       Synchronized.change_result loop_state
        (add_rewrite_step
          {rule = rule, name = name, redex = redex, redex_size = size_of_term redex,
            result = result})
       |> Option.app on_loop);
  in {observe = observe, step = step, rewrite = rewrite} end;

fun collected_deps collector = names_of (Synchronized.value collector);


(* instrumentation *)

val hook_name = "apply_inspect";

fun instrument_context ({observe, step, ...}: events) ctxt =
  let
    fun wrapper _ tac i st =
      let
        val _ = observe "classical" st;
        val st0 = refresh_state st;
      in Seq.map (tap (step "classical" st0)) (tac i st0) end;
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
          ((case result of Seq.Result (_, st') => step source st0 st' | Seq.Error _ => ());
            result))
      end;
    fun wrap (Method.Source src) =
          Method.Basic (fn ctxt =>
            wrap_method (#1 (Token.name_of_src src)) (Method.method_cmd ctxt src ctxt))
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
    val events = make_events (Proof_Context.theory_of ctxt) collector params;

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
  in (result, collected_deps collector) end;

fun inspect params text state =
  let val (result, deps) = run params text state
  in {succeeded = (case result of Exn.Res b => b | Exn.Exn _ => false), deps = deps} end;

fun pretty_deps ctxt deps =
  let
    val thy = Proof_Context.theory_of ctxt;
    val extern_fact = Name_Space.extern ctxt (Facts.space_of (Global_Theory.facts_of thy));
    val items =
      deps
      |> map (fn (thm_name as (name, _), _) => (extern_fact name, thm_name))
      |> sort_by #1
      |> map (fn (_, thm_name) => Pretty.item [Global_Theory.pretty_thm_name ctxt thm_name]);
  in
    Pretty.big_list
      ("theorems used in failed method application: " ^ string_of_int (length items)) items
  end;


(* command *)

fun apply_inspect (text, range as (pos, _)) state =
  let
    val ctxt = Proof.context_of state;
    fun on_use source (thm_name, _) =
      writeln (Pretty.string_of (Pretty.block [Pretty.str ("used (" ^ source ^ "): "),
        Global_Theory.pretty_thm_name ctxt thm_name]));
    fun pretty_rule (name, rule) =
      if Facts.defined (Global_Theory.facts_of (Proof_Context.theory_of ctxt)) (#1 name)
      then Global_Theory.pretty_thm_name ctxt name
      else Thm.pretty_thm ctxt rule;
    fun on_loop rules =
      warning (Pretty.string_of (Pretty.big_list "Simplifier may be looping, repeatedly trying:"
        (map (Pretty.item o single o pretty_rule) rules)));
    val params = {every_use = Config.get ctxt every_use, on_use = on_use, on_loop = on_loop};
  in
    (case run params text state of
      (Exn.Res true, _) => Proof.apply (text, range) state
    | (result, deps) =>
        (Pretty.writeln (pretty_deps ctxt deps);
         (case result of
           Exn.Exn exn => Exn.reraise exn
         | Exn.Res _ => Seq.single (Proof_Display.method_error "" pos (Proof.raw_goal state)))))
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply_inspect\<close>
    "initial goal refinement step (unstructured), reporting theorems used if it fails"
    (Method.parse >> (fn m => (Method.report m; Toplevel.proofs (apply_inspect m))));

end;
