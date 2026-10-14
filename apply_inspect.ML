(*  Title:      apply_inspect.ML

Diagnostic variant of "apply": if the proof method fails, report the
theorems that were used during the failed attempt.

The method is first run on a copy of the goal state that is produced by an
oracle (so that it has no theorem dependencies of its own), in a context
where the classical reasoner and the simplifier record every intermediate
goal state they see, and the simplifier records every rewrite rule it
tries. The results of that run are always discarded: if the method
succeeds, it is run again without instrumentation.
*)

signature APPLY_INSPECT =
sig
  val inspect: (Thm_Name.P -> unit) -> Method.text -> Proof.state ->
    {succeeded: bool, deps: Thm_Name.P list}
  val pretty_deps: Proof.context -> Thm_Name.P list -> Pretty.T
  val apply_inspect: Method.text_range -> Proof.state -> Proof.state Seq.result Seq.seq
end;

structure Apply_Inspect: APPLY_INSPECT =
struct

(* fresh goal state without dependencies *)

val (_, fresh_state) =
  Context.>>> (Context.map_theory_result (Thm.add_oracle (\<^binding>\<open>apply_inspect\<close>, I)));


(* collect dependencies of intermediate goal states *)

(*collector: serial of each dependency seen so far, with its name if it is a named theorem;
  see also Thm_Deps.thm_deps*)
fun record_deps thy collector on_use =
  let
    val lookup = Global_Theory.lookup_thm_id thy;
    fun new_deps seen (i, thm_node) tab =
      if Inttab.defined seen i orelse Inttab.defined tab i then tab
      else
        (case lookup (Proofterm.thm_id (i, thm_node)) of
          SOME thm_name => Inttab.update (i, SOME thm_name) tab
        | NONE =>
            Inttab.update (i, NONE) tab
            |> fold (new_deps seen) (Proofterm.thm_node_thms thm_node));
    fun add (i, entry) (names, seen) =
      if Inttab.defined seen i then (names, seen)
      else (the_list entry @ names, Inttab.update (i, entry) seen);
  in
    fn st =>
      (case try Thm.thm_deps st of
        SOME thms =>
          let
            val seen = Synchronized.value collector;
            val tab = Inttab.build (fold (new_deps seen) thms);
            val names = Synchronized.change_result collector (Inttab.fold add tab o pair []);
          in List.app on_use (rev names) end
      | NONE => ())
  end;

fun collected_deps collector =
  Inttab.fold_rev (fn (_, SOME thm_name) => cons thm_name | _ => I)
    (Synchronized.value collector) [];


(* instrumentation *)

val hook_name = "apply_inspect";

fun instrument_context record ctxt =
  let
    fun wrapper _ tac i st = (record st; Seq.map (tap record) (tac i st));
    fun record_tac (_: Proof.context) (_: int) st = (record st; Seq.empty);
    val solver = Simplifier.mk_solver hook_name record_tac;
  in
    ctxt
    |> (fn ctxt => Classical.addSWrapper (ctxt, (hook_name, wrapper)))
    |> (fn ctxt => Classical.addWrapper (ctxt, (hook_name, wrapper)))
    |> Simplifier.add_loop (hook_name, record_tac)
    |> Simplifier.add_unsafe_solver solver
    |> Simplifier.add_safe_solver solver
  end;

fun simp_trace_ops record : Raw_Simplifier.trace_ops =
 {trace_invoke = K I,
  trace_rrule = fn {thm, ...} => fn ctxt => fn cont => (record thm; cont ctxt),
  trace_simproc = K (fn ctxt => fn cont => cont ctxt)};

fun instrument_text record =
  let
    fun wrap_method (m: Method.method) : Method.method = fn facts => fn (ctxt, st) =>
      (record st;
        m facts (ctxt, st) |> Seq.map (fn result =>
          ((case result of Seq.Result (_, st') => record st' | Seq.Error _ => ()); result)));
    fun wrap (Method.Source src) =
          Method.Basic (fn ctxt => wrap_method (Method.method_cmd ctxt src ctxt))
      | wrap (Method.Basic m) = Method.Basic (wrap_method o m)
      | wrap (Method.Combinator (info, comb, txts)) =
          Method.Combinator (info, comb, map wrap txts);
  in wrap end;


(* inspect *)

fun run on_use text state =
  let
    val _ = Proof.assert_backward state;
    val ctxt = Proof.context_of state;
    val {context = goal_ctxt, facts = using, goal} = Proof.raw_goal state;

    val collector = Synchronized.var "apply_inspect" Inttab.empty;
    val record = record_deps (Proof_Context.theory_of ctxt) collector on_use;

    (*the results of the run are discarded, so its contexts may live in a private theory*)
    val thy' = Raw_Simplifier.set_trace_ops (simp_trace_ops record) (Proof_Context.theory_of ctxt);
    val instrument = Proof_Context.transfer thy' #> instrument_context record;

    val result =
      Exn.result (fn () =>
        (instrument goal_ctxt, fresh_state (Thm.cprop_of goal))
        |> Method.evaluate (instrument_text record text) (instrument ctxt) using
        |> Seq.filter_results
        |> Seq.pull
        |> is_some) ();
  in (result, collected_deps collector) end;

fun inspect on_use text state =
  let val (result, deps) = run on_use text state
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
    fun on_use (thm_name, _) =
      writeln (Pretty.string_of (Pretty.block [Pretty.str "used: ",
        Global_Theory.pretty_thm_name ctxt thm_name]));
  in
    (case run on_use text state of
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
