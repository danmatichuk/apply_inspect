(*  Title:      apply_inspect.ML

Diagnostic variant of "apply": if the proof method fails, report the
theorems that were used during the failed attempt.

The method is first run on a copy of the goal state that is produced by the
oracle of skipped proofs (so that it has no theorem dependencies of its
own), in a context where the classical reasoner and the simplifier record
every intermediate goal state they see, and the simplifier records every
rewrite rule it tries. Before each method or classical step, the goal state
is copied again in the same way, so that the result of the step depends on
exactly the theorems that the step used. The results of that run are
discarded: if the method succeeds, it is run again without instrumentation.

If the method exceeds the time limit apply_inspect_timeout (in ms), it is paused
and the command continues with the goal state that the method has reached,
as a skipped proof. The method runs in a thread of its own, which pauses at
the next point where the instrumentation is called (method or classical
step, rewrite rule or simproc). Each "back" continues it for
apply_inspect_step_time and yields the goal state that it has reached then,
so that "back" steps through the run of the method.
*)

signature APPLY_INSPECT =
sig
  val every_use: bool Config.T
  val join_timeout: int Config.T
  val timeout: int Config.T
  val step_time: int Config.T
  datatype use =
    Theorem of Thm_Name.P |
    Fact of Thm_Name.T |
    Assumption of Thm_Name.T * term |
    Rule of thm
  val use_thm: Proof.context -> use -> thm option
  val declarations: Proof.context -> use -> string list
  val pretty_use: Proof.context -> use -> Pretty.T
  type params =
   {every_use: bool,
    on_use: string -> use -> unit,
    on_loop: string -> use list -> unit}
  val inspect: params -> Method.text -> Proof.state ->
    {succeeded: bool, error: string option, uses: use list}
  val inspect_limited: params -> {timeout: Time.time, step_time: Time.time} ->
    Method.text -> Proof.state ->
    {succeeded: bool, error: string option, uses: use list,
      partial: (Time.time * Proof.state) Seq.seq}
  val pretty_uses: Proof.context -> use list -> Pretty.T
  val use_filter: Proof.state -> (bool * string Find_Theorems.criterion) list -> use -> bool
  val apply_inspect: (bool * string Find_Theorems.criterion) list option -> Method.text_range ->
    Proof.state -> Proof.state Seq.result Seq.seq
end;

structure Apply_Inspect: APPLY_INSPECT =
struct

(*report every use of a theorem, not just the first one*)
val every_use =
  Attrib.setup_config_bool \<^binding>\<open>apply_inspect_every_use\<close> (K false);

(*time limit (in milliseconds, 0 for none) for waiting on proofs of other theorems, which may
  still be running in a forked task, or never finish: their dependencies are left out*)
val join_timeout =
  Attrib.setup_config_int \<^binding>\<open>apply_inspect_join_timeout\<close> (K 100);

(*time limit (in milliseconds, 0 for none) for the method: if it is exceeded, the method is
  paused and the command continues with the goal state that it has reached, as a refinement of
  the goal by the oracle of skipped proofs*)
val timeout =
  Attrib.setup_config_int \<^binding>\<open>apply_inspect_timeout\<close> (K 0);

(*time (in milliseconds) for which each "back" after the timeout continues the method*)
val step_time =
  Attrib.setup_config_int \<^binding>\<open>apply_inspect_step_time\<close> (K 100);


(* uses *)

datatype use =
  Theorem of Thm_Name.P |  (*global theorem*)
  Fact of Thm_Name.T |  (*local fact of the proof context, e.g. result of "have"*)
  Assumption of Thm_Name.T * term |  (*assumption of the proof context, possibly unnamed*)
  Rule of thm;  (*other rule, e.g. premise of a subgoal*)

val classical_attributes =
 [(Bires.intro_bang_kind, "intro!"), (Bires.elim_bang_kind, "elim!"),
  (Bires.dest_bang_kind, "dest!"), (Bires.intro_kind, "intro"), (Bires.elim_kind, "elim"),
  (Bires.dest_kind, "dest"), (Bires.intro_query_kind, "intro?"),
  (Bires.elim_query_kind, "elim?"), (Bires.dest_query_kind, "dest?")];

fun use_name (Theorem (thm_name, _)) = thm_name
  | use_name (Fact thm_name) = thm_name
  | use_name (Assumption (thm_name, _)) = thm_name
  | use_name (Rule _) = Thm_Name.empty;

(*the theorem behind a use: named ones looked up in the context, unnamed assumptions as such*)
fun use_thm ctxt u =
  let
    fun lookup (thm_name as (name, i)) =
      if Thm_Name.is_empty thm_name then NONE
      else
        (case Facts.lookup (Context.Proof ctxt) (Proof_Context.facts_of ctxt) name of
          SOME {thms, ...} =>
            if i = 0 then (case thms of [thm] => SOME thm | _ => NONE)
            else try (nth thms) (i - 1)
        | NONE => NONE);
  in
    (case u of
      Rule thm => SOME thm
    | Assumption (thm_name, prop) =>
        (case lookup thm_name of
          NONE => try (Thm.assume o Thm.cterm_of ctxt) prop
        | some => some)
    | _ => lookup (use_name u))
  end;

(*attributes under which a used theorem is declared in the context: simp rules by name (the
  rewrite rules derived from a theorem keep its name), classical rules by proposition*)
fun declarations ctxt =
  let
    val simps =
      fold (fn ((name, i), _) => Symtab.insert_list (op =) (name, i))
        (Raw_Simplifier.dest_simps (Simplifier.simpset_of ctxt)) Symtab.empty;
    val rules = Classical.dest_decls ctxt (K true);

    fun simp (thm_name as (name, i)) =
      not (Thm_Name.is_empty thm_name) andalso member (op =) (Symtab.lookup_list simps name) i;
    fun classical thm =
      rules |> map_filter (fn (th, {kind, ...}) =>
        if Thm.eq_thm_prop (th, thm) then AList.lookup (op =) classical_attributes kind
        else NONE);
  in
    fn u =>
      (if simp (use_name u) then ["simp"] else []) @
      (case use_thm ctxt u of SOME thm => classical thm | NONE => [])
  end;

fun pretty_use ctxt =
  let
    val declared = declarations ctxt;
    fun pretty (Theorem (thm_name, _)) = Global_Theory.pretty_thm_name ctxt thm_name
      | pretty (Fact thm_name) =
          Pretty.block [Pretty.str "fact ", Proof_Context.pretty_thm_name ctxt thm_name]
      | pretty (Assumption (thm_name, prop)) =
          Pretty.block [Pretty.str "assumption ",
            if Thm_Name.is_empty thm_name then Pretty.quote (Syntax.pretty_term ctxt prop)
            else Proof_Context.pretty_thm_name ctxt thm_name]
      | pretty (Rule thm) = Pretty.block [Pretty.str "rule ", Thm.pretty_thm ctxt thm];
  in
    fn u =>
      (case distinct (op =) (declared u) of
        [] => pretty u
      | attribs =>
          Pretty.block [pretty u, Pretty.brk 1, Pretty.list "[" "]" (map Pretty.str attribs)])
  end;

(*named local facts of a proof context, without the ones that are also global*)
fun local_facts ctxt =
  Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of ctxt)]
    (Proof_Context.facts_of ctxt)
  |> filter_out (fn (name, _) => Long_Name.base_name name = "this")
  |> maps Thm_Name.make_list;

(*prefer facts that consist of a single theorem*)
fun prefer_single (thm_name: Thm_Name.T) (thm_name': Thm_Name.T) =
  if #2 thm_name = 0 andalso #2 thm_name' <> 0 then thm_name else thm_name';

(* waiting for proofs of other theorems *)

(*f x in a thread of its own, which is not a worker of the future scheduler: it only waits for
  forked proofs and never runs them itself, so that interrupting it after the timeout does not
  interrupt (and cancel) them. The caller waits with a time limit instead of Timeout.apply, which
  would interrupt the caller itself and could thus garble a timeout of an enclosing
  Timeout.apply (two interrupts at once).*)
fun join_limited timeout f x =
  let
    val result = Synchronized.var "apply_inspect_join" NONE;
    val thread =
      Isabelle_Thread.fork
        (Isabelle_Thread.params "apply_inspect_join" |> Isabelle_Thread.interrupts)
        (fn () => Synchronized.change result (K (SOME (Exn.capture0 f x))));
    fun stop () = Isabelle_Thread.interrupt_thread thread;
    val limit = if Timeout.ignored timeout then NONE else SOME (Timeout.end_time timeout);
    fun await () =
      Synchronized.timed_access result (K limit) (fn NONE => NONE | some => SOME (some, some));
  in
    (case Exn.capture_body await of
      Exn.Res (SOME (SOME (Exn.Res y))) => SOME y
    | Exn.Res (SOME _) => NONE
    | Exn.Res NONE => (stop (); NONE)
    | Exn.Exn exn => (stop (); Exn.reraise exn))
  end;

(*dependencies of a theorem, unless they wait for unfinished proofs of other theorems*)
fun thm_deps_limited ctxt =
  join_limited (Time.fromMilliseconds (Config.get ctxt join_timeout)) Thm.thm_deps;

(*dependencies of a node whose proof is finished, without waiting for it*)
fun finished_node_thms node =
  if Future.is_finished (Proofterm.thm_node_body node)
  then the_default [] (try Proofterm.thm_node_thms node)
  else [];

(*name of a node, if it names a global fact with the same statement: unlike
  Global_Theory.lookup_thm_id, this does not need the derivations of all facts of the theory,
  which wait for their proofs (in PIDE, failed or unfinished proofs do not stop the theory)*)
fun lookup_thm_node ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val facts = Global_Theory.facts_of thy;
    fun statement thm = #2 (Logic.unconstrainT (Thm.shyps_of thm) (Thm.prop_of thm));
  in
    fn node =>
      let val thm_name as (name, i) = Proofterm.thm_node_name node in
        if Thm_Name.is_empty thm_name then NONE
        else
          (case Facts.lookup (Context.Theory thy) facts name of
            SOME {thms, ...} =>
              (case if i = 0 then try the_single thms else try (nth thms) (i - 1) of
                SOME thm =>
                  if statement thm aconv Proofterm.thm_node_prop node
                  then SOME (thm_name, Position.none) else NONE
              | NONE => NONE)
          | NONE => NONE)
      end
  end;

(*local facts of a proof context, as the serials of their own (unnamed) dependency nodes, e.g.
  from the closed derivation of "have", with the serials of the other dependency nodes that
  come with them (e.g. Pure.protectD)*)
fun fact_serials ctxt lookup =
  let
    val thy = Proof_Context.theory_of ctxt;
    (*unnamed nodes, without proofs of sort constraints*)
    fun own_nodes thms =
      thms |> filter (fn (i, node) =>
        is_none (lookup node) andalso
        not (can Logic.dest_of_class (Proofterm.thm_node_prop node)));
    fun add (thm_name, thm) =
      let
        val deps =
          the_default [] (try (Thm.transfer thy) thm |> Option.mapPartial (thm_deps_limited ctxt));
      in
        (case own_nodes deps of
          [(i, node)] =>
            let
              val baggage = remove (op =) i (map #1 deps);
              (*the fact states the conclusion of the node, e.g. not a variant introduced by
                "note"*)
              val exact =
                Thm.prop_of thm aconv Logic.strip_imp_concl (Proofterm.thm_node_prop node);
              val entry = ((thm_name, baggage), exact);
              fun better (entry' as (_, exact')) =
                if exact <> exact' then if exact then entry else entry'
                else if prefer_single thm_name (#1 (#1 entry')) = thm_name then entry else entry';
            in Inttab.map_default (i, entry) better end
        | _ => I)
      end;
  in Inttab.build (fold add (local_facts ctxt)) |> Inttab.map (K #1) end;

(*names of the assumptions of a proof context, as local facts*)
fun assumption_names ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
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
    val candidates = fold add (local_facts ctxt) [];
    (*prefer the assumption itself, single facts, and specific names over "assms"*)
    fun rank (((name, i), exact)) =
      (if exact then 0 else 4) + (if i = 0 then 0 else 2) +
      (if Long_Name.base_name name = "assms" then 1 else 0);
  in
    Termtab.build (fold (fn (hyp, candidate) =>
      Termtab.map_default (hyp, candidate) (fn candidate' =>
        if rank candidate < rank candidate' then candidate else candidate')) candidates)
    |> Termtab.map (K #1)
  end;


(* fresh goal state without dependencies *)

(*goal states are produced by the oracle of skipped proofs, which every theory has, and
  transferred to the private theory of the run*)
fun fresh_state_of thy = Thm.transfer thy o Skip_Proof.make_thm_cterm;

(*copy of the goal state without dependencies, with the same hypotheses, unless the copy would
  differ in flex-flex constraints or sort hypotheses (which would affect the behaviour of
  tactics)*)
fun refresh_state fresh_state st =
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

(*Reading a method runs it once on a dummy goal state (Method.method_closure), which is not
  part of the run.*)
val closure_state = Thm.prop_of (Goal.protect 0 Drule.dummy_thm);
fun is_closure_state st = Thm.prop_of st aconv closure_state;

(*proposition of an intermediate goal state as a refinement of the goal, with the subgoals that
  goal restriction hides (Goal.restrict, e.g. in SELECT_GOAL) in a different order; NONE for
  goal states of other goals, e.g. of conditions of rewrite rules or of focused subgoals*)
fun goal_refinement goal st =
  let
    val concl = Thm.concl_of goal;
    fun unfold prems t =
      if t aconv concl then SOME (Logic.list_implies (prems, t))
      else
        (case try Logic.unprotect t of
          SOME u => unfold (prems @ Logic.strip_imp_prems u) (Logic.strip_imp_concl u)
        | NONE => NONE);
  in
    if subset (op aconv) (Thm.hyps_of st, Thm.hyps_of goal)
    then unfold (Thm.prems_of st) (Thm.concl_of st) else NONE
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

(*named theorems and facts behind dependency nodes, without those already seen;
  see also Thm_Deps.thm_deps*)
fun resolve_deps lookup seen thms =
  let
    fun deps (i, thm_node) tab =
      if Inttab.defined seen i orelse Inttab.defined tab i then tab
      else
        (case lookup (i, thm_node) of
          SOME u => Inttab.update (i, SOME u) tab
        | NONE =>
            Inttab.update (i, NONE) tab
            |> fold deps (finished_node_thms thm_node));
  in Inttab.build (fold deps thms) end;

fun uses_of tab = Inttab.fold_rev (fn (_, SOME u) => cons u | _ => I) tab [];

(*theorems and facts as keys for comparison*)
fun use_key (Theorem (thm_name, _)) = SOME (0, thm_name)
  | use_key (Fact thm_name) = SOME (1, thm_name)
  | use_key _ = NONE;

fun key_use (0, thm_name) = Theorem (thm_name, Position.none)
  | key_use (_, thm_name) = Fact thm_name;

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
    val facts = Global_Theory.facts_of thy;
    val thm_deps = thm_deps_limited ctxt;
    val lookup_node = lookup_thm_node ctxt;
    val fact_serials = fact_serials ctxt lookup_node;
    fun lookup (i, thm_node) =
      (case Inttab.lookup fact_serials i of
        SOME (thm_name, _) => SOME (Fact thm_name)
      | NONE => Option.map Theorem (lookup_node thm_node));

    (*named nodes that come with a local fact are not reported separately*)
    fun resolve seen thms =
      let
        val tab = resolve_deps lookup seen thms;
        val baggage =
          Inttab.fold (fn (i, _) =>
            (case Inttab.lookup fact_serials i of
              SOME (_, js) => fold (fn j => if Inttab.defined tab j then cons j else I) js
            | NONE => I)) tab [];
      in fold (fn j => Inttab.update (j, NONE)) baggage tab end;
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

    fun emit source uses hyps =
      (List.app (on_use source) uses; List.app (on_use source o assumption) hyps);

    (*first uses*)
    fun observe source st =
      let
        val names =
          (case thm_deps st of
            SOME thms => add_deps (resolve (Synchronized.value collector) thms)
          | NONE => []);
        val hyps = add_hyps (context_hyps (Thm.hyps_of st));
      in if every_use then () else emit source names hyps end;

    (*every use*)
    fun use source thms hyps =
      let val tab = resolve Inttab.empty thms
      in add_deps tab; add_hyps hyps; emit source (uses_of tab) hyps end;


    (* steps *)

    val step_loops = Synchronized.var "apply_inspect_step_loops" Symtab.empty;

    fun step source {input, start, output, size} =
      let
        val used =
          (case (thm_deps start, thm_deps output) of
            (SOME thms, SOME thms') =>
              let
                val tab = resolve Inttab.empty (Ord_List.subtract Proofterm.thm_ord thms thms');
                val hyps =
                  context_hyps (subtract (op aconv) (Thm.hyps_of start) (Thm.hyps_of output));
              in SOME (tab, hyps) end
          | _ => NONE);
        val _ =
          (case used of
            SOME (tab, hyps) =>
              if every_use then (add_deps tab; add_hyps hyps; emit source (uses_of tab) hyps)
              else observe source output
          | NONE => observe source output);
        val rule =
          (case used of
            SOME (tab, hyps) =>
              (sort_distinct (prod_ord int_ord Thm_Name.ord) (map_filter use_key (uses_of tab)),
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
          in on_loop source (map key_use names @ map assumption hyps) end)
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
        | _ =>
            (case try (Thm.transfer thy) rule |> Option.mapPartial thm_deps of
              SOME thms =>
                (case get_first (Inttab.lookup fact_serials o #1) thms of
                  SOME (thm_name, _) => Fact thm_name
                | NONE => Rule rule)
            | NONE => Rule rule));

    fun rewrite {instance, rule, name, redex, result} =
      let
        val _ =
          if every_use andalso Facts.defined facts (#1 name) then
            (observe "simp" instance; on_use "simp" (Theorem (name, Position.none)))
          else if every_use then
            use "simp" (the_default [] (thm_deps instance))
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
    uses_of (Synchronized.value collector) @
      map (fn hyp => Assumption (name hyp, hyp)) (Termtab.keys (Synchronized.value hyps_collector))
  end;


(* instrumentation *)

val hook_name = "apply_inspect";

(*checkpoint: called where the method may be paused*)

fun instrument_context fresh_state checkpoint ({observe, step, ...}: events) ctxt =
  let
    fun wrapper _ tac i st =
      if is_closure_state st then tac i st
      else
        let
          val _ = checkpoint ();
          val _ = observe "classical" st;
          val st0 = refresh_state fresh_state st;
          val size =
            (case try (Thm.cprem_of st) i of
              SOME ct => size_of_term (Thm.term_of ct)
            | NONE => 0);
          fun step_output st' =
            step "classical" {input = st, start = st0, output = st', size = size};
        in Seq.map (tap step_output) (tac i st0) end;
    fun observe_tac (_: Proof.context) (_: int) st =
      (if is_closure_state st then () else observe "simp" st; Seq.empty);
    val solver = Simplifier.mk_solver hook_name observe_tac;
  in
    ctxt
    |> (fn ctxt => Classical.addSWrapper (ctxt, (hook_name, wrapper)))
    |> (fn ctxt => Classical.addWrapper (ctxt, (hook_name, wrapper)))
    |> Simplifier.add_loop (hook_name, observe_tac)
    |> Simplifier.add_unsafe_solver solver
    |> Simplifier.add_safe_solver solver
  end;

fun simp_trace_ops checkpoint ({rewrite, ...}: events) : Raw_Simplifier.trace_ops =
 {trace_invoke = K I,
  trace_rrule = fn {thm, rrule = {thm = rule, name, ...}, cterm, ...} => fn ctxt => fn cont =>
    let
      val _ = checkpoint ();
      val res = cont ctxt;
      val result = Option.map (Thm.term_of o Thm.rhs_of o #1) res;
      val _ =
        rewrite {instance = thm, rule = rule, name = name, redex = Thm.term_of cterm,
          result = result};
    in res end,
  trace_simproc = K (fn ctxt => fn cont => (checkpoint (); cont ctxt))};

fun instrument_text fresh_state checkpoint ({observe, step, ...}: events) =
  let
    fun wrap_method source (m: Method.method) : Method.method = fn facts => fn (ctxt, st) =>
      if is_closure_state st then m facts (ctxt, st)
      else
        let
          val _ = checkpoint ();
          val _ = observe source st;
          val st0 = refresh_state fresh_state st;
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

(*The method runs in a thread of its own if it has a time limit: once its time is up, it pauses
  at the next checkpoint until it is continued. The goal states that it reaches later hold a
  token, which the paused method refers to only weakly: when they are gone (e.g. because the
  command has been removed from the document), the method is interrupted.*)
datatype control = Run of Time.time | Pause | Done of bool Exn.result;

(*how often a paused method checks whether its goal states are still referenced*)
val pause_check = seconds 1.0;

(*goal state reached by a run of the method after the time limit: running time, refinement of
  the goal (if any), and the outcome, if the method has finished*)
type progress = {time: Time.time, refinement: term option, finished: bool Exn.result option};

(*result: outcome of the method (TIMEOUT if it exceeds the time limit), theorems used, and the
  goal states that it reaches: at the time limit, and after each further step, until it has
  finished*)
fun run params {timeout, step_time} text state =
  let
    val _ = Proof.assert_backward state;
    val ctxt = Proof.context_of state;
    val {context = goal_ctxt, facts = using, goal} = Proof.raw_goal state;
    val limited = not (Timeout.ignored timeout);

    (*messages of the instrumentation go to the command that has continued the method last*)
    val output_pos = Synchronized.var "apply_inspect_output" (Position.thread_data ());
    fun output f x = Position.setmp_thread_data (Synchronized.value output_pos) f x;
    val params' =
     {every_use = #every_use params,
      on_use = fn source => output (#on_use params source),
      on_loop = fn source => output (#on_loop params source)};

    val collector = Synchronized.var "apply_inspect" Inttab.empty;
    val hyps_collector = Synchronized.var "apply_inspect_hyps" Termtab.empty;

    (*the goal state that the method last reached*)
    val last = Synchronized.var "apply_inspect_last" NONE;
    fun record st =
      (case goal_refinement goal st of
        SOME prop => Synchronized.change last (K (SOME prop))
      | NONE => ());
    fun refinement () =
      Synchronized.value last |> Option.mapPartial (fn prop =>
        if prop aconv Thm.prop_of goal then NONE else SOME prop);
    val events =
      let val {observe, step, rewrite} = make_events ctxt collector hyps_collector params' in
        {observe = observe, rewrite = rewrite,
          step = fn source => fn args as {output, ...} => (record output; step source args)}
      end;

    val start = Time.now ();
    val control =
      Synchronized.var "apply_inspect_control" (Run (start + Timeout.scale_time timeout));
    val token = Unsynchronized.ref ();
    val token_ref = Weak.weak (SOME token);
    fun wait_continued () =
      let val limit = Time.now () + pause_check in
        (case Synchronized.timed_access control (K (SOME limit))
            (fn Pause => NONE | c => SOME ((), c)) of
          SOME () => ()
        | NONE =>
            if is_some (! token_ref) then wait_continued ()
            else Isabelle_Thread.raise_interrupt ())
      end;
    fun checkpoint () =
      if not limited then ()
      else
        (case Synchronized.value control of
          Run deadline =>
            if Time.now () < deadline then ()
            else
              (Synchronized.change control (fn c as Run deadline =>
                  if Time.now () < deadline then c else Pause
                | c => c);
               wait_continued ())
        | _ => ());

    (*the results of the run are discarded, so its contexts may live in a private theory*)
    val thy' =
      Proof_Context.theory_of ctxt
      |> Raw_Simplifier.set_trace_ops (simp_trace_ops checkpoint events);
    val fresh_state = fresh_state_of thy';
    val instrument =
      Proof_Context.transfer thy' #> instrument_context fresh_state checkpoint events;

    fun evaluate () =
      (instrument goal_ctxt, fresh_state (Thm.cprop_of goal))
      |> Method.evaluate (instrument_text fresh_state checkpoint events text) (instrument ctxt)
        using
      |> Seq.filter_results
      |> Seq.pull
      |> Option.map (fn ((_, st), _) => record st)
      |> is_some;

    fun uses () = collected_uses ctxt collector hyps_collector;
  in
    if not limited then {result = Exn.result evaluate (), uses = uses (), progress = Seq.empty}
    else
      let
        val pos = Position.thread_data ();
        val context = Context.get_generic_context ();
        val worker =
          Isabelle_Thread.fork (Isabelle_Thread.params "apply_inspect" |> Isabelle_Thread.interrupts)
            (fn () =>
              let
                val result =
                  Exn.capture0
                    (Position.setmp_thread_data pos (Context.setmp_generic_context context evaluate))
                    ();
              in Synchronized.change control (K (Done result)) end);

        (*wait until the method pauses or finishes, or until the given time, if it does not reach
          a checkpoint (it then continues until it does)*)
        fun await limit =
          Synchronized.timed_access control (K (SOME limit))
            (fn Run _ => NONE | c => SOME (c, c));

        fun progress time c =
          let
            val finished = (case c of SOME (Done result) => SOME result | _ => NONE);
            val rest =
              if is_some finished then Seq.empty
              else Seq.make (fn () => Seq.pull (continue time));
          in Seq.cons {time = time, refinement = refinement (), finished = finished} rest end
        and continue time =
          let
            val _ = Weak.touch token;
            val _ = Synchronized.change output_pos (K (Position.thread_data ()));
            val t0 = Time.now ();
            val step = Timeout.scale_time step_time;
            val _ = Synchronized.change control (fn c as Done _ => c | _ => Run (t0 + step));
            val c = await (t0 + step + step);
          in progress (time + (Time.now () - t0)) c end;

        (*the command may be interrupted while it waits*)
        val c =
          (case Exn.capture_body (fn () => await (start + Timeout.scale_time (timeout + step_time))) of
            Exn.Res c => c
          | Exn.Exn exn => (Isabelle_Thread.interrupt_thread worker; Exn.reraise exn));
        val time = Time.now () - start;
      in
        (case c of
          SOME (Done result) => {result = result, uses = uses (), progress = Seq.empty}
        | _ =>
            {result = Exn.Exn (Timeout.TIMEOUT time), uses = uses (), progress = progress time c})
      end
  end;

(*proof state with the goal refined to the given proposition by the oracle of skipped proofs, as
  after "apply" (goal states of the run belong to its private theory)*)
fun refine_by_oracle state prop =
  state
  |> Proof.refine_primitive (fn ctxt => fn _ => Skip_Proof.make_thm_cterm (Thm.cterm_of ctxt prop))
  |> Proof.using_facts [];

fun refined_state state NONE = state
  | refined_state state (SOME prop) = refine_by_oracle state prop;

(*error: exception raised by the method or by the instrumentation, as opposed to plain failure;
  partial: if the method exceeds the time limit, the proof states with the goal states that it
  reaches (the given state while there is none), with its running time: at the time limit, and
  after each further step, until it has finished (the last one is its result if it succeeds)*)
fun inspect_limited params limits text state =
  let
    val {result, uses, progress} = run params limits text state;
    fun partial xq =
      Seq.make (fn () =>
        (case Seq.pull xq of
          SOME ({time, refinement, finished = NONE}, xq') =>
            SOME ((time, refined_state state refinement), partial xq')
        | SOME ({time, refinement, finished = SOME (Exn.Res true)}, _) =>
            SOME ((time, refined_state state refinement), Seq.empty)
        | _ => NONE));
  in
    (case result of
      Exn.Res b => {succeeded = b, error = NONE, uses = uses, partial = Seq.empty}
    | Exn.Exn exn =>
        {succeeded = false, error = SOME (Runtime.exn_message exn), uses = uses,
          partial = partial progress})
  end;

fun inspect params text state =
  let
    val {succeeded, error, uses, ...} =
      inspect_limited params {timeout = Time.zeroTime, step_time = Time.zeroTime} text state
  in {succeeded = succeeded, error = error, uses = uses} end;

fun pretty_use_list header ctxt uses =
  let
    val pretty = pretty_use ctxt;
    val items =
      uses
      |> map (fn u => let val prt = pretty u in (Pretty.unformatted_string_of prt, prt) end)
      |> sort_by #1
      |> map (fn (_, prt) => Pretty.item [prt]);
  in
    Pretty.big_list (header ^ ": " ^ string_of_int (length items)) items
  end;

val pretty_uses = pretty_use_list "theorems used in failed method application";


(* filter *)

(*uses that are named facts meeting the given find_theorems criteria*)
fun use_filter state criteria =
  let
    val ctxt = Proof.context_of state;
    val goal = try (#goal o Proof.simple_goal) state;
    (*without a limit, find_theorems still truncates to find_theorems_limit*)
    val unlimited = SOME (length (Find_Theorems.all_facts_of ctxt));
    val (_, found) = Find_Theorems.find_theorems_cmd ctxt goal unlimited false criteria;
    val names = Thm_Name.Set.make (map #1 found);
    fun named thm_name = Thm_Name.Set.member names thm_name;
  in
    fn Theorem (thm_name, _) => named thm_name
     | Fact thm_name => named thm_name
     | Assumption (thm_name, _) => named thm_name
     | Rule _ => false
  end;


(* command *)

(*the command is a diagnostic tool, not meant to stay in a proof*)
fun report_bad () =
  Output.report [Markup.markup (Markup.bad ()) "Diagnostic proof command"];

fun apply_inspect criteria (text, range as (pos, _)) state =
  let
    val _ = report_bad ();
    val ctxt = Proof.context_of state;
    val pretty = pretty_use ctxt;
    val printed =
      (case criteria of
        SOME criteria => use_filter state criteria
      | NONE => K true);
    fun on_use source u =
      if printed u then
        writeln (Pretty.string_of (Pretty.block [Pretty.str ("used (" ^ source ^ "): "),
          pretty u]))
      else ();
    fun on_loop source rules =
      let
        val what =
          (case source of
            "simp" => "Simplifier"
          | "classical" => "Classical reasoner"
          | _ => "Proof method " ^ quote source);
        val items =
          if null rules then [Pretty.item [Pretty.str "(no named theorems)"]]
          else map (Pretty.item o single o pretty) rules;
      in
        warning (Pretty.string_of
          (Pretty.big_list (what ^ " may be looping, repeatedly using:") items))
      end;
    val params = {every_use = Config.get ctxt every_use, on_use = on_use, on_loop = on_loop};
    val limits =
     {timeout = Time.fromMilliseconds (Config.get ctxt timeout),
      step_time = Time.fromMilliseconds (Config.get ctxt step_time)};
    fun ms t = string_of_int (Time.toMilliseconds t) ^ " ms";
    val continue_msg = "\"back\" continues it for " ^ ms (#step_time limits);

    (*the goal states that the method reaches, as alternative results for "back"; each one is
      reported when it is reached*)
    fun results first prev xq =
      Seq.make (fn () =>
        (case Seq.pull xq of
          NONE => NONE
        | SOME ({time, refinement, finished}, xq') =>
            let
              val after = " after " ^ ms time;
              val goal_state =
                (case refinement of
                  NONE => "the unchanged goal"
                | SOME prop =>
                    "the goal state reached" ^
                    (case prev of
                      SOME prop' => if prop aconv prop' then " (unchanged)" else ""
                    | NONE => "") ^ " (skipped proof)");
              val state' = refined_state state refinement;
            in
              (case finished of
                NONE =>
                  (warning ((if first then "Timeout" ^ after ^ ": method paused at "
                      else "Method paused" ^ after ^ " at ") ^ goal_state ^ "; " ^ continue_msg);
                   SOME (Seq.Result state', results false refinement xq'))
              | SOME (Exn.Res true) =>
                  (warning ("Method finished" ^ after ^ " with " ^ goal_state);
                   SOME (Seq.Result state', Seq.empty))
              | SOME (Exn.Res false) => (warning ("Method failed" ^ after); NONE)
              | SOME (Exn.Exn exn) =>
                  (warning ("Method failed" ^ after ^ ": " ^ Runtime.exn_message exn); NONE))
            end));
  in
    (case run params limits text state of
      {result = Exn.Res true, ...} => Proof.apply (text, range) state
    | {result = Exn.Exn (Timeout.TIMEOUT _), uses, progress} =>
        (Pretty.writeln (pretty_use_list "theorems used before the timeout" ctxt
          (filter printed uses));
         results true NONE progress)
    | {result, uses, ...} =>
        (Pretty.writeln (pretty_uses ctxt (filter printed uses));
         (case result of
           Exn.Exn exn => Exn.reraise exn
         | Exn.Res _ => Seq.single (Proof_Display.method_error "" pos (Proof.raw_goal state)))))
  end;

val criteria =
  Scan.option (Parse.$$$ "[" |-- Parse.!!! (Find_Theorems.query_parser --| Parse.$$$ "]"));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply_inspect\<close>
    "initial goal refinement step (unstructured), reporting theorems used if it fails"
    (criteria -- Method.parse >> (fn (crit, m) =>
      (Method.report m;
        Toplevel.proofs (apply_inspect crit m) o Toplevel.skip_proof report_bad)));

end;
