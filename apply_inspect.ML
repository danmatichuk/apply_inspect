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

(*Global_Theory.lookup_thm_id builds the name table of a theory from the derivations of all of
  its facts, which joins their proofs: a single failed proof makes every lookup in that theory
  fail. This happens in PIDE, where a failed proof of an earlier theorem does not stop the
  theory. Such theories get a table of their own here, without the facts whose proofs fail.*)
fun lookup_thm_id thy =
  let
    val global_lookup = Global_Theory.lookup_thm_id thy;
    val theories =
      Symtab.build (Theory.nodes_of thy |> fold (fn thy' =>
        Symtab.update (Context.theory_long_name thy', thy')));
    fun make_thm_names thy' =
      Global_Theory.dest_thms true (Theory.parents_of thy') thy'
      |> fold (fn (thm_name, thm) =>
          (case try Thm.derivation_id (Thm.transfer thy' thm) of
            SOME (SOME {serial, ...}) => Inttab.default (serial, thm_name)
          | _ => I))
      |> (fn f => f Inttab.empty);
    val own_tables = Synchronized.var "apply_inspect_thm_names" Symtab.empty;
    fun own_table theory_name =
      Synchronized.change_result own_tables (fn tabs =>
        (case Symtab.lookup tabs theory_name of
          SOME tab => (tab, tabs)
        | NONE =>
            let
              val tab =
                Lazy.lazy (fn () =>
                  (case Symtab.lookup theories theory_name of
                    SOME thy' => make_thm_names thy'
                  | NONE => Inttab.empty));
            in (tab, Symtab.update (theory_name, tab) tabs) end));
    fun own_lookup (thm_id: Proofterm.thm_id) =
      Inttab.lookup (Lazy.force (own_table (#theory_name thm_id))) (#serial thm_id);
  in
    fn thm_id =>
      if Symtab.defined (Synchronized.value own_tables) (#theory_name thm_id)
      then own_lookup thm_id
      else
        (case Exn.result global_lookup thm_id of
          Exn.Res res => res
        | Exn.Exn _ => own_lookup thm_id)
  end;

(*local facts of a proof context, as the serials of their own (unnamed) dependency nodes, e.g.
  from the closed derivation of "have", with the serials of the other dependency nodes that
  come with them (e.g. Pure.protectD)*)
fun fact_serials ctxt lookup =
  let
    val thy = Proof_Context.theory_of ctxt;
    (*unnamed nodes, without proofs of sort constraints*)
    fun own_nodes thm =
      (case try (Thm.thm_deps o Thm.transfer thy) thm of
        SOME thms =>
          thms |> filter (fn (i, node) =>
            is_none (lookup (Proofterm.thm_id (i, node))) andalso
            not (can Logic.dest_of_class (Proofterm.thm_node_prop node)))
      | NONE => []);
    fun add (thm_name, thm) =
      (case own_nodes thm of
        [(i, node)] =>
          let
            val baggage =
              map #1 (the_default [] (try (Thm.thm_deps o Thm.transfer thy) thm))
              |> remove (op =) i;
            (*the fact states the conclusion of the node, e.g. not a variant introduced by "note"*)
            val exact =
              Thm.prop_of thm aconv Logic.strip_imp_concl (Proofterm.thm_node_prop node);
            val entry = ((thm_name, baggage), exact);
            fun better (entry' as (_, exact')) =
              if exact <> exact' then if exact then entry else entry'
              else if prefer_single thm_name (#1 (#1 entry')) = thm_name then entry else entry';
          in Inttab.map_default (i, entry) better end
      | _ => I);
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

(*The oracle is declared for each run, in the private theory of the run, so that it also works
  for goals from theories that do not import this one. Theorems produced by an oracle are
  certified only by the identity of the oracle's theory, without its content, so they are
  transferred to the private theory explicitly.*)
fun add_oracle thy =
  let val ((_, oracle), thy') = Thm.add_oracle (\<^binding>\<open>apply_inspect\<close>, I) thy
  in (Thm.transfer thy' o oracle, thy') end;

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
            |> fold deps (Proofterm.thm_node_thms thm_node));
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
    val global_lookup = lookup_thm_id thy;
    val fact_serials = fact_serials ctxt global_lookup;
    fun lookup (i, thm_node) =
      (case Inttab.lookup fact_serials i of
        SOME (thm_name, _) => SOME (Fact thm_name)
      | NONE => Option.map Theorem (global_lookup (Proofterm.thm_id (i, thm_node))));

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
          (case try Thm.thm_deps st of
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
          (case (try Thm.thm_deps start, try Thm.thm_deps output) of
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
            (case try (Thm.thm_deps o Thm.transfer thy) rule of
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
    uses_of (Synchronized.value collector) @
      map (fn hyp => Assumption (name hyp, hyp)) (Termtab.keys (Synchronized.value hyps_collector))
  end;


(* instrumentation *)

val hook_name = "apply_inspect";

fun instrument_context fresh_state ({observe, step, ...}: events) ctxt =
  let
    fun wrapper _ tac i st =
      if is_closure_state st then tac i st
      else
        let
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

fun instrument_text fresh_state ({observe, step, ...}: events) =
  let
    fun wrap_method source (m: Method.method) : Method.method = fn facts => fn (ctxt, st) =>
      if is_closure_state st then m facts (ctxt, st)
      else
        let
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

fun run params text state =
  let
    val _ = Proof.assert_backward state;
    val ctxt = Proof.context_of state;
    val {context = goal_ctxt, facts = using, goal} = Proof.raw_goal state;

    val collector = Synchronized.var "apply_inspect" Inttab.empty;
    val hyps_collector = Synchronized.var "apply_inspect_hyps" Termtab.empty;
    val events = make_events ctxt collector hyps_collector params;

    (*the results of the run are discarded, so its contexts may live in a private theory*)
    val (fresh_state, thy') =
      Proof_Context.theory_of ctxt
      |> Raw_Simplifier.set_trace_ops (simp_trace_ops events)
      |> add_oracle;
    val instrument = Proof_Context.transfer thy' #> instrument_context fresh_state events;

    val result =
      Exn.result (fn () =>
        (instrument goal_ctxt, fresh_state (Thm.cprop_of goal))
        |> Method.evaluate (instrument_text fresh_state events text) (instrument ctxt) using
        |> Seq.filter_results
        |> Seq.pull
        |> is_some) ();
  in (result, collected_uses ctxt collector hyps_collector) end;

(*error: exception raised by the method or by the instrumentation, as opposed to plain failure*)
fun inspect params text state =
  let val (result, uses) = run params text state in
    (case result of
      Exn.Res b => {succeeded = b, error = NONE, uses = uses}
    | Exn.Exn exn => {succeeded = false, error = SOME (Runtime.exn_message exn), uses = uses})
  end;

fun pretty_uses ctxt uses =
  let
    val pretty = pretty_use ctxt;
    val items =
      uses
      |> map (fn u => let val prt = pretty u in (Pretty.unformatted_string_of prt, prt) end)
      |> sort_by #1
      |> map (fn (_, prt) => Pretty.item [prt]);
  in
    Pretty.big_list
      ("theorems used in failed method application: " ^ string_of_int (length items)) items
  end;


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

fun apply_inspect criteria (text, range as (pos, _)) state =
  let
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
  in
    (case run params text state of
      (Exn.Res true, _) => Proof.apply (text, range) state
    | (result, uses) =>
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
      (Method.report m; Toplevel.proofs (apply_inspect crit m))));

end;
