# Changes

## Unreleased

- If the method fails, `apply_inspect` no longer fails like `apply`: it continues with the
  goal state that the method reached last before the failure (after its last method or
  classical step), as a skipped proof, with a warning; it still fails if the method got
  nowhere. `Apply_Inspect.inspect_limited` returns this state as `final`.

- The lists of theorems used show how often each theorem was used (by method and classical
  steps, and by successful rewrites), most frequent first; for a looping method, the rules
  of the loop come first. `Apply_Inspect.inspect_limited` returns the numbers as
  `use_counts`, also for each traced goal state; its `uses` are in the same order.

- `apply_inspect` no longer runs a successful method a second time without instrumentation:
  it continues with the goal state of the instrumented run, as a skipped proof (oracle
  `skip_proof`), since the command is not meant to stay in a finished proof.
  `Apply_Inspect.inspect_limited` returns this state as `final` (also the state at the time
  limit after a timeout; `NONE` if the method fails). Goal states that carry assumptions of
  the proof context (e.g. in a `context` with `assumes`) are no longer mistaken for goal
  states of other goals.

- `apply_inspect` no longer reports infrastructure: theorems of Pure, class axioms
  (definition, introduction rule and axioms of a class as recorded by `Axclass`, and
  theorems concluding a sort constraint, e.g. class relations and arities), locale axioms
  (introduction rules and axioms as recorded by `Locale`, and the definitions of locale
  predicates), and theorems declared with the new attribute `apply_inspect_hide`
  (`eq_reflection`, `TrueI`, `Eq_TrueI`, `Eq_FalseI` and `simp_thms` are declared so). The
  new option `apply_inspect_show_infrastructure` (default `false`) reports them again.
  `Apply_Inspect.infrastructure` offers the test in ML; the uses returned by the ML
  functions are not filtered.

  ```isabelle
  declare foo [apply_inspect_hide]       (* hide foo *)
  declare foo [apply_inspect_hide del]   (* show it again *)
  ```

- `apply_inspect` is always marked as `bad` (like `sorry` or `back`), as a diagnostic command
  that is not meant to stay in a proof.

- New option `apply_inspect_timeout` (int, milliseconds; default `0`, no limit). If the method
  of `apply_inspect` exceeds it, the method is frozen: the simplifier stops rewriting (so that
  it returns the term that it has reached) and no further method or classical step starts; a
  method that still does not finish (e.g. `blast`) is interrupted one second later. The
  command then shows the goal states that the method reached, as skipped proofs (oracle
  `skip_proof`): from `apply_inspect_trace_start` on (default `0`), every
  `apply_inspect_trace_interval` milliseconds (default `100`), up to the state at the time
  limit. The command shows the first of them and each `back` the next one, with the theorems
  used since the previous one. Each state is computed when it is shown, by replaying the
  method and freezing it after the number of steps and rewrites that it had reached, so the
  partial result of a looping simplifier shows within the goal state, also inside other
  methods such as `auto`. Subgoals that goal restriction hid (e.g. in `SELECT_GOAL`) are
  kept, possibly in a different order. `Apply_Inspect.inspect_limited` offers the same in ML.

  ```isabelle
  declare [[apply_inspect_timeout = 5000, apply_inspect_trace_start = 4000,
    apply_inspect_trace_interval = 200]]

  lemma ...
    apply_inspect auto  (* the goal state after 4000 ms *)
    back                (* after 4200 ms *)
  ```

- The instrumented run copies goal states with the oracle `skip_proof` instead of an
  oracle of its own.

- New option `apply_inspect_join_timeout` (int, milliseconds; default `100`, `0` for no
  limit). It bounds how long the inspection waits for proofs of other theorems,
  e.g. forked proofs in PIDE that are still running or never finish. A theorem
  whose proof has not finished within the limit contributes no dependencies, so
  uses that go through it are not reported.

  ```isabelle
  declare [[apply_inspect_join_timeout = 1000]]
  ```
