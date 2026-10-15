# Changes

## Unreleased

- `apply_inspect` is always marked as `bad` (like `sorry` or `back`), as a diagnostic command
  that is not meant to stay in a proof.

- New option `apply_inspect_timeout` (int, milliseconds; default `0`, no limit). If the method
  of `apply_inspect` exceeds it, the theorems used so far are reported, the method is paused,
  and the command continues with the goal state that it has reached (after its last method
  or classical step), as a skipped proof (oracle `skip_proof`). Each `back` continues the
  method for `apply_inspect_step_time` milliseconds (default `100`), reports the theorems used
  in that step, and yields the goal state reached then, so that `back` steps through the run
  of the method, without a limit on the total time; if the method finishes, its result is the
  last goal state. The method pauses only where the instrumentation is called (method and
  classical steps, rewrites, simprocs), so a looping simplifier shows the goal state before
  it was called. Subgoals that goal restriction hid (e.g. in `SELECT_GOAL`) are kept,
  possibly in a different order. A paused method is stopped once its goal states are no
  longer referenced, e.g. after the command has been removed. `Apply_Inspect.inspect_limited`
  offers the same in ML.

  ```isabelle
  declare [[apply_inspect_timeout = 5000, apply_inspect_step_time = 200]]

  lemma ...
    apply_inspect auto
    back  (* continue for another 200 ms *)
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
