# Changes

## Unreleased

- New option `apply_inspect_join_timeout` (real, seconds; default `0.1`, `0` for no
  limit). It bounds how long the inspection waits for proofs of other theorems,
  e.g. forked proofs in PIDE that are still running or never finish. A theorem
  whose proof has not finished within the limit contributes no dependencies, so
  uses that go through it are not reported.

  ```isabelle
  declare [[apply_inspect_join_timeout = 1.0]]
  ```
