# padic-log-volume

Local-field analytic infrastructure: p-adic log/exp and normalized Haar log-volume.

## Goals

Build the local-field analytic stack that IUT4 §1 (Propositions 1.1–1.4) presupposes and that Mathlib does not yet provide.

As of Mathlib v4.32.0 there is no ready model of finite extensions of `ℚ_p` carrying:

* normalized valuation and ramification data;
* convergent `p`-adic `log`/`exp` with their image lattices;
* tensor normalization in total quotient rings;
* local different estimates;
* normalized additive Haar log-volume.

This repository develops that stack as standalone, Mathlib-style mathematics.

## Upstreaming

This material is generic local-field theory, not IUT-specific, and is **potentially upstreamable to Mathlib**. Keep the API and style aligned with Mathlib conventions so that upstreaming stays cheap.

## Related repositories

Consumed by `iut` (IUT4 §1, and the log-volume on the large volume container) and by `tate-curves-theta`.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
Library sources live under `PadicLogVolume/`, and every file must be imported from
the root module `PadicLogVolume.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib PadicLogVolume --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#4](https://taxis.lana.merten.dev/issues/4)
