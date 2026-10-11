# padic-log-volume

Local-field analytic infrastructure: p-adic log/exp and normalized Haar log-volume.

## Status

Started 2026-10. The library `PadicLogVolume` contains, with no `sorry`, `axiom` or `admit`:

* `PadicLogVolume/PadicLog.lean` — the `p`-adic logarithm `padicLog` of a complete
  discretely valued field of characteristic `0` (summability, the homomorphism property on the
  principal units, surjectivity of `a ↦ log (1 + a)` onto a ball by a contraction argument) and
  the log-shell `logShell k p = (2p)⁻¹·log(1 + 𝔪)` (bounded, containing the ring of integers,
  equal to it for odd unramified `p`);
* `PadicLogVolume/LogLattice.lean` — the image lattices of the logarithm with Mochizuki's
  exponents (IUT IV, Proposition 1.2(i)): `(2p)⁻¹·p^a·𝒪 ⊆ 𝓘 ⊆ (2p)⁻¹·p^{-b}·𝒪` with
  `a = logLatticeA p e`, `b = logLatticeB p e`, and `(a + b)·log p ≤ 3 + log e`
  (`= 0` when `p` is odd and `e ≤ p − 2`);
* `PadicLogVolume/TraceDuality.lean` — traces, integral lattices and trace-dual bases in finite
  `ℚ_p`-algebras and their tensor products, the ingredients of the different estimate for tensor
  products of local fields (IUT IV, Proposition 1.1).

These were developed in `lana-agents/iut` (`Iut/Concrete/LocalConstruct/`) and moved here;
`iut` requires this repository.

## Goals

Build, as a general library, the local-field analytic stack that IUT4 §1 (Propositions 1.1–1.4) presupposes and that Mathlib does not yet provide.

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

Planned as the local-field input to `iut` and `tate-curves-theta`. Neither uses it:
`tate-curves-theta` lists it only as a future dependency, and `iut` now constructs what it
needs itself (see *Status*).

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`
(commit `81a5d25`), its only direct dependency.
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

License: Apache 2.0 (see LICENSE).
