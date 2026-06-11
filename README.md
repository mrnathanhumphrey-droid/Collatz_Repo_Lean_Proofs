# Lean verification — Syracuse Plancherel mass S_k and the c = 7/45 constant

Formal (Lean 4 + Mathlib) verification accompanying the paper
*"A Closed-Form Leading Constant for the High-Frequency Plancherel Mass of Tao's
Syracuse Stationary Measure: The Constant c = 7/45."*

- **Lean toolchain:** `leanprover/lean4:v4.30.0` (see `lean-toolchain`)
- **Mathlib:** `v4.30.0` (see `lake-manifest.json`)
- **Top-level module:** `CollatzVerify.lean` — imports every file below so
  `lake build` exercises the entire formalization.

## Build

```
lake exe cache get   # downloads precompiled Mathlib
lake build           # builds the whole project
```

The first `cache get` is several GB and takes a few minutes; subsequent builds
are fast.

## File-by-file outline

### `CollatzVerify/Basic.lean` — exact S_k values, k = 1..6

Machine-checked rational arithmetic backing **Table 1** of the paper.

- `pi1`, `pi2` — the exact stationary distributions of the Syracuse Markov chain
  on `(ℤ/3ℤ)ˣ` and `(ℤ/9ℤ)ˣ` (as `Fin n → ℚ`).
- `X1, X2 : ℚ` — the scaled L² masses, derived in Lean from `pi1`, `pi2`.
- `S1 : ℚ = 2/3`, `S2 : ℚ = 10/21` — proved equal to the closed forms by
  `norm_num`.
- `S3, S4, S5, S6 : ℚ` — entered as the exact rationals output by
  `s_infinity_exact.py` (the chains at k = 3..6 are 18, 54, 162, 486 states; the
  Q-arithmetic stationary solve is in the companion Python, the result is the
  rational here).
- `example` lemmas: `S_k - 7/15` evaluates to the exact deviation in the paper's
  Table 1, for k = 1..6.

What this file **does not** do: re-solve the k ≥ 3 Markov chains inside Lean.
It checks that the rationals reported in Table 1 are self-consistent. The
chain-solving step is external (Python, rational arithmetic).

### `CollatzVerify/Symbolic_prefix.lean` — termination + Lemma 1

Symbolic dynamics of the 3x+1 prefix iteration on the state `(a, c)` where `a`
is the 2-power budget and `c` is the residue class.

- `oddSteps : (Fin k → Bool) → ℕ` — number of odd-steps in a parity vector.
- `aFinal : (Fin k → Bool) → ℕ` — terminal value of `a`, equal to `3 ^ oddSteps`.
- `oddSteps_le`, `aFinal_le`, `aFinal_eq_pow` — basic bounds and structural identity.
- `oddSteps_pos` — **Lemma 1 of the paper**: strict positivity of the odd-step
  count under the trigger hypothesis.
- `termination` — the prefix iteration terminates after at most k steps.
- `stateParity`, `prefixStep`, `prefixIter` — the explicit dynamics.
- `parity_m_independent`, `prefixStep_m_independent`, `prefixStep_faithful` —
  the m-independence properties (the prefix step on `(a, c)` doesn't see `m`
  when `a` is even, so the symbolic dynamics is faithful).

### `CollatzVerify/Parseval.lean` — Parseval / Plancherel for `ZMod.dft`

Mathlib-shaped general statement, generalizing from the paper's `3^k` to
arbitrary `N : ℕ` with `[NeZero N]`. Both theorems take `Φ : ZMod N → ℂ`.

- `ZMod.sum_norm_sq_dft_complex` — the identity in `ℂ`:
  `∑ ξ, ‖dft Φ ξ‖² = N · ∑ r, ‖Φ r‖²`. The proof-convenient form (uses
  `Complex.mul_conj` directly).
- `ZMod.sum_norm_sq_dft` — the natural real-valued companion (derived by
  `exact_mod_cast` from the complex version).

This identity does not currently exist in Mathlib (verified against
`Mathlib/Analysis/Fourier/ZMod.lean`, which has `dft_apply`, `dft_dft`
inversion, `invDFT_*`, but no Parseval / norm-squared identity). Candidate
for upstream PR.

### `CollatzVerify/Theorem3.lean` — Plancherel decomposition + Theorem 3 capstone

Specialized to `ZMod (3 ^ k)`, this is the formalization of the paper's
Theorem 3 (Plancherel decomposition into high-frequency + low-frequency mass)
and its capstone.

- `highFreqMass`, `totalMass`, `lowFreqMass` — the three mass quantities.
- `mass_split` — `totalMass = lowFreqMass + highFreqMass` (partitions the
  ξ-sum by `3 ∣ ξ`).
- `theorem3_core` — given the nesting hypothesis (low-frequency mass at level
  k equals total mass at level k-1, i.e. R66), the high-frequency mass equals
  `X_k - X_{k-1} = S_k`.
- `theorem3` — assembled with both Parseval (`totalMass = X_k`) and nesting
  hypotheses.
- `parseval` — specialized `3 ^ k` version of the Parseval identity (the
  general form is in `Parseval.lean`). Provided here as the version the rest
  of this file consumes directly.
- `totalMass_dft` — connects `totalMass k (ZMod.dft π) = (3 ^ k) · ∑ ‖π r‖²`.
- `theorem3_final` — Theorem 3 assembled end-to-end, taking only the nesting
  hypothesis (R66, cited not re-derived) and concluding the Plancherel
  decomposition.

### `CollatzVerify/Test.lean` — standalone k=6 deviation check

A minimal independent file containing only the `S_6` rational and the
deviation `S_6 - 7/15 = ...` lemma. Uses only `Mathlib.Tactic.NormNum` and
`Mathlib.Data.Rat.Defs` (no full Mathlib import), so it builds quickly and
demonstrates the k=6 check in isolation.

## Honest scope

**Verified** (compiles, "Goals accomplished!"):
- Exact rational `S_k` values for k = 1..6, with k = 1, 2 *derived* from the
  stationary distributions inside Lean.
- All deviations `S_k - 7/15` for k = 1..6 match the paper's Table 1 exactly.
- The Plancherel identity for `ZMod.dft` (`Parseval.lean`) — fully proved.
- The Plancherel decomposition `totalMass = lowFreqMass + highFreqMass`.
- Theorem 3, conditional on the nesting hypothesis (R66).
- Termination of the symbolic prefix iteration and Lemma 1.

**Conditional / not internally re-derived:**
- For k = 3..6 the exact `S_k` are entered as constants (the chains are solved
  by `s_infinity_exact.py` in the companion repo; this file verifies the
  arithmetic).
- Theorem 3's `nesting` hypothesis (R66) is taken as a parameter, not proved
  here. The rigorous derivation of nesting is the next formalization step.

**Open** (by the paper's own statement):
- `S_∞ = 7/15` and the rate of convergence remain open in the paper (Section
  5). Nothing in this Lean repo asserts a closed-form `S_∞ = 7/15` as a theorem.

## Companion repository

The full research repository (Python computations, structural identities,
numerical experiments) is at
https://github.com/mrnathanhumphrey-droid/Collatz.
This repo contains only the Lean formalization, intended for archival via
Zenodo.
