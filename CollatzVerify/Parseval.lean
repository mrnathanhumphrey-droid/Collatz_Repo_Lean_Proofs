/-
Copyright (c) 2026 Nathan Humphrey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Humphrey
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Parseval / Plancherel identity for `ZMod.dft`

For any `N : ℕ` with `[NeZero N]` and any `Φ : ZMod N → ℂ`, the discrete Fourier
transform `ZMod.dft` preserves the sum of squared norms up to a factor of `N`:

  ∑ ξ, ‖dft Φ ξ‖² = N · ∑ r, ‖Φ r‖²

This is the Parseval (a.k.a. Plancherel) identity in the finite abelian setting.

## Main statements

* `ZMod.sum_norm_sq_dft_complex` — the identity stated in `ℂ` (proof-convenient).
* `ZMod.sum_norm_sq_dft` — the natural real-valued statement.
-/

open scoped BigOperators

namespace ZMod

/-- **Parseval / Plancherel identity for `ZMod.dft`** (complex form).

For any `N : ℕ` with `[NeZero N]` and any `Φ : ZMod N → ℂ`, the discrete Fourier
transform `ZMod.dft` satisfies
  ∑ ξ, ‖dft Φ ξ‖² = N · ∑ r, ‖Φ r‖²
as an equality in `ℂ`. -/
theorem sum_norm_sq_dft_complex (N : ℕ) [NeZero N] (Φ : ZMod N → ℂ) :
    (∑ ξ : ZMod N, (‖ZMod.dft Φ ξ‖ ^ 2 : ℂ))
      = (N : ℂ) * ∑ r : ZMod N, (‖Φ r‖ ^ 2 : ℂ) := by
  -- STEP 1: expand each ‖dft Φ ξ‖² into a double sum, fusing the two characters
  -- using `AddChar.map_add_eq_mul`.
  have expand : (∑ ξ : ZMod N, (‖ZMod.dft Φ ξ‖ ^ 2 : ℂ))
      = ∑ ξ : ZMod N, ∑ j : ZMod N, ∑ j' : ZMod N,
          ZMod.stdAddChar ((j' - j) * ξ) * (Φ j * (starRingEnd ℂ) (Φ j')) := by
    apply Finset.sum_congr rfl
    intro ξ _
    rw [show (‖ZMod.dft Φ ξ‖ ^ 2 : ℂ) = ZMod.dft Φ ξ * (starRingEnd ℂ) (ZMod.dft Φ ξ) by
          rw [Complex.mul_conj]; norm_cast; rw [Complex.normSq_eq_norm_sq]]
    rw [ZMod.dft_apply, map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro j' _
    rw [smul_eq_mul]
    rw [show (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ)) • Φ j')
          = (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ))) * (starRingEnd ℂ) (Φ j') by
        rw [smul_eq_mul, map_mul]]
    rw [show (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ)) : ℂ) = ZMod.stdAddChar (j' * ξ) by
          rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
              ← AddChar.map_neg_eq_inv, neg_neg, ← ZMod.stdAddChar_apply]]
    rw [show ZMod.stdAddChar (-(j * ξ)) * Φ j *
              (ZMod.stdAddChar (j' * ξ) * (starRingEnd ℂ) (Φ j'))
            = (ZMod.stdAddChar (-(j * ξ)) * ZMod.stdAddChar (j' * ξ)) *
              (Φ j * (starRingEnd ℂ) (Φ j')) from by ring]
    rw [← AddChar.map_add_eq_mul,
        show -(j * ξ) + j' * ξ = (j' - j) * ξ from by ring]
  rw [expand]
  -- STEP 2: swap the sums so `ξ` is innermost: `(ξ, j, j') → (j, j', ξ)`.
  rw [Finset.sum_comm]
  rw [show (∑ j : ZMod N, ∑ ξ : ZMod N, ∑ j' : ZMod N,
              ZMod.stdAddChar ((j' - j) * ξ) * (Φ j * (starRingEnd ℂ) (Φ j')))
          = (∑ j : ZMod N, ∑ j' : ZMod N, ∑ ξ : ZMod N,
              ZMod.stdAddChar ((j' - j) * ξ) * (Φ j * (starRingEnd ℂ) (Φ j'))) from by
        apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]]
  -- STEP 3: pull `Φ j * conj(Φ j')` outside the ξ-sum (it doesn't depend on `ξ`).
  rw [show (∑ j : ZMod N, ∑ j' : ZMod N, ∑ ξ : ZMod N,
              ZMod.stdAddChar ((j' - j) * ξ) * (Φ j * (starRingEnd ℂ) (Φ j')))
          = (∑ j : ZMod N, ∑ j' : ZMod N,
              (∑ ξ : ZMod N, ZMod.stdAddChar ((j' - j) * ξ))
                * (Φ j * (starRingEnd ℂ) (Φ j'))) from by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro j' _
        rw [← Finset.sum_mul]]
  -- STEP 4: collapse the ξ-sum via standard-character orthogonality:
  -- `∑_ξ χ(c · ξ) = N` if `c = 0`, else `0`.
  have h_orth : ∀ (c : ZMod N),
      (∑ ξ : ZMod N, ZMod.stdAddChar (c * ξ))
        = if c = 0 then (N : ℂ) else 0 := by
    intro c
    have hcomm : ∀ ξ : ZMod N, ZMod.stdAddChar (c * ξ) = ZMod.stdAddChar (ξ * c) := by
      intro ξ; rw [mul_comm]
    simp_rw [hcomm]
    rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar N)]
    rw [ZMod.card]
    push_cast
    rfl
  simp_rw [h_orth]
  -- STEP 5: collapse the double sum to its diagonal (only `j' = j` contributes).
  rw [show (∑ j : ZMod N, ∑ j' : ZMod N,
              (if (j' - j : ZMod N) = 0 then (N : ℂ) else 0)
                * (Φ j * (starRingEnd ℂ) (Φ j')))
          = (∑ j : ZMod N,
              (N : ℂ) * (Φ j * (starRingEnd ℂ) (Φ j))) from by
        apply Finset.sum_congr rfl; intro j _
        rw [show (∑ j' : ZMod N,
                  (if (j' - j : ZMod N) = 0 then (N : ℂ) else 0)
                    * (Φ j * (starRingEnd ℂ) (Φ j')))
                = (∑ j' : ZMod N,
                    (if j' = j then (N : ℂ) * (Φ j * (starRingEnd ℂ) (Φ j')) else 0)) from by
              apply Finset.sum_congr rfl; intro j' _
              by_cases hjj : j' = j
              · simp [hjj]
              · simp [hjj, sub_eq_zero]]
        rw [Finset.sum_ite_eq' Finset.univ j
              (fun j' => (N : ℂ) * (Φ j * (starRingEnd ℂ) (Φ j')))]
        simp]
  -- Final: pull `N` out of the j-sum and identify `‖Φ r‖² = Φ r * conj(Φ r)`.
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

/-- **Parseval / Plancherel identity for `ZMod.dft`** (real form).

The natural real-valued statement: `∑‖dft Φ ξ‖² = N · ∑‖Φ r‖²`. -/
theorem sum_norm_sq_dft (N : ℕ) [NeZero N] (Φ : ZMod N → ℂ) :
    (∑ ξ : ZMod N, ‖ZMod.dft Φ ξ‖ ^ 2)
      = (N : ℝ) * ∑ r : ZMod N, ‖Φ r‖ ^ 2 := by
  have h := sum_norm_sq_dft_complex N Φ
  exact_mod_cast h

end ZMod
