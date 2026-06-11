import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false

open scoped BigOperators

-- We work at a fixed level k, on the group ZMod (3^k).
-- π : the stationary distribution (as a complex-valued function for Fourier purposes)
-- μ̂ : its discrete Fourier transform (we'll connect to ZMod.dft later)

-- Step 1: just state the high-frequency mass S_k as a sum, and check it typechecks.
-- N = 3^k. "3 ∤ ξ" means ξ is not in the image of multiplication by 3.

noncomputable def highFreqMass (k : ℕ) (muhat : ZMod (3 ^ k) → ℂ) : ℝ :=
  ∑ ξ : ZMod (3 ^ k), if (3 : ZMod (3 ^k)) ∣ ξ then 0 else ‖muhat ξ‖^2

#check @highFreqMass

-- Total mass: sum of |μ̂(ξ)|² over ALL ξ (this is X_k by Plancherel)
noncomputable def totalMass (k : ℕ) (muhat : ZMod (3 ^ k) → ℂ) : ℝ :=
  ∑ ξ : ZMod (3 ^ k), ‖muhat ξ‖ ^ 2

-- Low-frequency mass: sum over ξ WITH 3 ∣ ξ
noncomputable def lowFreqMass (k : ℕ) (muhat : ZMod (3 ^ k) → ℂ) : ℝ :=
  ∑ ξ : ZMod (3 ^ k), if (3 : ZMod (3 ^ k)) ∣ ξ then ‖muhat ξ‖ ^ 2 else 0

  theorem mass_split (k : ℕ) (muhat : ZMod (3 ^ k) → ℂ) :
    totalMass k muhat = lowFreqMass k muhat + highFreqMass k muhat := by
  unfold totalMass lowFreqMass highFreqMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases h : (3 : ZMod (3 ^ k)) ∣ ξ
  · simp [h]
  · simp [h]

    -- S_k is DEFINED as total mass at level k minus total mass at level (k-1).
-- (This matches X_k - X_{k-1} from the paper; Xprev stands for X_{k-1}.)

-- The nesting hypothesis (R66 / Terras, cited — not re-derived here):
-- the low-frequency mass at level k equals the total mass at level k-1.
-- We carry it as a hypothesis `nesting`.

theorem theorem3_core
    (k : ℕ) (muhat : ZMod (3 ^ k) → ℂ) (Xprev : ℝ)
    (nesting : lowFreqMass k muhat = Xprev) :
    totalMass k muhat - Xprev = highFreqMass k muhat := by
  rw [← nesting]
  rw [mass_split k muhat]
  ring

-- Full Theorem 3, assembled: given Plancherel (totalMass = X_k) and nesting
-- (lowFreqMass = X_{k-1}), the high-frequency mass equals S_k = X_k - X_{k-1}.
--
-- Xk, Xprev are the scaled L² masses from the paper (X_k, X_{k-1}).
-- `plancherel` : the level-k total mass IS X_k  (Parseval — Step 5 will derive this)
-- `nesting`    : the low-frequency mass IS X_{k-1}  (R66 / Terras — cited)

theorem theorem3
    (k : ℕ) (muhat : ZMod (3 ^ k) → ℂ) (Xk Xprev : ℝ)
    (plancherel : totalMass k muhat = Xk)
    (nesting : lowFreqMass k muhat = Xprev) :
    highFreqMass k muhat = Xk - Xprev := by
  have h := mass_split k muhat
  rw [plancherel, nesting] at h
  linarith

open scoped BigOperators

-- Connect to mathlib's discrete Fourier transform on ZMod N.
-- π : the stationary distribution as a complex function on ZMod (3^k).
-- mathlib's ZMod.dft (notation 𝓕) is the transform; we define μ̂ := 𝓕 π.

noncomputable def muHatOf (k : ℕ) (π : ZMod (3 ^ k) → ℂ) : ZMod (3 ^ k) → ℂ :=
  ZMod.dft π

-- Parseval for ZMod.dft: ∑‖𝓕 π ξ‖² = N · ∑‖π r‖²
-- Built from dft_dft (inversion) + the orthogonality already inside auxDFT_auxDFT.

example (k : ℕ) (f : ZMod (3 ^ k) → ℂ) :
    ∑ ξ : ZMod (3 ^ k), ‖f ξ‖ ^ 2 = ∑ ξ : ZMod (3 ^ k), Complex.normSq (f ξ) := by
  simp only [Complex.normSq_eq_norm_sq]

example (k : ℕ) (π : ZMod (3 ^ k) → ℂ) (ξ : ZMod (3 ^ k)) :
    ZMod.dft π ξ = ∑ j : ZMod (3 ^ k), ZMod.stdAddChar (-(j * ξ)) • π j := by
  rw [ZMod.dft_apply]

example (z : ℂ) : (Complex.normSq z : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj]

example (k : ℕ) (π : ZMod (3 ^ k) → ℂ) (ξ : ZMod (3 ^ k)) :
    (‖ZMod.dft π ξ‖ ^ 2 : ℂ) = ZMod.dft π ξ * (starRingEnd ℂ) (ZMod.dft π ξ) := by
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

example (k : ℕ) (π : ZMod (3 ^ k) → ℂ) (ξ : ZMod (3 ^ k)) :
    (starRingEnd ℂ) (ZMod.dft π ξ)
      = ∑ j : ZMod (3 ^ k), (starRingEnd ℂ) (ZMod.stdAddChar (-(j * ξ)) • π j) := by
  rw [ZMod.dft_apply, map_sum]

example (k : ℕ) (π : ZMod (3 ^ k) → ℂ) (ξ : ZMod (3 ^ k)) :
    (‖ZMod.dft π ξ‖ ^ 2 : ℂ)
      = ∑ j : ZMod (3 ^ k), ∑ j' : ZMod (3 ^ k),
          (ZMod.stdAddChar (-(j * ξ)) • π j) * (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ)) • π j') := by
  rw [show (‖ZMod.dft π ξ‖ ^ 2 : ℂ) = ZMod.dft π ξ * (starRingEnd ℂ) (ZMod.dft π ξ) by
        rw [Complex.mul_conj]; norm_cast; rw [Complex.normSq_eq_norm_sq]]
  rw [ZMod.dft_apply, map_sum]
  rw [Finset.sum_mul_sum]

example (k : ℕ) (x : ZMod (3 ^ k)) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply]
  rw [← Circle.coe_inv_eq_conj]
  rw [← AddChar.map_neg_eq_inv]

example (k : ℕ) (j j' ξ : ZMod (3 ^ k)) :
    ZMod.stdAddChar (-(j * ξ)) * (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ)))
      = ZMod.stdAddChar ((j' - j) * ξ) := by
  rw [show (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ))) = ZMod.stdAddChar (j' * ξ) by
        rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
            ← AddChar.map_neg_eq_inv, neg_neg]]
  rw [← AddChar.map_add_eq_mul]
  ring_nf

example (k : ℕ) (c : ZMod (3 ^ k)) :
    ∑ ξ : ZMod (3 ^ k), ZMod.stdAddChar (ξ * c) = if c = 0 then (3 ^ k : ℂ) else 0 := by
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar (3 ^ k))]
  rw [ZMod.card]
  push_cast
  rfl

theorem parseval (k : ℕ) (π : ZMod (3 ^ k) → ℂ) :
    (∑ ξ : ZMod (3 ^ k), (‖ZMod.dft π ξ‖ ^ 2 : ℂ))
      = (3 ^ k : ℂ) * ∑ r : ZMod (3 ^ k), (‖π r‖ ^ 2 : ℂ) := by
  -- STEP 1: expand each ‖dft π ξ‖² into a double sum, fusing the two characters
  -- using AddChar.map_add_eq_mul.
  have expand : (∑ ξ : ZMod (3 ^ k), (‖ZMod.dft π ξ‖ ^ 2 : ℂ))
      = ∑ ξ : ZMod (3 ^ k), ∑ j : ZMod (3 ^ k), ∑ j' : ZMod (3 ^ k),
          ZMod.stdAddChar ((j' - j) * ξ) * (π j * (starRingEnd ℂ) (π j')) := by
    apply Finset.sum_congr rfl
    intro ξ _
    -- |z|² = z * conj z
    rw [show (‖ZMod.dft π ξ‖ ^ 2 : ℂ) = ZMod.dft π ξ * (starRingEnd ℂ) (ZMod.dft π ξ) by
          rw [Complex.mul_conj]; norm_cast; rw [Complex.normSq_eq_norm_sq]]
    -- Expand both copies of dft (the single `rw` unfolds all occurrences)
    -- and distribute conj over the second sum
    rw [ZMod.dft_apply, map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro j' _
    -- Inner term: (χ(-(j·ξ)) • π j) * conj(χ(-(j'·ξ)) • π j')
    -- Rewrite both smuls as muls (the target type is ℂ).
    rw [smul_eq_mul]
    -- conj of (χ(-(j'·ξ)) • π j') = conj(χ(-(j'·ξ))) * conj(π j')
    rw [show (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ)) • π j')
          = (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ))) * (starRingEnd ℂ) (π j') by
        rw [smul_eq_mul, map_mul]]
    -- conj(χ(-(j'·ξ))) = χ(j'·ξ): characters on a finite group have unit-modulus values,
    -- so conjugation equals inversion equals negation-of-argument.
    rw [show (starRingEnd ℂ) (ZMod.stdAddChar (-(j' * ξ)) : ℂ) = ZMod.stdAddChar (j' * ξ) by
          rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
              ← AddChar.map_neg_eq_inv, neg_neg, ← ZMod.stdAddChar_apply]]
    -- Regroup so the two characters are adjacent.
    rw [show ZMod.stdAddChar (-(j * ξ)) * π j *
              (ZMod.stdAddChar (j' * ξ) * (starRingEnd ℂ) (π j'))
            = (ZMod.stdAddChar (-(j * ξ)) * ZMod.stdAddChar (j' * ξ)) *
              (π j * (starRingEnd ℂ) (π j')) from by ring]
    -- Fuse them via the AddChar additivity.
    rw [← AddChar.map_add_eq_mul,
        show -(j * ξ) + j' * ξ = (j' - j) * ξ from by ring]
  rw [expand]
  -- STEP 2: swap (ξ, j, j') → (j, j', ξ).
  -- First swap outer two: (ξ, j, j') → (j, ξ, j').
  rw [Finset.sum_comm]
  -- Then swap inner two under the j binder: (j, ξ, j') → (j, j', ξ).
  rw [show (∑ j : ZMod (3 ^ k), ∑ ξ : ZMod (3 ^ k), ∑ j' : ZMod (3 ^ k),
              ZMod.stdAddChar ((j' - j) * ξ) * (π j * (starRingEnd ℂ) (π j')))
          = (∑ j : ZMod (3 ^ k), ∑ j' : ZMod (3 ^ k), ∑ ξ : ZMod (3 ^ k),
              ZMod.stdAddChar ((j' - j) * ξ) * (π j * (starRingEnd ℂ) (π j'))) from by
        apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]]
  -- STEP 3: pull (π j * conj(π j')) out of the ξ-sum (it doesn't depend on ξ).
  rw [show (∑ j : ZMod (3 ^ k), ∑ j' : ZMod (3 ^ k), ∑ ξ : ZMod (3 ^ k),
              ZMod.stdAddChar ((j' - j) * ξ) * (π j * (starRingEnd ℂ) (π j')))
          = (∑ j : ZMod (3 ^ k), ∑ j' : ZMod (3 ^ k),
              (∑ ξ : ZMod (3 ^ k), ZMod.stdAddChar ((j' - j) * ξ))
                * (π j * (starRingEnd ℂ) (π j'))) from by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro j' _
        rw [← Finset.sum_mul]]
  -- STEP 4: collapse the ξ-sum via standard-character orthogonality.
  have h_orth : ∀ (c : ZMod (3 ^ k)),
      (∑ ξ : ZMod (3 ^ k), ZMod.stdAddChar (c * ξ))
        = if c = 0 then (3 ^ k : ℂ) else 0 := by
    intro c
    have hcomm : ∀ ξ : ZMod (3 ^ k), ZMod.stdAddChar (c * ξ) = ZMod.stdAddChar (ξ * c) := by
      intro ξ; rw [mul_comm]
    simp_rw [hcomm]
    rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar (3 ^ k))]
    rw [ZMod.card]
    push_cast
    rfl
  simp_rw [h_orth]
  -- STEP 5: collapse to the diagonal.
  -- For each j: ∑_j' (if j' - j = 0 then 3^k else 0) * (π j * conj(π j'))
  --   = (3^k) * (π j * conj(π j))
  rw [show (∑ j : ZMod (3 ^ k), ∑ j' : ZMod (3 ^ k),
              (if (j' - j : ZMod (3 ^ k)) = 0 then (3 ^ k : ℂ) else 0)
                * (π j * (starRingEnd ℂ) (π j')))
          = (∑ j : ZMod (3 ^ k),
              (3 ^ k : ℂ) * (π j * (starRingEnd ℂ) (π j))) from by
        apply Finset.sum_congr rfl; intro j _
        rw [show (∑ j' : ZMod (3 ^ k),
                  (if (j' - j : ZMod (3 ^ k)) = 0 then (3 ^ k : ℂ) else 0)
                    * (π j * (starRingEnd ℂ) (π j')))
                = (∑ j' : ZMod (3 ^ k),
                    (if j' = j then (3 ^ k : ℂ) * (π j * (starRingEnd ℂ) (π j')) else 0)) from by
              apply Finset.sum_congr rfl; intro j' _
              by_cases hjj : j' = j
              · simp [hjj]
              · simp [hjj, sub_eq_zero]]
        rw [Finset.sum_ite_eq' Finset.univ j
              (fun j' => (3 ^ k : ℂ) * (π j * (starRingEnd ℂ) (π j')))]
        simp]
  -- Final: pull 3^k out and identify ‖π r‖² = π r * conj(π r).
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

-- BRIDGE: totalMass of the Fourier transform = 3^k · ∑‖π r‖² (real-valued Parseval).
-- This is what discharges the `plancherel` hypothesis in theorem3.
theorem totalMass_dft (k : ℕ) (π : ZMod (3 ^ k) → ℂ) :
    totalMass k (muHatOf k π) = (3 ^ k : ℝ) * ∑ r : ZMod (3 ^ k), ‖π r‖ ^ 2 := by
  unfold totalMass muHatOf
  have h := parseval k π
  exact_mod_cast h

-- CAPSTONE — Theorem 3 (paper form): given only the nesting hypothesis (R66, cited
-- to Tao 2022 Lemma 1.12), the high-frequency mass equals 3^k·∑‖π r‖² − X_{k−1}.
-- Plancherel is no longer a hypothesis here — it is discharged by totalMass_dft.
theorem theorem3_final (k : ℕ) (π : ZMod (3 ^ k) → ℂ) (Xprev : ℝ)
    (nesting : lowFreqMass k (muHatOf k π) = Xprev) :
    highFreqMass k (muHatOf k π) = (3 ^ k : ℝ) * (∑ r : ZMod (3 ^ k), ‖π r‖ ^ 2) - Xprev := by
  exact theorem3 k (muHatOf k π) ((3 ^ k : ℝ) * ∑ r : ZMod (3 ^ k), ‖π r‖ ^ 2) Xprev
    (totalMass_dft k π) nesting
