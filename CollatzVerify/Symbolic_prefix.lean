import Mathlib

set_option linter.style.longLine false

set_option linter.style.whitespace false

open scoped BigOperators

-- The prefix-iteration state: (a, c) where a tracks the 2-power budget being
-- converted to 3-powers, c tracks the residue class. One "even-step" of the
-- 3x+1 prefix iteration acts on the state when a is still even.
-- We model the symbolic dynamics by the parity vector: a list of bits
-- b : Fin k → Bool, where b i = true means the i-th step was an odd-step (c odd).

-- a_final after the prefix iteration: starting 2-budget k, each step either
-- halves (even-step, c even) or multiplies a by 3 (odd-step, c odd).
-- After the budget of k even-applications is exhausted, a_final = 3^(#odd-steps).

-- Count of odd-steps in a parity vector of length k.
def oddSteps {k : ℕ} (b : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => b i = true)).card

-- a_final = 3 ^ (number of odd steps).
def aFinal {k : ℕ} (b : Fin k → Bool) : ℕ :=
  3 ^ (oddSteps b)

#check @oddSteps
#check @aFinal

-- Termination (upper half): the number of odd-steps is at most k,
-- so a_final = 3^(oddSteps) is a power of 3 bounded by 3^k.
theorem oddSteps_le {k : ℕ} (b : Fin k → Bool) : oddSteps b ≤ k := by
  unfold oddSteps
  calc (Finset.univ.filter (fun i => b i = true)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = k := by simp

-- a_final is a power of 3, bounded by 3^k.
theorem aFinal_le {k : ℕ} (b : Fin k → Bool) : aFinal b ≤ 3 ^ k := by
  unfold aFinal
  exact Nat.pow_le_pow_right (by norm_num) (oddSteps_le b)

-- a_final is exactly 3 raised to the odd-step count (definitional, but useful as a named fact).
theorem aFinal_eq_pow {k : ℕ} (b : Fin k → Bool) : aFinal b = 3 ^ (oddSteps b) := rfl

-- Lower bound: if the first prefix step is an odd-step (which holds because
-- a_0 = 2^k is even and c_0 = r is odd, forcing case (ii) first — Theorem 1),
-- then at least one odd-step is consumed, so j ≥ 1.
theorem oddSteps_pos {k : ℕ} (hk : 0 < k) (b : Fin k → Bool)
    (hfirst : b ⟨0, hk⟩ = true) : 1 ≤ oddSteps b := by
  unfold oddSteps
  apply Finset.card_pos.mpr
  exact ⟨⟨0, hk⟩, by simp [hfirst]⟩

-- THEOREM 1 (Termination), parity-vector form: given that the first prefix step
-- is an odd-step (forced by r odd, per the paper), the terminal value a_final
-- equals 3^j for some j with 1 ≤ j ≤ k.
theorem termination {k : ℕ} (hk : 0 < k) (b : Fin k → Bool)
    (hfirst : b ⟨0, hk⟩ = true) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ aFinal b = 3 ^ j := by
  refine ⟨oddSteps b, oddSteps_pos hk b hfirst, oddSteps_le b, ?_⟩
  rw [aFinal_eq_pow]

-- ===== LEMMA 1 (Prefix determinism) =====
-- The real symbolic state is (a, c); the Collatz value at this state is a*m + c.
-- While a is even, the parity of a*m + c equals c % 2 for EVERY m — this is the
-- m-independence that makes the whole prefix iteration a function of r alone.

-- The parity of the symbolic value a*m + c.
def stateParity (a c m : ℕ) : ℕ := (a * m + c) % 2

-- KEY FACT: while a is even, the parity of a*m + c is c % 2, independent of m.
theorem parity_m_independent (a c m : ℕ) (ha : a % 2 = 0) :
    stateParity a c m = c % 2 := by
  unfold stateParity
  have h : (a * m) % 2 = 0 := by
    rw [Nat.mul_mod, ha]; simp
  omega

-- One prefix step on the state (a, c), per the paper's transition rules.
-- (i) a even, c even → (a/2, c/2);  (ii) a even, c odd → (3a, 3c+1).
-- We only care about behavior while a is even (the prefix region).
def prefixStep (a c : ℕ) : ℕ × ℕ :=
  if c % 2 = 0 then (a / 2, c / 2) else (3 * a, 3 * c + 1)

-- LEMMA 1 (Prefix determinism), step form: while a is even, the transition taken
-- depends only on (a, c) — not on m. The Collatz action on a*m + c, for every m,
-- selects exactly the branch prefixStep selects from c % 2 alone.
theorem prefixStep_m_independent (a c m : ℕ) (ha : a % 2 = 0) :
    stateParity a c m = c % 2 ∧
    prefixStep a c = (if stateParity a c m = 0 then (a / 2, c / 2) else (3 * a, 3 * c + 1)) := by
  have hp : stateParity a c m = c % 2 := parity_m_independent a c m ha
  refine ⟨hp, ?_⟩
  unfold prefixStep
  rw [hp]

-- Iterate prefixStep n times from (a, c). This depends only on (a, c) — never m.
def prefixIter : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | n + 1, s => prefixIter n (prefixStep s.1 s.2)

-- FAITHFULNESS: while a is even, one real Collatz prefix step on the integer
-- N = a*m + c lands exactly on the predicted new symbolic state evaluated at m.
-- i.e. realStep(a*m+c) = (prefixStep a c).1 * m + (prefixStep a c).2, for every m.
theorem prefixStep_faithful (a c m : ℕ) (ha : a % 2 = 0) :
    (if (a * m + c) % 2 = 0 then (a * m + c) / 2 else 3 * (a * m + c) + 1)
      = (prefixStep a c).1 * m + (prefixStep a c).2 := by
  have hp : (a * m + c) % 2 = c % 2 := parity_m_independent a c m ha
  unfold prefixStep
  rw [hp]
  by_cases hc : c % 2 = 0
  · rw [if_pos hc, if_pos hc]
    simp only
    obtain ⟨a', rfl⟩ := Nat.dvd_of_mod_eq_zero ha
    obtain ⟨c', rfl⟩ := Nat.dvd_of_mod_eq_zero hc
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    ring_nf
    omega
  · rw [if_neg hc, if_neg hc]
    simp only
    ring
