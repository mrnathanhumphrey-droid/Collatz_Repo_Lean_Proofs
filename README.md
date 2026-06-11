# Lean verification — Syracuse Plancherel mass S_k

Formal (Lean 4 + mathlib) verification accompanying the paper
"Closed-Form Plancherel Mass of the Syracuse Stationary Measure: The Constant 7/45."

Project: `collatz_verify`. Verified file: `CollatzVerify/Basic.lean`.
Lean toolchain + mathlib (see `lake-manifest.json` / `lean-toolchain` for versions).

## What is formally verified (compiles, "Goals accomplished!")

**Exact rational values of S_k, k = 1..5.**
- S_1 = 2/3 and S_2 = 10/21 are DERIVED in Lean from the stationary distributions
  pi_1 = (1/3, 2/3) and pi_2 = (8,16,11,4,2,22)/63 via X_k = 3^k * sum pi_k^2 and
  S_k = X_k - X_{k-1}. The stationary vectors are checked to sum to 1.
- For k = 3, 4, 5 the exact S_k values (from `s_infinity_exact.py`, reproduced in
  `experiments_output/s_infinity_exact_log.txt`) are entered as the rationals they are,
  and Lean verifies by exact arithmetic that S_k - 7/15 equals the exact deviation
  reported in Table 1 of the paper:
    S_1 - 7/15 = 1/5
    S_2 - 7/15 = 1/105
    S_3 - 7/15 = -5191/1019445
    S_4 - 7/15 = -11346676448406637/4627031617157687115
    S_5 - 7/15 = -92434923833741342979555966832824971889713393752300513614871
                  / 80256280802131672650443132418883371059408447291113411242243045

This is the machine-checked version of the paper's "certified (exact computation,
finite range)" claim (section 1.2), for k = 1..5.

## What is NOT (yet) in this file — honest scope

- **k = 6 is not yet included.** The paper certifies through k = 6; this file currently
  covers k = 1..5. Adding k = 6 requires the exact S_6 rational (run
  `push_to_k6_rate_analysis.py` and read its exact output) plus one more verified line.
- **Theorem 3 (the Plancherel decomposition itself) is NOT yet formalized here.** This
  file verifies the ARITHMETIC of the S_k values. It does not yet contain the proof that
  S_k = sum over {xi : 3 does not divide xi} of |mu-hat_k(xi)|^2. That proof rests on the
  level-nesting property (the repo's R66: the chain on (Z/3^k Z)* projects consistently
  across levels) plus Plancherel, and is the next build.
- **For k = 3, 4, 5 the chain is NOT rebuilt from scratch in Lean.** For k = 1, 2 the S_k
  are derived from the stationary vectors. For k >= 3 the exact S_k are entered as
  constants and their deviations from 7/15 are verified. So the k>=3 claim is
  "these exact rationals are self-consistent with Table 1," not "Lean re-solved the
  18/54/162-state chains."

## What is OPEN (not provable — by the paper's own statement)

- **S_infinity = 7/15 is NOT proven**, and is NOT claimed as a theorem anywhere in this
  project. The paper (section 1.2, section 7) and the repo's own notes
  (`s_infinity_derivation.md`) state the limit is certified by exact computation through
  finite k but the rigorous rate / unconditional limit proof remains open. Nothing here
  asserts otherwise.

## Honest one-line summary

Lean-verified that the paper's Table 1 values S_1..S_5 and their exact deviations from
7/15 are correct, with S_1, S_2 derived from the stationary distributions. Theorem 3
(the Plancherel decomposition proof) and k = 6 are the next steps; S_infinity = 7/15
remains open exactly as the paper states.
