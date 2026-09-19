/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import Lean4LPD.Constants.C0

/-!
# Non-vacuity checks for the bounds on `c₀`

Standalone: `lake env lean tests/C0LayerCount.lean`.

The module `Lean4LPD.Constants.C0` proves `c₀ ≤ 2` under several alternative sufficient conditions
(a cap `Γ ≤ 6` or `Γ ≤ 7` on the effective layer count, or `m* ≥ 3`), weaker constants under
weaker hypotheses (`10/3`, `4e^{9/32}`), and witnesses with `c₀ > 2` showing which hypotheses are
needed. This file instantiates each of those theorems at an explicit parameter point that matters
— an extremal point of its hypothesis set, or a point where the neighbouring theorems do not
apply — because a sufficient condition with an empty or degenerate set of instances proves
nothing. Every `Admissible` hypothesis below is discharged by `norm_num`.
-/

open Lean4LPD

/-- The general `m* = 0` theorem reproduces the numeric witness `two_lt_cZero_of_m_zero` at
`(r, m*, Γ, B) = (5, 0, 2, 1)`, so the two statements agree where both apply. -/
example : 2 < cZero 5 0 2 1 :=
  two_lt_cZero_of_m_zero_general (by norm_num) (by norm_num) (by norm_num)

/-- …and it fires at `Γ = 512` and, in the next example, at `Γ = 1/1000`: no bound on `Γ` can
take the place of `m* ≥ 1`, since the obstruction survives arbitrarily large *and* arbitrarily
small layer counts. -/
example : 2 < cZero 1 0 512 1 :=
  two_lt_cZero_of_m_zero_general (by norm_num) (by norm_num) (by norm_num)

example : 2 < cZero 1000 0 (1/1000) 1 :=
  two_lt_cZero_of_m_zero_general (by norm_num) (by norm_num) (by norm_num)

/-- `(32/7, 1, 7)` is admissible — the **extremal** point of the `Γ ≤ 7` region, where
`8(m*+1)² ≤ rΓ` holds with equality and `c₀ = 1.9838`. A cap theorem that did not reach its own
extremal point would be untested exactly where it is tight. -/
example : Admissible (32/7) 1 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

example : cZero (32/7) 1 7 1 ≤ 2 :=
  cZero_le_two_of_gamma_le_seven ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The `Γ ≤ 6` route fires at `Γ_eff = 6`, which is the second-order formula on a 1D
nearest-neighbour chain (bare `Γ = 3`, `Υ = 2`) — the physically motivated case. -/
example : cZero 6 1 6 1 ≤ 2 :=
  cZero_le_two_of_gamma_le_six ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `le_r_of_gamma_le_six` *derives* `r ≥ 5` rather than assuming it — that is the whole reason
`Γ ≤ 6` costs no new estimate. -/
example : (5 : ℝ) ≤ 6 :=
  le_r_of_gamma_le_six (r := 6) (m := 1) (G := 6)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ (by norm_num) (by norm_num)

/-- **`cZero_le_two_of_three_le_m` fires exactly where the other two sufficient conditions do not
apply**, which is what makes the three genuinely incomparable rather than nested. At
`(r, m*, Γ) = (3, 3, 128)`:
`r = 3 < 5` so `cZero_le_two` does not apply, and `Γ = 128 > 7` so
`cZero_le_two_of_gamma_le_seven` does not either. -/
example : Admissible 3 3 128 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

example : cZero 3 3 128 1 ≤ 2 :=
  cZero_le_two_of_three_le_m ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num)

/-- And `m* = 2` is genuinely not enough — at its own argmax `Γ* = 8(m*+1)²/2 = 36`. -/
example : 2 < cZero 2 2 36 1 := two_lt_cZero_of_m_two.2

/-! ### The constant ladder: each weaker constant buys real coverage -/

/-- **The point that makes `c₀ ≤ 10/3` worth stating.** At `(r, m*, Γ, B) = (1, 1, 32, 1)` —
admissible, `8(m*+1)² = 32 = 1·32` with equality — the value is `2√2·e^{9/64} ≈ 3.2555`, so
**`c₀ ≤ 2` does not hold here** while `c₀ ≤ 10/3` does. A weaker constant is not merely a weaker
statement; it covers admissible parameters that no bound of 2 can. -/
example : Admissible 1 1 32 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

example : cZero 1 1 32 1 ≤ 10 / 3 :=
  cZero_le_ten_thirds_of_one_le_m ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num)

/-- …and the bound `2` already fails at the same admissible triple with `B = 0`, the most
favourable value of the entry factor (`two_lt_cZero_of_admissible`). -/
example : 2 < cZero 1 1 32 0 := two_lt_cZero_of_admissible.2

/-- **The unconditional bound is attained, so it cannot be improved.** All three factor bounds are
simultaneously tight at `(1, 0, 8, 1)`, which is why the crude separate-factor argument is sharp. -/
example : cZero 1 0 8 1 = 4 * Real.exp (9 / 32) := cZero_eq_four_mul_exp_at_worst.2

example : cZero 1 0 8 1 ≤ 4 * Real.exp (9 / 32) :=
  cZero_le_four_mul_exp ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num)

#print axioms two_lt_cZero_of_m_zero_general
#print axioms cZero_le_two_of_gamma_le_seven
#print axioms cZero_le_two_of_gamma_le_six
#print axioms cZero_antitone_gamma
