import Lean4LPD.Constants.ChainWeights
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Regression tests for `Lean4LPD/Constants/ChainWeights.lean`

Boundary and non-vacuity checks for the concrete chain weights: the empty chain, the zero
angle `a = 0`, the reservoir endpoint `j = m`, the sharp two-jump corner of
`apd:eq:part_factor`, and a positive-angle instance of the composition count in which every
premise is discharged.
-/

namespace Lean4LPD.ChainWeightsRegression

open Finset

/-- The empty all-ones chain is exactly one, not zero, for `apd:eq:composition_majorant`. -/
example (kh1 c a : ℝ) : chainWeight kh1 c a 0 = 1 := chainWeight_zero kh1 c a

/-- Zero angle kills every all-ones weight with `m ≥ 1`. This is the boundary case that a
ratio form of `apd:eq:part_factor` cannot handle by cancellation. -/
example (kh1 c : ℝ) (m : ℕ) (hm : 1 ≤ m) : chainWeight kh1 c 0 m = 0 := by
  simp [chainWeight, zero_pow (by omega : m ≠ 0)]

/-- The exact jump/all-ones identity remains valid at zero angle and at the reservoir
endpoint `j=m`; no nonzero-angle premise is hidden in `apd:eq:part_factor`'s use here. -/
example (kh1 c : ℝ) (hc : 0 ≤ c) (m : ℕ) :
    epsJump kh1 c 0 m m * chainWeight kh1 c 0 (m - m)
      = partFactor m ((m : ℝ) + c) * chainWeight kh1 c 0 m :=
  epsJump_mul_chainWeight_eq_partFactor hc kh1 0 (le_refl m)

/-- **The sharp two-jump corner is attained**: at `j = m = 2`, `c = 0` the constant `9/4` of
`apd:eq:part_factor` is an equality. An off-by-one in the rung product of `chainWeight` or a
missing factorial in `epsJump` would break this identity. -/
theorem two_jump_equality (kh1 a : ℝ) :
    epsJump kh1 0 a 2 2 = (9 / 4 : ℝ) * chainWeight kh1 0 a 2 := by
  norm_num [epsJump, chainWeight, rungW, Finset.prod_range_succ]
  ring

/-- A single jump costs exactly its single-jump weight, so no `9/4` factor is introduced
at `j=1` (`apd:eq:composition_majorant`). -/
example (kh1 c a : ℝ) : epsJump kh1 c a 1 1 = chainWeight kh1 c a 1 := by
  norm_num [epsJump, chainWeight, rungW, Finset.prod_range_succ]
  ring

/-- The ratio form of the part factor cannot be used at `a = 0`: under Lean's totalized
division the quotient `ε_2^{(2)} / (ε_1^{(1)} ε_1^{(2)})` is zero there, while the part factor is
`9/4`. The library theorem `epsJump_mul_chainWeight_eq_partFactor` therefore proves the
multiplied identity (`apd:eq:part_factor`). -/
theorem zero_angle_quotient_is_not_shape_factor :
    epsJump 1 0 0 2 2 / (epsJump 1 0 0 1 1 * epsJump 1 0 0 1 2)
      ≠ partFactor 2 (2 : ℝ) := by
  norm_num [epsJump, partFactor, rungW, Finset.prod_range_succ]

/-- The generic chain API's `(j,m)=(0,0)` corner is genuinely nonnegative with value one
(`apd:eq:composition_majorant`). -/
example (kh1 c a : ℝ) : epsJump kh1 c a 0 0 = 1 := by simp [epsJump]

/-- A nonzero angle in the entry-tail regime `β ≤ 1/2` of `apd:eq:entry_bound`: the smallness
hypothesis of the chain bounds is satisfiable, and is checked here for a concrete value. -/
theorem small_beta : betaOf 1 0 (1 / 100) ≤ 1 / 2 := by
  unfold betaOf rungW
  norm_num
  nlinarith [Real.exp_one_lt_three]

/-- The test's all-ones reference weight is strictly positive, not a zero-angle/vacuous
instance of `apd:eq:total_high_weight_norm`. -/
theorem small_weight_pos : 0 < chainWeight 1 0 (1 / 100) 3 := by
  norm_num [chainWeight, rungW, Finset.prod_range_succ]

/-- A genuine two-part chain at rung three satisfies the bound with the entry factor once,
not squared. This is the concrete composition count of `apd:eq:total_high_weight_norm`. -/
example :
    chain (epsJump 1 0 (1 / 100)) (entryFactor 1 0 (1 / 100)) 2 3
      ≤ (1 + 2 * betaOf 1 0 (1 / 100)) * (9 / 4 : ℝ)
        * chainWeight 1 0 (1 / 100) 3 * 2 := by
  simpa using chain_epsJump_le_weighted_choose (kh1 := 1) (c := 0) (a := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) small_beta 1 3 (by decide)

/-- The form with the paper's entry constant `1 + 4eβ` holds at a positive angle with every
premise discharged (`apd:eq:total_high_weight_norm`). -/
example (k m : ℕ) (hm : 1 ≤ m) :
    chain (epsJump 1 0 (1 / 100)) (entryFactor 1 0 (1 / 100)) (k + 1) m
      ≤ (1 + 4 * Real.exp 1 * betaOf 1 0 (1 / 100))
        * (9 / 4 : ℝ) ^ (m - (k + 1)) * chainWeight 1 0 (1 / 100) m
        * ((m - 1).choose k : ℝ) :=
  chain_epsJump_le_weighted_choose_source (by norm_num) (by norm_num)
    (by norm_num) small_beta k m hm

#print axioms epsJump_mul_chainWeight_eq_partFactor
#print axioms epsJump_mul_chainWeight_le
#print axioms entryFactor_le_chainWeight
#print axioms epsJump_nonneg_for_chain
#print axioms chain_epsJump_le_weighted_choose
#print axioms chain_epsJump_le_weighted_choose_source
#print axioms two_jump_equality
#print axioms zero_angle_quotient_is_not_shape_factor

end Lean4LPD.ChainWeightsRegression
