import Lean4LPD.Constants.AssemblyBound
import Lean4LPD.Pauli.DiscardWitness

/-!
# Regression tests for `Lean4LPD/Constants/AssemblyBound.lean`

Boundary and non-vacuity checks for the product estimate, the block-inflow slot bounds, the
`D`-sector estimate and the `c₀` assembly of `apd:eq:total_high_weight_norm`: empty products,
the `m = 0` and zero-angle endpoints, a ladder with nonzero inflow, and a two-qubit example
separating the retained high-weight mass from the discarded norm.
-/

namespace Lean4LPD.AssemblyBoundRegression

open Finset PauliString MultiLadder

/-- Regression for `apd:eq:total_high_weight_norm`: at `c=0`,
the product bound has exactly the factorial normalization, including the empty product. -/
theorem zero_shift (n : ℕ) :
    (∏ i ∈ range n, ((i : ℝ) + 1)) ≤ (Nat.factorial n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · simpa using prod_add_one_le_factorial_exp_rpow (c := 0) (by norm_num) n
      (Nat.one_le_iff_ne_zero.mpr hn)

/-- Regression for the shifted product estimate of `apd:eq:total_high_weight_norm`: its `n = 0`
endpoint remains valid for every nonnegative real shift. -/
theorem empty_shifted_product (c : ℝ) (hc : 0 ≤ c) : 1 ≤ (Real.exp 1) ^ c := by
  simpa using prod_shifted_le_factorial_exp_rpow hc 0

/-- A `MultiLadder` with no internal jumps and unit entry factor, `N m T = T`, used as
regression data for the abstract recurrence behind `apd:eq:total_high_weight_norm`. It is not a
Pauli instance. -/
private def entryLadder : MultiLadder (fun _ _ => 0) (fun _ => 1) 1 where
  N _ T := T
  nonneg _ T := Nat.cast_nonneg T
  init _ _ := by simp
  step _ _ _ := by simp

/-- Nonzero reset regression for `apd:eq:total_high_weight_norm`: a unit inflow
in every layer gives a first-power slot bound, not the extra power from a global mass sum. -/
theorem reset_mass_bound (r G : ℕ) (hG : 1 ≤ G) :
    (∑ _d ∈ range r, (G : ℝ)) ≤ ((r : ℝ) + 1) * G := by
  have h := sum_block_inflow_le entryLadder (by intros; norm_num) (by intros; norm_num)
    (by norm_num) (m := 1) (by decide) hG r (fun _ i => (i : ℝ))
    (by intros; simp) (by intros; simp)
  simpa [chain] using h

/-- Regression for the composition count in `apd:eq:total_high_weight_norm`:
unit local weights give the binomial bound without assuming a chain-sum estimate. -/
theorem unit_chain_bound (k m : ℕ) (hm : 1 ≤ m) :
    chain (fun _ _ => 1) (fun _ => 1) (k + 1) m ≤ ((m - 1).choose k : ℝ) := by
  simpa using chain_le_weighted_choose (eps := fun _ _ => 1) (E := fun _ => 1)
    (W := fun _ => 1) (C := 1) (R := 1) (by intros; norm_num)
    (by norm_num) (by norm_num) (by intros; simp) (by intros; simp) k m hm

/-- Regression for `apd:eq:total_high_weight_norm`: at zero part-ratio cost,
the exponential correction is one and the all-single-jump normalization survives. -/
theorem zero_sector_ratio (m : ℕ) (hm : 1 ≤ m) (X : ℝ) (hX : 0 < X) :
    (∑ k ∈ range m, X ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) *
      (0 : ℝ) ^ (m - (k + 1)) * ((m - 1).choose k : ℝ)) ≤
      X ^ m / (Nat.factorial m : ℝ) := by
  simpa using slot_polynomial_le_exp hm hX (R := 0) (by norm_num)

/-- Nonzero abstract regression through the full sector estimate of
`apd:eq:total_high_weight_norm`, with all reset, local-inflow, entry, and jump hypotheses
discharged. -/
theorem reset_exponential_bound (r G : ℕ) (hG : 1 ≤ G) :
    (∑ _d ∈ range r, (G : ℝ)) ≤
      (((r : ℝ) + 1) * G) * Real.exp (1 / (((r : ℝ) + 1) * G)) := by
  have h := sum_block_inflow_le_exp entryLadder (W := fun _ => 1) (C := 1) (R := 1)
    (by intros; norm_num) (by intros; norm_num) (by norm_num)
    (by norm_num) (by norm_num) (m := 1) (by decide) hG (by norm_num)
    r (fun _ i => (i : ℝ)) (by intros; simp) (by intros; simp)
    (by intros; simp) (by intros; simp)
  simpa using h

/-- Regression for `apd:eq:c0`: at `m = 0`, where `c₀` has degree one, it is expanded exactly.
The uniform bound `c₀ ≤ 2`, which requires `m ≥ 1`, is not used. -/
theorem cZero_degree_one (r G B : ℝ) (hB : 0 ≤ B) :
    cZero r 0 G B = (r + 1) / r * Real.exp (9 / 4 / (r * G)) * (1 + B) := by
  simpa using cZero_pow_nat (r := r) (G := G) hB 0

/-- Zero-angle regression through the concrete assembly of `apd:eq:total_high_weight_norm`.
No angle, all-ones weight, or possibly zero binomial is divided out. -/
theorem zero_angle_cZero_instantiation : (∑ _d ∈ range 1, (0 : ℝ)) ≤ 0 := by
  have heps : ∀ j m, 0 ≤ epsJump 1 0 0 j m :=
    epsJump_nonneg_for_chain (by norm_num) (by norm_num) (by norm_num)
  have hE : ∀ m, 0 ≤ entryFactor 1 0 0 m := by
    intro m
    unfold entryFactor
    exact tsum_nonneg fun i => heps (m + i) m
  let L := MultiLadder.trivialMultiLadder heps hE (M := 1) (by norm_num)
  have h := sum_block_epsJump_le_cZero L
    (by norm_num) (by norm_num) (by norm_num) (by simp [betaOf])
    (A := 0) (by norm_num) (by norm_num) (G := 1) (r := 1)
    (by decide) (by decide) (by norm_num) 1 (fun _ _ => 0)
    (by intros; rfl)
    (by intros; simpa [L, MultiLadder.trivialMultiLadder] using hE 2)
  refine h.trans ?_
  simp

/-- Non-vacuity check for `apd:eq:step_component` and `apd:eq:total_high_weight_norm`: in the
two-qubit example of `Lean4LPD.DiscardWitness` the retained trajectory has high-weight norm `0`
at the step boundary while the discarded component has norm `1`, so the retained mass cannot be
substituted for the discarded norm. `MultiLadder.sum_steps_le` is unaffected: it is an abstract
theorem about its own family `N`. -/
theorem retained_mass_ne_discarded_norm :
    highNorm 1 (trotterStepTraj DiscardWitness.Gs DiscardWitness.angles 2 1
      (toMatrix DiscardWitness.P) 1) ≠
    pauliNorm (discardedStep DiscardWitness.Gs DiscardWitness.angles 2 1
      (toMatrix DiscardWitness.P) 0) := by
  rw [highNorm_trotterStepTraj_succ, DiscardWitness.discardedStep_pauliNorm]
  norm_num

#print axioms prod_add_one_le_factorial_exp_rpow
#print axioms prod_shifted_le_factorial_exp_rpow
#print axioms total_truncation_error_product_bound
#print axioms majorant_inflow_eq_shifted_chain
#print axioms shifted_chain_sum_eq_range
#print axioms sum_inflow_majorant_le
#print axioms block_inflow_le
#print axioms sum_block_inflow_le
#print axioms sum_reverse_choose
#print axioms chain_le_weighted_choose
#print axioms factorial_ratio_le_pow
#print axioms sum_factorial_sectors_le_exp
#print axioms slot_polynomial_eq_sectors
#print axioms slot_polynomial_le_exp
#print axioms chain_slot_sum_le_exp
#print axioms sum_block_inflow_le_exp
#print axioms cZero_pow_nat
#print axioms sector_bound_le_cZero
#print axioms sum_block_epsJump_le_exp_source
#print axioms sum_block_epsJump_le_cZero
#print axioms reset_mass_bound
#print axioms reset_exponential_bound
#print axioms zero_angle_cZero_instantiation
#print axioms retained_mass_ne_discarded_norm

end Lean4LPD.AssemblyBoundRegression
