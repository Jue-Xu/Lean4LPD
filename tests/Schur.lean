import Lean4LPD.Schur

/-!
# Schur-test regressions

Regression tests for `Lean4LPD/Schur.lean`, the Schur step of `apd:thm:layer_inflow`, on concrete
rectangular complex matrices.

* The `2 × 3` all-ones matrix `ones23` has row sums `3` and column sums `2`, so
  `l2_opNorm_le_schur` gives `‖ones23‖ ≤ √6`. The constant is sharp: at the all-ones vector both
  sides of `schur_mulVec_sq_le` equal `18`.
* Matrices with an empty row or column index type are covered without a nonemptiness hypothesis.
* `row_bound_alone_insufficient`: the column bound cannot be dropped.

The tests use nothing about Pauli branch blocks; their row and column bounds are proved in
`Lean4LPD/Pauli/LayerFlow.lean`.
-/

namespace Lean4LPD.SchurRegression

open Matrix Finset WithLp
open scoped Matrix.Norms.L2Operator

/-- The `2 × 3` all-ones complex matrix, with row sums `3` and column sums `2`. The Schur bound
used in `apd:thm:layer_inflow` is sharp on it. -/
def ones23 : Matrix (Fin 2) (Fin 3) ℂ := fun _ _ => 1

example : ‖ones23‖ ≤ Real.sqrt 6 := by
  have h := l2_opNorm_le_schur (R := 3) (C := 2) ones23 (by norm_num) (by norm_num)
    (fun i => by norm_num [ones23]) (fun j => by norm_num [ones23])
  norm_num at h
  exact h

example : (∑ i : Fin 2, ‖(ones23 *ᵥ (fun _ => 1)) i‖ ^ 2) = 18 := by
  norm_num [ones23, Matrix.mulVec, dotProduct]

example : (3 : ℝ) * 2 * ∑ _j : Fin 3, ‖(1 : ℂ)‖ ^ 2 = 18 := by norm_num

example : ‖(0 : Matrix (Fin 0) (Fin 3) ℂ)‖ ≤ 0 := by
  exact l2_opNorm_le_of_row_col_bound _ (by norm_num) (by simp) (by simp)

example : ‖(0 : Matrix (Fin 2) (Fin 0) ℂ)‖ ≤ 0 := by
  exact l2_opNorm_le_of_row_col_bound _ (by norm_num) (by simp) (by simp)

/-- The column bound in the Schur test of `apd:thm:layer_inflow` cannot be dropped: in the
`2 × 1` all-ones matrix each row has absolute sum one, but the ℓ² operator norm exceeds one. -/
theorem row_bound_alone_insufficient :
    ∃ A : Matrix (Fin 2) (Fin 1) ℂ, (∀ i, ∑ j, ‖A i j‖ ≤ 1) ∧ ¬ ‖A‖ ≤ 1 := by
  let A : Matrix (Fin 2) (Fin 1) ℂ := fun _ _ => 1
  let y : EuclideanSpace ℂ (Fin 1) := toLp 2 (fun _ => 1)
  refine ⟨A, ?_, ?_⟩
  · intro i; norm_num [A]
  · have hynorm : ‖y‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      norm_num [y]
    have hAy : ‖clm A y‖ ^ 2 = 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      change (∑ i : Fin 2, ‖(A *ᵥ y.ofLp) i‖ ^ 2) = 2
      norm_num [A, y, Matrix.mulVec, dotProduct]
    intro hA
    have hbound : ‖clm A y‖ ≤ ‖A‖ * ‖y‖ :=
      (Matrix.l2_opNorm_def A) ▸ ContinuousLinearMap.le_opNorm _ _
    rw [hynorm, mul_one] at hbound
    nlinarith [norm_nonneg (clm A y)]

#print axioms Lean4LPD.schur_mulVec_le
#print axioms Lean4LPD.l2_opNorm_le_schur
#print axioms row_bound_alone_insufficient

end Lean4LPD.SchurRegression
