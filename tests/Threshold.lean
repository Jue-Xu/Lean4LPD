import Lean4LPD.Constants.Threshold

/-!
# Cutoff-existence regressions

Regression and non-vacuity tests for `Lean4LPD.Constants.Threshold`, the norm-level existence
form of `apd:thm:truncation_threshold_entangled`.

* The existence theorems are instantiated at the degenerate base `q = 0`, at a noninteger
  exponent `c = 1/2`, on a family with varying but uniformly bounded mass coefficients, and at
  concrete model constants with `t < tZeroModel`.
* `base_one_counterexample`: the strict inequality `q < 1` cannot be relaxed to `q ≤ 1`.
* `unbounded_mass_counterexample`: the common bound `M` in `exists_uniform_norm_threshold`
  cannot be dropped.
-/

namespace Lean4LPD.ThresholdRegression

/-- Zero-base regression for the norm-level existence part of
`apd:thm:truncation_threshold_entangled`. -/
example (c M ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ (0 : ℝ) ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε :=
  exists_norm_threshold (by norm_num) (by norm_num) c M hε

/-- A noninteger polynomial exponent is covered without replacing it by an assumed
integer estimate (`apd:thm:truncation_threshold_entangled`). -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ (1 / 2 : ℝ) ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ (1 / 2 : ℝ) * 3 ≤ ε :=
  exists_norm_threshold (by norm_num) (by norm_num) (1 / 2) 3 hε

/-- The hypothesis `q < 1` cannot be relaxed to `q ≤ 1`: at `q=1,c=0,M=1` the majorant is
identically `1`, so no finite rung achieves tolerance `1/2`
(`apd:thm:truncation_threshold_entangled`). -/
theorem base_one_counterexample :
    ¬ ∃ m : ℕ, 1 ≤ m ∧ (1 : ℝ) ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ (0 : ℝ) * 1 ≤ 1 / 2 := by
  norm_num

/-- Scalar regression for the uniformity hypothesis of `exists_uniform_norm_threshold`
(`apd:thm:truncation_threshold_entangled`): with unbounded mass factors `M_n=2^n` no single rung
brings all the majorants `(1/2)^(m+1) · 2^n` below `1`, so the common bound `M` cannot be
dropped. This is not a lower-bound theorem about every physical Pauli family. -/
theorem unbounded_mass_counterexample :
    ¬ ∃ m : ℕ, 1 ≤ m ∧ ∀ n : ℕ,
      (1 / 2 : ℝ) ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ (0 : ℝ) *
        (2 : ℝ) ^ n ≤ 1 := by
  rintro ⟨m, _, h⟩
  have hbad := h (m + 2)
  have hp : (1 / 2 : ℝ) ^ (m + 1) * 2 ^ (m + 2) = 2 := by
    rw [div_pow, one_pow, one_div, pow_succ (2 : ℝ) (m + 1), ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  simp only [Real.rpow_zero, mul_one, hp] at hbad
  norm_num at hbad

/-- A family with genuinely varying but uniformly bounded mass coefficients receives one
common rung threshold (`apd:thm:truncation_threshold_entangled`). -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∀ n : ℕ,
      (1 / 2 : ℝ) ^ (m + 1) * (Real.exp 1 * ((m : ℝ) + 1)) ^ (1 / 2 : ℝ) *
        (if n % 2 = 0 then 1 else 2) ≤ ε := by
  apply exists_uniform_norm_threshold (q := 1 / 2) (c := 1 / 2) (M := 2)
    (by norm_num) (by norm_num) _ hε
  intro n m _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  split <;> norm_num

/-- Concrete short-time model constants `(Γ, k_h, α, t) = (2, 2, 1, 1/50)`, for which
`t < tZeroModel = 1/4`, reach every positive norm tolerance
(`apd:thm:truncation_threshold_entangled`). -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ decayBase 2 2 1 (1 / 50) ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ (1 : ℝ) * 1 ≤ ε :=
  exists_model_norm_threshold (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [tZeroModel]) hε

#print axioms norm_majorant_tendsto_zero
#print axioms exists_eventual_norm_threshold
#print axioms exists_norm_threshold
#print axioms exists_uniform_norm_threshold
#print axioms exists_uniform_weight_cutoff
#print axioms exists_model_norm_threshold
#print axioms exists_admissible_step_count
#print axioms base_one_counterexample
#print axioms unbounded_mass_counterexample

end Lean4LPD.ThresholdRegression
