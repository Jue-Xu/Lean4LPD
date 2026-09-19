import Lean4LPD.RotationExp
import Lean4LPD.Pauli.Branch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Exponential-gate regression tests

Regression and non-vacuity checks for `Lean4LPD/RotationExp.lean`, which identifies the
closed-form rotation `rot` with the exponential gate of `apd:eq:pauli_rotation_branch`. They
cover: the actual Mathlib exponential `NormedSpace.exp`, zero and negative angles, the nonzero
`X`/`Z` anticommuting branch, the half-angle, the sign of the exponent, and the necessity of the
involution hypothesis `G * G = 1`. The last section also checks compatibility with the scoped
Euclidean operator norm, without changing the matrix topology used in the theorem statements.

## Main results

* `pauli_exp_mul_neg`: the positive and negative exponential gates are mutually inverse.
* `pauli_exp_pi`, `exp_X_on_Z_eq_Y`: concrete values at nonzero angles, which fix the half-angle
  and the sign of the new term.
* `involution_hypothesis_is_essential`, `half_angle_is_essential`,
  `exponent_sign_is_essential`: the hypothesis `G * G = 1`, the factor `1/2` and the sign of the
  exponent cannot be dropped or changed.
-/

namespace Lean4LPD.RotationExpRegression

open PauliString

example {A : Type*} [Ring A] [Algebra ℂ A] [TopologicalSpace A] [IsTopologicalRing A]
    (G : A) : rot G 0 = NormedSpace.exp ((Complex.I * (0 / 2 : ℝ)) • G) := by
  simp

example {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (G : A) (hG : G * G = 1) (θ : ℝ) :
    rot G θ = NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • G) :=
  rot_eq_exp hG θ

example (θ : ℝ) : rot (toMatrix X1) θ =
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • toMatrix X1) :=
  rot_toMatrix_eq_exp isSelfAdjoint_X1 θ

example (θ : ℝ) : rot (toMatrix Y1) θ =
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • toMatrix Y1) :=
  rot_toMatrix_eq_exp isSelfAdjoint_Y1 θ

example (θ : ℝ) : rot (toMatrix Z1) (-θ) =
    NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • toMatrix Z1) :=
  rot_toMatrix_neg_eq_exp isSelfAdjoint_Z1 θ

/-- For a Hermitian Pauli string `G`, the exponentials `exp ((I * (θ/2)) • G)` and
`exp ((-I * (θ/2)) • G)` are mutually inverse gates, in the half-angle and sign convention of
`apd:eq:pauli_rotation_branch`. -/
theorem pauli_exp_mul_neg {n : ℕ} {G : PauliString n} (hG : IsSelfAdjoint G) (θ : ℝ) :
    NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • toMatrix G) *
      NormedSpace.exp ((-Complex.I * (θ / 2 : ℝ)) • toMatrix G) = 1 := by
  rw [← rot_toMatrix_eq_exp hG, ← rot_toMatrix_neg_eq_exp hG]
  exact rot_mul_rot_neg (toMatrix_mul_self_of_isSelfAdjoint hG)

/-- At a nonzero angle the genuine exponential is computed exactly: `exp (i (π/2) X) = i X`.
This tests the half-angle in `apd:eq:pauli_rotation_branch`, since it is `rot X π`. -/
theorem pauli_exp_pi :
    NormedSpace.exp ((Complex.I * (Real.pi / 2 : ℝ)) • toMatrix X1) =
      Complex.I • toMatrix X1 := by
  rw [← rot_toMatrix_eq_exp isSelfAdjoint_X1 Real.pi]
  simp [rot, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The anticommuting branch with genuine exponentials creates `+Y`, not `-Y`: at conjugation
angle `π/2`, `e^{i X π/4} Z e^{-i X π/4} = Y`. This fixes the sign of the new term under the
paper's convention, with the positive exponent on the left of the Heisenberg conjugation
(`apd:eq:pauli_rotation_branch`). -/
theorem exp_X_on_Z_eq_Y :
    NormedSpace.exp ((Complex.I * ((Real.pi / 2) / 2 : ℝ)) • toMatrix X1) * toMatrix Z1 *
      NormedSpace.exp ((-Complex.I * ((Real.pi / 2) / 2 : ℝ)) • toMatrix X1) = toMatrix Y1 := by
  rw [← rot_toMatrix_eq_exp isSelfAdjoint_X1, ← rot_toMatrix_neg_eq_exp isSelfAdjoint_X1,
    pauli_rotation_branch_anticommute_hermitian isSelfAdjoint_X1 sympForm_X1_Z1,
    Real.cos_pi_div_two, Real.sin_pi_div_two, phaseMul_one_X1_mul_Z1]
  simp

/-- The hypothesis `G * G = 1` of `rot_eq_exp` cannot be dropped: `G = 0` gives `rot 0 π = 0`
but `exp 0 = 1`. -/
theorem involution_hypothesis_is_essential :
    rot (0 : ℂ) Real.pi ≠ NormedSpace.exp ((Complex.I * (Real.pi / 2 : ℝ)) • (0 : ℂ)) := by
  simp [rot, Real.cos_pi_div_two]

/-- The factor `1/2` in `rot_eq_exp` cannot be dropped: at `G = 1` and `θ = π`,
`rot 1 π = i` whereas the full-angle exponential is `exp (i π) = -1`. The half-angle of
`apd:eq:pauli_rotation_branch` is therefore part of the statement, not a notational choice. -/
theorem half_angle_is_essential :
    rot (1 : ℂ) Real.pi ≠ NormedSpace.exp (Complex.I * (Real.pi : ℂ)) := by
  rw [← Complex.exp_eq_exp_ℂ, mul_comm Complex.I (Real.pi : ℂ), Complex.exp_pi_mul_I]
  simp [rot, Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ext_iff]

/-- The sign of the exponent in `apd:eq:pauli_rotation_branch` matters: at `G = 1` and `θ = π`
the two scalar gates `exp (i π/2)` and `exp (-i π/2)` are `i` and `-i`. -/
theorem exponent_sign_is_essential :
    NormedSpace.exp ((Complex.I * (Real.pi / 2 : ℝ)) • (1 : ℂ)) ≠
      NormedSpace.exp ((-Complex.I * (Real.pi / 2 : ℝ)) • (1 : ℂ)) := by
  rw [← rot_eq_exp (G := (1 : ℂ)) (by simp) Real.pi,
    ← rot_neg_eq_exp (G := (1 : ℂ)) (by simp) Real.pi]
  norm_num [rot, neg_div, Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ext_iff]

section L2Operator

open scoped Matrix.Norms.L2Operator

example {n : ℕ} {G : PauliString n} (hG : IsSelfAdjoint G) (θ : ℝ) :
    rot (toMatrix G) θ = NormedSpace.exp ((Complex.I * (θ / 2 : ℝ)) • toMatrix G) :=
  rot_toMatrix_eq_exp hG θ

end L2Operator

#print axioms exp_smul_I_of_involution
#print axioms rot_eq_exp
#print axioms rot_toMatrix_eq_exp
#print axioms exp_conj_of_anticommute
#print axioms exp_X_on_Z_eq_Y
#print axioms involution_hypothesis_is_essential
#print axioms half_angle_is_essential
#print axioms exponent_sign_is_essential

end Lean4LPD.RotationExpRegression
