import Lean4LPD.Pauli.Tensor

/-!
# Tensor-representation regressions

Regression tests for `Lean4LPD/Pauli/Tensor.lean`, which identifies the entrywise model
`toMatrix` with the tensor products of `def:pauli_basis`:

* the one-qubit tensors are `toMatrix` of `X1`, `Y1`, `Z1`, and the empty tensor is `1`;
* the double-`Y` class `yy`, the smallest case in which the phase matters: the positive tensor
  `Y ⊗ Y` is *minus* the matrix of the parity representative `herm yy`
  (`yy_tensor_eq_neg_herm`, `herm_is_not_positive_yy`);
* Hermiticity, orthogonality of the trace pairing, and the adjoint-preserving change of index
  type, instantiated for all `n`.
-/

namespace Lean4LPD.TensorRegression

open PauliString Matrix

example : tensorPauli 1 X1.x X1.z = toMatrix X1 := by
  have hx : tensorRepresentative (cls X1) = X1 := by decide
  simpa only [hx, cls_fst, cls_snd] using (toMatrix_tensorRepresentative (cls X1)).symm

example : tensorPauli 1 Y1.x Y1.z = toMatrix Y1 := by
  have hy : tensorRepresentative (cls Y1) = Y1 := by decide
  simpa only [hy, cls_fst, cls_snd] using (toMatrix_tensorRepresentative (cls Y1)).symm

example : tensorPauli 1 Z1.x Z1.z = toMatrix Z1 := by
  have hz : tensorRepresentative (cls Z1) = Z1 := by decide
  simpa only [hz, cls_fst, cls_snd] using (toMatrix_tensorRepresentative (cls Z1)).symm

example (x z : Bits 0) : tensorPauli 0 x z = 1 := rfl

/-- Double-Y class, the smallest sign-sensitive case of `def:pauli_basis`. -/
def yy : PauliIndex 2 := (fun _ => 1, fun _ => 1)

/-- Full Y count, not its parity, fixes positive tensors in `def:pauli_basis`. -/
theorem yy_phase : yPhase yy.1 yy.2 = 2 := by decide

/-- The positive double-`Y` representative is the parity representative `herm yy` with its
phase shifted by `2`, that is, with the opposite sign (`def:pauli_basis`). -/
theorem yy_representative_phase : tensorRepresentative yy = phaseMul 2 (herm yy) := by decide

/-- The double-`Y` sign as a matrix identity: `Y ⊗ Y = -toMatrix (herm yy)`
(`def:pauli_basis`). -/
theorem yy_tensor_eq_neg_herm : tensorPauli 2 yy.1 yy.2 = -toMatrix (herm yy) := by
  rw [← toMatrix_tensorRepresentative, yy_representative_phase, toMatrix_phaseMul, iPow_two]
  simp

/-- The double-`Y` sign is genuine: since the matrix is nonzero, `toMatrix (herm yy)` is not
equal to the positive tensor `Y ⊗ Y` (`def:pauli_basis`). -/
theorem herm_is_not_positive_yy : toMatrix (herm yy) ≠ tensorPauli 2 yy.1 yy.2 := by
  intro h
  have he : toMatrix (herm yy) = -toMatrix (herm yy) := h.trans yy_tensor_eq_neg_herm
  have htwo : (2 : ℂ) • toMatrix (herm yy) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr he
  have hz : toMatrix (herm yy) = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact toMatrix_ne_zero _ hz

example (n : ℕ) (p : PauliIndex n) : IsSelfAdjoint (tensorPauli n p.1 p.2) :=
  isSelfAdjoint_tensorPauli p

example (n : ℕ) (p : PauliIndex n) :
    (tensorPauli n p.1 p.2 * tensorPauli n p.1 p.2).trace = (2 : ℂ) ^ n := by
  rw [trace_tensorPauli_mul, ite_eq_left rfl]

example (n : ℕ) (p q : PauliIndex n) (hpq : p ≠ q) :
    (tensorPauli n p.1 p.2 * tensorPauli n q.1 q.2).trace = 0 := by
  rw [trace_tensorPauli_mul, ite_eq_right hpq]

example (n : ℕ) (A B : Matrix (Bits n) (Bits n) ℂ) :
    bitsMatrixEquiv n (A * B) = bitsMatrixEquiv n A * bitsMatrixEquiv n B :=
  (bitsMatrixEquiv n).map_mul A B

example (n : ℕ) (A : Matrix (Bits n) (Bits n) ℂ) :
    bitsMatrixEquiv n (star A) = star (bitsMatrixEquiv n A) := bitsMatrixEquiv_star n A

#print axioms Lean4LPD.PauliString.toMatrix_eq_phase_tensor
#print axioms Lean4LPD.PauliString.isSelfAdjoint_tensorRepresentative
#print axioms Lean4LPD.PauliString.trace_tensorPauli_mul
#print axioms Lean4LPD.PauliString.bitsMatrixEquiv
#print axioms yy_tensor_eq_neg_herm
#print axioms herm_is_not_positive_yy

end Lean4LPD.TensorRegression
