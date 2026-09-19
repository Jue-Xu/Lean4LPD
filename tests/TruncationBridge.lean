import Lean4LPD.Pauli.DiscardWitness

/-!
# Regression tests for the truncation/discard bridge

These tests exercise the definitions of `Lean4LPD.Pauli.TrotterTruncate`: the end-of-step
truncation schedule `trotterSchedule` of `apd:thm:triangle` and the discarded operator
`discardedStep` of `apd:eq:step_component`. They consist of boundary cases (empty and full
retained sets, block lengths one and zero, a cutoff at or above the number of qubits) and of
instantiations on the two-qubit witness of `Lean4LPD.Pauli.DiscardWitness`, whose first
discarded operator is nonzero. No target estimate is supplied as a hypothesis.

## Main results

* `period_zero_counterexample`: the hypothesis `0 < period` of `trotterTraj_at_boundary` cannot
  be dropped.
* `differs_from_per_rotation_cut`: the end-of-step schedule is not the same as truncating after
  every rotation.
* `named_boundary_identity`, `named_witness_ladder_instance`: `discardedStep_eq_boundary_sub` and
  `pauliNorm_discardedStep_le` instantiated on the witness.
-/

namespace Lean4LPD.TruncationBridgeRegression

open Finset PauliString

example {n : ℕ} (O : Matrix (Bits n) (Bits n) ℂ) (w : ℕ) :
    pauliNorm (O - truncOp (highSet n w)ᶜ O) = highNorm w O :=
  pauliNorm_sub_truncOp_highSet_compl w O

example {n : ℕ} (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    truncOp S O + truncOp Sᶜ O = O := by
  rw [← sub_truncOp, add_comm, sub_add_cancel]

example {n : ℕ} (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    truncOp S (truncOp S O) = truncOp S O := by
  apply coeff_ext
  intro p
  by_cases hp : p ∈ S
  · simp only [coeff_truncOp, ite_eq_left hp]
  · simp only [coeff_truncOp, ite_eq_right hp]

example {n : ℕ} (O : Matrix (Bits n) (Bits n) ℂ) : truncOp ∅ O = 0 := by
  simp [truncOp]

example {n : ℕ} (O : Matrix (Bits n) (Bits n) ℂ) : O - truncOp univ O = 0 := by
  rw [truncOp_univ, sub_self]

example (n w g : ℕ) : trotterSchedule (n := n) 1 w g = (highSet n w)ᶜ := by
  simp only [trotterSchedule, Nat.mod_one, ↓reduceIte]

example (n w : ℕ) : trotterSchedule (n := n) 3 w 3 = univ := by
  simp [trotterSchedule]

example (n w : ℕ) : trotterSchedule (n := n) 3 w 5 = (highSet n w)ᶜ := by
  simp [trotterSchedule]

example (n w g : ℕ) : trotterSchedule (n := n) 0 w g = univ := by
  simp [trotterSchedule]

example {n : ℕ} (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    trotterTraj Gs θ 1 w O g =
      trajTrunc (fun _ => Gs 0) (fun _ => θ 0) (fun _ => (highSet n w)ᶜ) O g := by
  have hs : trotterSchedule (n := n) 1 w = fun _ => (highSet n w)ᶜ := by
    funext i
    simp only [trotterSchedule, Nat.mod_one, ↓reduceIte]
  simp only [trotterTraj, hs, Nat.mod_one]

/-- If the cutoff is at least the number of qubits, the high-weight sector is empty: no Pauli on
`n` qubits has weight above `n`. Boundary case for `apd:eq:step_component`. -/
theorem highSet_empty_of_dim_le {n w : ℕ} (hnw : n ≤ w) : highSet n w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro p hp
  have hpw := mem_highSet.1 hp
  have hdim : wt p ≤ n := by
    change (support (herm p)).card ≤ n
    simpa using (Finset.card_le_card (Finset.subset_univ (support (herm p))))
  omega

example {n w period : ℕ} (hnw : n ≤ w) (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    discardedStep Gs θ period w O d = 0 := by
  rw [discardedStep_eq_truncOp, highSet_empty_of_dim_le hnw, truncOp]
  exact Finset.sum_empty

example (Gs : ℕ → PauliString 0) (θ : ℕ → ℝ)
    (O : Matrix (Bits 0) (Bits 0) ℂ) (period w d : ℕ) :
    discardedStep Gs θ period w O d = 0 := by
  rw [discardedStep_eq_truncOp, highSet_empty_of_dim_le (Nat.zero_le w), truncOp]
  exact Finset.sum_empty

/-- A cut at weight zero removes the one-qubit Pauli `Z` entirely. Helper for
`period_zero_counterexample`. -/
theorem cut_Z1 : truncOp (highSet 1 0)ᶜ (toMatrix Z1) = 0 := by
  have hz : herm (cls Z1) = Z1 := by decide
  rw [truncOp]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpz : p ≠ cls Z1 := by
    intro h
    subst p
    exact (Finset.mem_compl.1 hp) (mem_highSet.2 (by decide))
  rw [← hz, coeff_toMatrix_herm, ite_eq_right hpz, zero_smul]

/-- The hypothesis `0 < period` of `trotterTraj_at_boundary` cannot be dropped. At `period = 0`
one step of the whole-block recurrence still applies the cut, here removing `Z`, whereas the
rotation-indexed trajectory at index `1 * 0 = 0` is still the input
(`apd:eq:step_component`). -/
theorem period_zero_counterexample (Gs : ℕ → PauliString 1) (θ : ℕ → ℝ) :
    trotterTraj Gs θ 0 0 (toMatrix Z1) (1 * 0) ≠
      trotterStepTraj Gs θ 0 0 (toMatrix Z1) 1 := by
  simp only [mul_zero, trotterTraj_zero, trotterStepTraj_succ,
    trotterStepTraj_zero, traj_zero, cut_Z1]
  exact toMatrix_ne_zero Z1

/-- Truncating after every rotation is not the end-of-step schedule of `apd:thm:triangle`. On
the two-qubit witness the scheduled trajectory still contains the weight-two Pauli `Q` after the
first rotation, whereas a cut at weight one after that rotation removes it. -/
theorem differs_from_per_rotation_cut :
    trotterTraj DiscardWitness.Gs DiscardWitness.angles 2 1 (toMatrix DiscardWitness.P) 1 ≠
      trajTrunc DiscardWitness.Gs DiscardWitness.angles (fun _ => (highSet 2 1)ᶜ)
        (toMatrix DiscardWitness.P) 1 := by
  rw [DiscardWitness.interior_eq_Q]
  change toMatrix DiscardWitness.Q ≠ truncOp (highSet 2 1)ᶜ
    (rot (toMatrix DiscardWitness.G) (Real.pi / 2) * toMatrix DiscardWitness.P *
      rot (toMatrix DiscardWitness.G) (-(Real.pi / 2)))
  rw [DiscardWitness.first_rotation, DiscardWitness.cutoff_Q]
  exact toMatrix_ne_zero DiscardWitness.Q

example : highNorm 1 (toMatrix DiscardWitness.P) = 0 := DiscardWitness.input_highNorm
example : (highSet 2 1).Nonempty := DiscardWitness.highSet_nonempty
example : (highSet 2 1)ᶜ ≠ univ := DiscardWitness.cutoff_ne_univ
example : discardedStep DiscardWitness.Gs DiscardWitness.angles 2 1
    (toMatrix DiscardWitness.P) 0 ≠ 0 := DiscardWitness.discardedStep_ne_zero
example : pauliNorm (discardedStep DiscardWitness.Gs DiscardWitness.angles 2 1
    (toMatrix DiscardWitness.P) 0) = 1 := DiscardWitness.discardedStep_pauliNorm

/-- `discardedStep_eq_boundary_sub` instantiated on the two-qubit witness: the first discarded
operator is the final rotation applied to the interior state, minus the state at the step
boundary (`apd:eq:step_component`). -/
theorem named_boundary_identity :
    discardedStep DiscardWitness.Gs DiscardWitness.angles 2 1 (toMatrix DiscardWitness.P) 0 =
      rot (toMatrix DiscardWitness.Q) (Real.pi / 2) *
        trotterTraj DiscardWitness.Gs DiscardWitness.angles 2 1 (toMatrix DiscardWitness.P) 1 *
        rot (toMatrix DiscardWitness.Q) (-(Real.pi / 2)) -
      trotterTraj DiscardWitness.Gs DiscardWitness.angles 2 1 (toMatrix DiscardWitness.P) 2 := by
  exact discardedStep_eq_boundary_sub DiscardWitness.Gs DiscardWitness.angles 2 1
    (toMatrix DiscardWitness.P) 0 (by decide)

/-- `pauliNorm_discardedStep_le` instantiated on the two-qubit witness: the norm of its nonzero
first discarded operator is bounded by the two ladder rungs just before the step boundary
(`apd:thm:local_flow_k_local`). -/
theorem named_witness_ladder_instance :
    pauliNorm (discardedStep DiscardWitness.Gs DiscardWitness.angles 2 1
      (toMatrix DiscardWitness.P) 0) ≤
      ladderNTrunc (fun j => DiscardWitness.Gs (j % 2))
        (fun j => DiscardWitness.angles (j % 2)) (trotterSchedule 2 1)
        (toMatrix DiscardWitness.P) 1 2 1 1 +
      |Real.sin (DiscardWitness.angles 1)| *
        ladderNTrunc (fun j => DiscardWitness.Gs (j % 2))
          (fun j => DiscardWitness.angles (j % 2)) (trotterSchedule 2 1)
          (toMatrix DiscardWitness.P) 1 2 0 1 := by
  exact pauliNorm_discardedStep_le
    (Gs := DiscardWitness.Gs) (θ := DiscardWitness.angles)
    (period := 2) (wstar := 1) (ko := 1) (kh := 2) (m := 1)
    (O := toMatrix DiscardWitness.P)
    DiscardWitness.generators_selfAdjoint
    (fun g => le_of_eq (DiscardWitness.generators_weight g))
    (by decide) (by decide) (by rfl) 0

#print axioms period_zero_counterexample
#print axioms differs_from_per_rotation_cut
#print axioms named_boundary_identity
#print axioms named_witness_ladder_instance

end Lean4LPD.TruncationBridgeRegression
