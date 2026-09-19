/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import Lean4LPD.Constants.C0
import Lean4LPD.Constants.Entry
import Lean4LPD.Constants.PartFactor
import Lean4LPD.Constants.StepSum
import Lean4LPD.Constants.Total
import Lean4LPD.Constants.AssemblyBound
import Lean4LPD.Constants.Threshold
import Lean4LPD.Ladder.Assembly
import Lean4LPD.Ladder.MultiJump
import Lean4LPD.Ladder.Recursion
import Lean4LPD.Ladder.Weighted
import Lean4LPD.BlockNorm
import Lean4LPD.Pauli.Branch
import Lean4LPD.Pauli.Count
import Lean4LPD.Pauli.DiscardWitness
import Lean4LPD.Pauli.Flow
import Lean4LPD.Pauli.LayerWitness
import Lean4LPD.Pauli.Trace
import Lean4LPD.Pauli.Truncate
import Lean4LPD.Pauli.LayerError
import Lean4LPD.Pauli.LayerCounterexample
import Lean4LPD.Pauli.Tensor
import Lean4LPD.Rotation
import Lean4LPD.RotationExp

/-!
# Axiom audit

Prints the axioms each headline theorem of the library depends on. Every declaration listed
below depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axiom at all (see
the Trust base section of `README.md`). CI elaborates this file and checks its output with
`scripts/check_axioms.py`, so an accidental new dependency fails the build.

Axiom-free is not assumption-free: what each theorem assumes is in its statement, and an axiom
report does not say whether a definition models what it is meant to model. For the two modelling
choices of this library that question is settled by theorems, which are audited here as well.
`RotationExp` proves that the rotation `rot G θ = cos (θ/2) • 1 + i sin (θ/2) • G` is the matrix
exponential `exp (i (θ/2) G)` whenever `G * G = 1`, and `Pauli/Tensor` proves that the entrywise
Pauli-string matrix `toMatrix` is a power of `i` times the Kronecker product of single-qubit
Pauli matrices.

## Guide to the audited names

The `#print axioms` lines come in two blocks. The first follows the single-rotation chain.

* `Ladder/` — the abstract damped recursion: the hockey-stick identity `sum_range_choose`, the
  single-jump cumulation bounds `Ladder.cumulation`, `WeightedLadder.cumulation` and
  `layer_cumulation` (`apd:cor:norm_cumulation_jump`), and the multi-jump majorant
  `MultiLadder.le_majorant` with its monotonicity and its sum over steps
  (`apd:eq:composition_majorant`).
* `Constants/` — the scalar estimates: `entryFactor_le`, `partFactor_le`, the sums over steps,
  the time threshold (`tZeroModel_le_tZero`, `decayBase_lt_one`), `total_truncation_error`, and
  the constant `c₀` of `apd:eq:c0`. `cZero_le_two` and its variants are upper bounds. The
  `two_lt_cZero_*` theorems are necessity witnesses: parameter points at which a hypothesis of
  `cZero_le_two` fails and `c₀ > 2`. `cZero_eq_four_mul_exp_at_worst` shows that the uniform
  bound `cZero_le_four_mul_exp` is attained.
* `Rotation`, `Pauli/Basic`, `Pauli/Matrix`, `Pauli/Weight`, `Pauli/Branch` — Pauli rotations:
  conjugation of a commuting or an anticommuting operator, the commute-or-anticommute dichotomy,
  the change of weight under multiplication, and the two-branch formula `pauli_rotation_branch`
  (`apd:eq:pauli_rotation_branch`).
* `Pauli/Trace`, `Pauli/Coeff`, `Pauli/Flow` — orthogonality and Parseval for Pauli coefficients,
  invariance of the normalized Pauli norm under conjugation, and the one-rotation flow bound
  `local_flow_k_local` (`apd:thm:local_flow_k_local`). `pauliLadder` is the entry to read: it is
  a `Ladder`-valued *definition*, so its axiom report covers the proof of its `step` field, which
  is `local_flow_k_local`, and with it everything `Ladder/` and `Constants/` derive from that
  field.
* `Pauli/Truncate`, `Pauli/Discard`, `Pauli/TrotterTruncate`, `Pauli/DiscardWitness` — the
  truncated trajectory, which is what LPD runs. `pauliLadder` is a ladder for the untruncated
  flow; `pauliLadderTrunc` is the same ladder with truncations interleaved. `truncOp_univ` and
  `trajTrunc_univ` are not dependencies of `pauliLadderTrunc`. They are listed because they show
  that the truncated trajectory generalizes `traj` (retaining every Pauli recovers it), and
  `truncOp_univ` is completeness of the Pauli expansion, proved from Parseval rather than
  assumed. The `discardedStep` lemmas identify the operator removed at a step boundary
  (`apd:eq:step_component`) and equate its norm with a high-weight norm; the `DiscardWitness`
  entries exhibit a step whose discarded operator is nonzero.
* `Pauli/LayerWitness` — weight growth across layers. `reachable_weight_le` bounds the weight
  after `ℓ` layers by `k_h ^ ℓ` times the initial weight. The `gamma_weight_bound_false*`
  witnesses are combinatorial: they use the reachable set, which over-approximates the support.
* `BlockNorm` — a block of a matrix has ℓ² operator norm at most that of the matrix, hence at
  most one for a unitary or an orthogonal matrix. The block closes with the angle-addition law
  `rot_mul_rot` of `Rotation`.

The second block is the norm-level error chain for whole layers, together with the two
representation bridges.

* `Schur` — the finite Schur test for the ℓ² operator norm.
* `RotationExp`, `Pauli/Tensor` — the representation bridges described above.
* `Pauli/TruncationError` — the telescoping identity and the triangle bound of
  `apd:thm:triangle` at the level of the normalized Pauli norm.
* `Pauli/LayerFlow`, `Pauli/LayerLadder` — the layer inflow bound (`apd:thm:layer_inflow`), from
  row and column sums of the jump matrices through the Schur test, and the resulting
  `MultiLadder`-valued definition `pauliMultiLadder`, which plays for whole layers the role
  `pauliLadder` plays for single rotations (`apd:rmk:multijump`).
* `Ladder/ChainBound`, `Constants/ChainWeights`, `Constants/AssemblyBound` — the scalar assembly
  of `apd:eq:total_high_weight_norm`: the inflow of a `MultiLadder`, summed over steps, is at most
  `(c₀ Γ A) ^ (m + 1)` times a product of rung weights divided by `(m + 1)!`.
* `Pauli/LayerError` — the truncation error of the layered evolution in normalized Pauli norm;
  `pauliNorm_layerStep_error_le_model_of_source_regime` is the same bound in the paper's
  parameter regime.
* `Constants/Threshold` — existence of a weight cutoff and of a step count meeting the
  hypotheses of the error bound.
* `Pauli/LayerCounterexample` — the operator-level counterpart of the `LayerWitness` entries.
  For a second-order product-formula step, `actual_discard_exceeds_gamma_bound` exhibits a
  discarded Pauli of weight greater than `w* k_h ^ Γ = 4` (the witness has weight `6`) whose
  coefficient is nonzero. The coefficient is computed, not inferred from reachability. So the
  weight reached within one such step is not bounded by `w* k_h ^ Γ`.
* `Pauli/Count` — the number of Pauli strings of weight at most `w`.
-/

#print axioms Lean4LPD.sum_range_choose
#print axioms Lean4LPD.Ladder.step_iterate
#print axioms Lean4LPD.Ladder.cumulation
#print axioms Lean4LPD.WeightedLadder.cumulation
#print axioms Lean4LPD.layer_cumulation
#print axioms Lean4LPD.MultiLadder.le_majorant
#print axioms Lean4LPD.MultiLadder.majorant_mono
#print axioms Lean4LPD.MultiLadder.majorant_eq_sum_range
#print axioms Lean4LPD.MultiLadder.sum_steps_le
#print axioms Lean4LPD.chain_diag
#print axioms Lean4LPD.entryFactor_le
#print axioms Lean4LPD.partFactor_le
#print axioms Lean4LPD.sum_pow_le
#print axioms Lean4LPD.sum_choose_mul_le
#print axioms Lean4LPD.prod_rungW_eq
#print axioms Lean4LPD.prod_shift_ratio
#print axioms Lean4LPD.tZeroModel_le_tZero
#print axioms Lean4LPD.lt_tZero_of_lt_tZeroModel
#print axioms Lean4LPD.decayBase_lt_one
#print axioms Lean4LPD.total_truncation_error
#print axioms Lean4LPD.cZero_le_two
#print axioms Lean4LPD.cZero_le_two_without_m_le_r
#print axioms Lean4LPD.cZero_antitone_gamma
#print axioms Lean4LPD.cZero_extremal_isotone_gamma
#print axioms Lean4LPD.cZero_le_two_of_three_le_m
#print axioms Lean4LPD.cZero_le_four_mul_exp
#print axioms Lean4LPD.cZero_eq_four_mul_exp_at_worst
#print axioms Lean4LPD.cZero_le_ten_thirds_of_one_le_m
#print axioms Lean4LPD.two_lt_cZero_of_m_two
#print axioms Lean4LPD.exp_factor_le_sharp
#print axioms Lean4LPD.le_r_of_gamma_le_six
#print axioms Lean4LPD.cZero_le_two_of_gamma_le_six
#print axioms Lean4LPD.cZero_le_two_of_gamma_le_seven
#print axioms Lean4LPD.two_lt_cZero_of_m_zero_general
#print axioms Lean4LPD.two_lt_cZero_of_admissible
#print axioms Lean4LPD.two_lt_cZero_of_admissible_four
#print axioms Lean4LPD.two_lt_cZero_of_m_zero
#print axioms Lean4LPD.rot_conj_of_commute
#print axioms Lean4LPD.rot_conj_of_anticommute
#print axioms Lean4LPD.rot_mem_unitary
#print axioms Lean4LPD.PauliString.commute_or_anticommute
#print axioms Lean4LPD.PauliString.isSelfAdjoint_iff_mul_self_eq_one
#print axioms Lean4LPD.PauliString.isSelfAdjoint_phaseMul_one_mul
#print axioms Lean4LPD.PauliString.toMatrix_mul
#print axioms Lean4LPD.PauliString.toMatrix_star
#print axioms Lean4LPD.PauliString.toMatrix_injective
#print axioms Lean4LPD.PauliString.toMatrix_commute_or_anticommute
#print axioms Lean4LPD.PauliString.weight_sub_le_weight_mul
#print axioms Lean4LPD.PauliString.abs_weight_mul_sub_weight_le
#print axioms Lean4LPD.PauliString.toMatrix_mul_ne_smul
#print axioms Lean4LPD.PauliString.linearIndependent_toMatrix_mul_pair
#print axioms Lean4LPD.PauliString.isSelfAdjoint_toMatrix_iff
#print axioms Lean4LPD.PauliString.pauli_rotation_branch
#print axioms Lean4LPD.PauliString.pauli_rotation_branch_anticommute_hermitian
#print axioms Lean4LPD.PauliString.pauli_rotation_branch_anticommute_bounds
#print axioms Lean4LPD.PauliString.char_sum
#print axioms Lean4LPD.PauliString.trace_star_toMatrix_mul
#print axioms Lean4LPD.PauliString.trace_star_toMatrix_mul_self
#print axioms Lean4LPD.PauliString.sum_norm_coeff_sq
#print axioms Lean4LPD.PauliString.norm_coeffVec
#print axioms Lean4LPD.PauliString.coeff_toMatrix_herm
#print axioms Lean4LPD.PauliString.coeff_conj
#print axioms Lean4LPD.PauliString.norm_rotAct
#print axioms Lean4LPD.PauliString.pauliNorm_conj
#print axioms Lean4LPD.PauliString.highNorm_conj_le_highNorm
#print axioms Lean4LPD.PauliString.local_flow_k_local
#print axioms Lean4LPD.PauliString.pauliLadder
#print axioms Lean4LPD.PauliString.pauliWeightedLadder
#print axioms Lean4LPD.PauliString.pauliLadderOfHerm
#print axioms Lean4LPD.PauliString.coeff_truncOp
#print axioms Lean4LPD.PauliString.truncOp_univ
#print axioms Lean4LPD.PauliString.sum_coeff_smul_toMatrix_herm
#print axioms Lean4LPD.PauliString.highNorm_truncOp_le
#print axioms Lean4LPD.PauliString.trajTrunc_univ
#print axioms Lean4LPD.PauliString.highNorm_conj_trajTrunc_le
#print axioms Lean4LPD.PauliString.pauliLadderTrunc
#print axioms Lean4LPD.PauliString.pauliWeightedLadderTrunc
#print axioms Lean4LPD.PauliString.coeff_ext
#print axioms Lean4LPD.PauliString.sub_truncOp
#print axioms Lean4LPD.PauliString.pauliNorm_sub_truncOp_highSet_compl
#print axioms Lean4LPD.PauliString.trotterSchedule_interior
#print axioms Lean4LPD.PauliString.trotterSchedule_boundary
#print axioms Lean4LPD.PauliString.trotterTraj_within_step
#print axioms Lean4LPD.PauliString.trotterTraj_at_boundary
#print axioms Lean4LPD.PauliString.discardedStep_eq_truncOp
#print axioms Lean4LPD.PauliString.pauliNorm_discardedStep
#print axioms Lean4LPD.PauliString.discardedStep_eq_boundary_sub
#print axioms Lean4LPD.PauliString.pauliNorm_discardedStep_eq_boundary_highNorm
#print axioms Lean4LPD.PauliString.pauliNorm_discardedStep_le
#print axioms Lean4LPD.DiscardWitness.interior_highNorm
#print axioms Lean4LPD.DiscardWitness.boundary_eq_zero
#print axioms Lean4LPD.DiscardWitness.discardedStep_ne_zero
#print axioms Lean4LPD.DiscardWitness.discardedStep_pauliNorm
#print axioms Lean4LPD.PauliString.sympForm_eq_zero_of_disjoint_support
#print axioms Lean4LPD.PauliString.layer_weight_le
#print axioms Lean4LPD.PauliString.reachable_weight_le
#print axioms Lean4LPD.LayerWitness.isLayer_L₁
#print axioms Lean4LPD.LayerWitness.isLayer_L₂
#print axioms Lean4LPD.LayerWitness.isSelfAdjoint_L₁
#print axioms Lean4LPD.LayerWitness.isSelfAdjoint_L₂
#print axioms Lean4LPD.LayerWitness.gamma_layers_weight_le
#print axioms Lean4LPD.LayerWitness.gamma_layers_weight_four
#print axioms Lean4LPD.LayerWitness.gamma_weight_bound_false
#print axioms Lean4LPD.LayerWitness.gamma_weight_bound_false_unmerged
#print axioms Lean4LPD.l2_opNorm_submatrix_le
#print axioms Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_unitary
#print axioms Lean4LPD.l2_opNorm_toBlock_le_one_of_mem_orthogonalGroup
#print axioms Lean4LPD.rot_mul_rot

-- Norm-level error chain for whole layers, and the representation bridges.
#print axioms Lean4LPD.schur_mulVec_le
#print axioms Lean4LPD.l2_opNorm_le_schur
#print axioms Lean4LPD.exp_smul_I_of_involution
#print axioms Lean4LPD.rot_eq_exp
#print axioms Lean4LPD.exp_conj_of_anticommute
#print axioms Lean4LPD.PauliString.rot_toMatrix_eq_exp
#print axioms Lean4LPD.PauliString.toMatrix_eq_phase_tensor
#print axioms Lean4LPD.PauliString.toMatrix_tensorRepresentative
#print axioms Lean4LPD.PauliString.isSelfAdjoint_tensorRepresentative
#print axioms Lean4LPD.PauliString.trace_tensorPauli_mul
#print axioms Lean4LPD.PauliString.bitsMatrixEquiv
#print axioms Lean4LPD.PauliString.bitsMatrixEquiv_star
#print axioms Lean4LPD.PauliString.trotterStep_telescoping
#print axioms Lean4LPD.PauliString.periodic_traj_sub_trotterStepTraj
#print axioms Lean4LPD.PauliString.pauliNorm_trotterTraj_error_le
#print axioms Lean4LPD.PauliString.coeffVec_layerConj
#print axioms Lean4LPD.PauliString.layerAct_eq_sum_layerJump
#print axioms Lean4LPD.PauliString.row_sum_norm_layerJumpMatrix_le
#print axioms Lean4LPD.PauliString.col_sum_norm_layerJumpMatrix_le
#print axioms Lean4LPD.PauliString.norm_layerInflowMatrix_le
#print axioms Lean4LPD.PauliString.norm_layerInflowMatrix_le_factorial
#print axioms Lean4LPD.PauliString.norm_layerInflowMatrix_clm_le_restr
#print axioms Lean4LPD.summable_epsJump_tail
#print axioms Lean4LPD.sum_Ico_epsJump_le_entryFactor
#print axioms Lean4LPD.PauliString.highNorm_layerConj_le_multi
#print axioms Lean4LPD.PauliString.pauliMultiLadder
#print axioms Lean4LPD.PauliString.layerN_le_majorant
#print axioms Lean4LPD.MultiLadder.sum_block_inflow_le
#print axioms Lean4LPD.chain_le_weighted_choose
#print axioms Lean4LPD.epsJump_mul_chainWeight_eq_partFactor
#print axioms Lean4LPD.chain_epsJump_le_weighted_choose_source
#print axioms Lean4LPD.prod_add_one_le_factorial_exp_rpow
#print axioms Lean4LPD.prod_shifted_le_factorial_exp_rpow
#print axioms Lean4LPD.slot_polynomial_le_exp
#print axioms Lean4LPD.cZero_pow_nat
#print axioms Lean4LPD.MultiLadder.sum_block_epsJump_le_cZero
#print axioms Lean4LPD.PauliString.sum_pauliNorm_discardedLayerStep_le_chain
#print axioms Lean4LPD.PauliString.pauliNorm_layerStep_error_le_model
#print axioms Lean4LPD.PauliString.pauliNorm_layerStep_error_le_model_of_source_regime
#print axioms Lean4LPD.norm_majorant_tendsto_zero
#print axioms Lean4LPD.exists_model_norm_threshold
#print axioms Lean4LPD.exists_uniform_weight_cutoff
#print axioms Lean4LPD.exists_admissible_step_count
#print axioms Lean4LPD.LayerCounterexample.pf2Output_eq_four_layers
#print axioms Lean4LPD.LayerCounterexample.pf2_coeff_sines
#print axioms Lean4LPD.LayerCounterexample.actual_discard_exceeds_gamma_bound
#print axioms Lean4LPD.PauliString.card_lowSet_le
#print axioms Lean4LPD.PauliString.card_lowSet_le_pow
