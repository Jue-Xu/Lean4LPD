import Lean4LPD.Pauli.LayerCounterexample
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Tests for the second-order layer-count witness

Regression and non-vacuity checks for `Lean4LPD.Pauli.LayerCounterexample`, which shows that
the exponent `ΥΓ` of the light-cone weight bound `w* k_h^{ΥΓ}` (`apd:thm:lightcone`) cannot be
replaced by `Γ`: after one second-order step on an 8-qubit brickwork, the operator discarded at
`w* = 1` (`apd:eq:step_component`) has a nonzero coefficient at the weight-six Pauli `P₆`.

* The first example records the parameters: two disjoint-support two-local layers, a weight-one
  input, and a witness of weight six.
* `small_angle_admissible`, `small_angle_output_nonzero`, `small_angle_discard_nonzero`: at the
  concrete small angle `θ = 1/100` the coefficient is nonzero, before and after truncation.
* `gamma_weight_bound_fails`: at that angle, weight `w* k_h^Γ = 4` does not bound the Pauli classes
  of the discarded operator.
* The remaining examples are non-vacuity checks: the coefficient vanishes at `θ = 0` and at the
  Clifford angle `θ = π/2`, so the hypotheses `0 < θ` and `2 * θ < π` of `pf2_coeff_ne_zero`
  matter; the closed form is evaluated at a rational point; and the sign relating `P₆` to its
  canonical representative is checked.
-/

namespace Lean4LPD.LayerCounterexampleRegression

open LayerCounterexample LayerWitness PauliString

/-- The eight-qubit circuit has two disjoint-support two-local brickwork layers and a
weight-one input, and the witness `P₆` has weight six. -/
example : IsLayer 2 L₁ ∧ IsLayer 2 L₂ ∧ weight (Z (3 : Fin 8)) = 1 ∧ weight P₆ = 6 :=
  ⟨isLayer_L₁, isLayer_L₂, weight_Z_three, weight_P₆⟩

/-- The concrete small angle `θ = 1/100` lies in the interval `0 < θ`, `2 * θ < π` on which the
coefficient is nonzero. The proof uses only `2 ≤ π`; no floating-point evaluation of a sine is
involved. -/
theorem small_angle_admissible : (0 : ℝ) < 1 / 100 ∧ 2 * (1 / 100 : ℝ) < Real.pi := by
  constructor
  · norm_num
  · have hpi := Real.two_le_pi
    linarith

/-- The output of the literal second-order word has a nonzero coefficient at the weight-six
class `cls P₆` at angle `1/100`: an actual coefficient, not merely a reachable class. -/
theorem small_angle_output_nonzero : coeff (pf2Output (1 / 100)) (cls P₆) ≠ 0 :=
  pf2_coeff_ne_zero small_angle_admissible.1 small_angle_admissible.2

/-- The same coefficient survives in the operator discarded at cutoff one
(`apd:eq:step_component`). -/
theorem small_angle_discard_nonzero : coeff (pf2Discard (1 / 100)) (cls P₆) ≠ 0 := by
  rw [pf2Discard_coeff]
  exact small_angle_output_nonzero

/-- **Weight `w* k_h^Γ = 4` does not bound the discarded operator.** At `θ = 1/100` it is not
the case that every Pauli class with a nonzero coefficient in `pf2Discard θ` has weight at most
`4`. The bound with the layer count in the exponent, `w* k_h^{ΥΓ} = 16` for this step
(`apd:thm:lightcone`), is not affected by this test. -/
theorem gamma_weight_bound_fails :
    ¬ ∀ p : PauliIndex 8, coeff (pf2Discard (1 / 100)) p ≠ 0 → wt p ≤ 4 := by
  intro h
  have hbad := h (cls P₆) small_angle_discard_nonzero
  simp [weight_P₆] at hbad

/-- At angle zero the coefficient vanishes. Non-vacuity check for the hypothesis `0 < θ`:
reachability, which ignores the angle, must not be read as a nonzero amplitude. -/
example : coeff (pf2Output 0) (cls P₆) = 0 := by
  rw [pf2_coeff_sines]
  norm_num

/-- At the Clifford angle `θ = π/2` this particular coefficient also vanishes, since
`cos θ = 0`. Non-vacuity check for the hypothesis `2 * θ < π`; the witness deliberately uses a
small non-Clifford angle. -/
example : coeff (pf2Output (Real.pi / 2)) (cls P₆) = 0 := by
  rw [pf2_coeff_polynomial, Real.cos_pi_div_two]
  norm_num

/-- An exact rational check of the proved polynomial: at `cos θ = 4/5`, `sin θ = 3/5` the
coefficient is `-4 (4/5)^2 (3/5)^5 = -15552/78125`. These cosine and sine values are hypotheses
of this example only, not of the small-angle witness or of the general formula. -/
example (θ : ℝ) (hc : Real.cos θ = 4 / 5) (hs : Real.sin θ = 3 / 5) :
    coeff (pf2Output θ) (cls P₆) = -(15552 / 78125 : ℂ) := by
  rw [pf2_coeff_polynomial, hc, hs]
  norm_num

/-- The named positive tensor `P₆` (phase `3`) and the canonical representative
`herm (cls P₆)` (phase `1`) differ by the definite sign `i^2 = -1`, not by an arbitrary
convention. -/
example : (herm (cls P₆)).phase = 1 ∧ P₆.phase = 3 := by decide

#print axioms pf2_coeff_polynomial
#print axioms pf2Output_eq_four_layers
#print axioms pf2_coeff_sines
#print axioms pf2_named_P6_component
#print axioms pf2Discard_coeff
#print axioms actual_discard_exceeds_gamma_bound
#print axioms small_angle_discard_nonzero
#print axioms gamma_weight_bound_fails

end Lean4LPD.LayerCounterexampleRegression
