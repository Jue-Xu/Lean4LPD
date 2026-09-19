# Lean4LPD

[![Lean Action CI](https://github.com/Jue-Xu/Lean4LPD/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Jue-Xu/Lean4LPD/actions/workflows/lean_action_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 / Mathlib formalization of the core of **low-weight Pauli dynamics (LPD)**, the
classical algorithm for Hamiltonian dynamics of

> Jue Xu, Chu Zhao, Xiangran Zhang, Shuchen Zhu, Qi Zhao,
> *Classical Simulation of Noiseless Quantum Dynamics without Randomness*, [arXiv:2601.15770](https://arxiv.org/abs/2601.15770).

LPD evolves an observable in the Heisenberg picture under a Trotterized evolution and discards,
at the end of every Trotter step, all Pauli strings of weight above a threshold $w^\ast$.
This repository machine-checks the two operator-level pillars of its analysis. Both are statements
about operators in the normalized Pauli 2-norm; the passage to expectation values in a state, which is
where the entanglement of the input enters, and the Trotter error are outside it
(see [Not formalized](#not-formalized)):

1. **The damped norm flow (Pauli truncation error).** Every Pauli rotation moves norm to higher
   weight only with amplitude $|\sin \delta t|$. Formalized end to end, this gives the bound on
   the total operator that LPD discards,

$$\bigl\lVert\, \widetilde U^{\dagger r} O\, \widetilde U^{r} \;-\; \mathrm{LPD}_r(O) \,\bigr\rVert_{\bar 2}
\;\le\; \Bigl(\frac{t}{t_0}\Bigr)^{m^\ast+1} \bigl(e\,(m^\ast+1)\bigr)^{k_o/(k_h-1)}\, \lVert O\rVert_{\bar 2},
\qquad t_0 = \frac{1}{2\,\Gamma\,(k_h-1)\,\alpha},$$

   where $\lVert\cdot\rVert_{\bar 2}$ is the normalized Pauli 2-norm, $w^\ast = k_o + m^\ast (k_h-1)$,
   one Trotter step consists of $\Gamma$ layers of $k_h$-local Pauli rotations with pairwise disjoint
   supports, the observable is $k_o$-local, and every conjugation angle satisfies
   $\lvert\sin\theta\rvert \le \alpha t/r$. (In the paper $\Gamma$ counts the disjoint-support groups of the
   Hamiltonian, which is the number of layers of a first-order step; a $p$-th order step has
   $\Upsilon\Gamma$ layers, $\Upsilon = 2\cdot 5^{p/2-1}$, and $\Gamma$ above is to be read as $\Upsilon\Gamma$.)

2. **The weight-growth and counting steps of the light-cone lemma** (its branch count and its conclusion are not formalized). One layer of disjoint-support $k_h$-local rotations multiplies the
   Pauli weight by at most $k_h$, so $L$ layers give at most $k_h^{L}$; and the number of Pauli
   strings of weight at most $w$ on $n$ qubits is at most $4^w n^w$. Together these are what makes
   the truncated evolution cost $n^{O(w^\ast)}$.

The statements, in the notation of the paper and keyed by the labels of its supplementary material, are
collected in [`STATEMENTS.md`](STATEMENTS.md) together with the Lean declaration that proves each of them.
`STATEMENTS.md` writes every statement out in full: it follows the current version of the supplementary
material, which organizes the truncation analysis differently from the first arXiv version.

## Status

**0 `sorry`, 0 project axioms.** `#print axioms` on every headline theorem reports only Lean's
standard axioms `[propext, Classical.choice, Quot.sound]`; [`Lean4LPD/Audit.lean`](Lean4LPD/Audit.lean)
prints the report for 156 declarations and CI fails if anything else appears
(see [Trust base](#trust-base)).

Toolchain: `leanprover/lean4:v4.34.0-rc2`, Mathlib `v4.34.0-rc2`.

### Main results

#### Damped norm flow

| Declaration | Statement | Paper label |
|---|---|---|
| `PauliString.local_flow_k_local` | $\mathcal N^{(g)}_{\ge m} \le \mathcal N^{(g-1)}_{\ge m} + \lvert\sin\delta t\rvert\, \mathcal N^{(g-1)}_{\ge m-1}$ for one $k_h$-local Pauli rotation and $m\ge2$ (rung $1$: `PauliString.highNorm_conj_le_pauliNorm`) | `apd:thm:local_flow_k_local` |
| `PauliString.norm_layerInflowMatrix_le_factorial` | the $j$-jump inflow block of one disjoint-support layer has operator norm $\le (w_{m+j}\,\sigma)^j/j!$, $\sigma=\max_l\lvert\sin\delta t_l\rvert$ (Schur test) | `apd:thm:layer_inflow` |
| `Ladder.cumulation`, `layer_cumulation` | $\mathcal N^{(g)}_{\ge m}\le\binom{g}{m}\sin^m(\delta t)\,\lVert O\rVert_{\bar 2}$, and its per-layer form with $\prod_j w_j$ (for sequences obeying the single-jump layer recursion; Pauli layers are covered by the next two rows) | `apd:cor:norm_cumulation_jump` |
| `PauliString.highNorm_layerConj_le_multi`, `PauliString.pauliMultiLadder` | one layer with all jump lengths: $\mathcal N^{(T)}_{\ge m} \le \mathcal N^{(T-1)}_{\ge m} + \sum_{1\le j \lt m}\varepsilon_j^{(m)}\mathcal N^{(T-1)}_{\ge m-j} + E_m \lVert O\rVert_{\bar 2}$ | `apd:eq:multijump_recursion` (`apd:thm:first_passage`) |
| `MultiLadder.le_majorant` | the first-passage majorant of the multi-jump recursion | `apd:eq:composition_majorant` |
| `entryFactor_le`, `partFactor_le` | $E_\nu \le \varepsilon_\nu^{(\nu)}(1+2\beta)$ for $\beta\le1/2$; a part of size $j\ge2$ ending at $\sigma\ge j$ costs at most $(9/4)^{j-1}$ | `apd:eq:entry_bound`, `apd:eq:part_factor` |
| `cZero_le_two` | $c_0 = \frac{r+1}{r}\,e^{\frac94\frac{m^\ast+1}{r\Gamma}}(1+B)^{\frac1{m^\ast+1}} \le 2$ for $m^\ast\ge1$, $r\ge5$, $8(m^\ast+1)^2\le r\Gamma$, $0\le B\le1$ | `apd:eq:c0` |
| `two_lt_cZero_of_admissible`, `…_four`, `…_of_m_zero`, `…_of_m_two` | neither $m^\ast\ge1$ nor $r\ge5$ can be dropped: explicit points that satisfy every other hypothesis and have $c_0>2$ | — |
| `PauliString.pauliNorm_trotterTraj_error_le` | telescoping: $\lVert \widetilde O^{(r)} - \mathrm{LPD}_r(O)\rVert_{\bar 2} \le \sum_{d} \lVert X_d\rVert_{\bar 2}$, $X_d$ the operator discarded at step $d$ | `apd:eq:step_component`, `apd:thm:triangle` (norm level) |
| **`PauliString.pauliNorm_layerStep_error_le_model_of_source_regime`** | **the displayed bound above** | `apd:thm:one_step_truncation_error` (norm level) |
| `exists_model_norm_threshold` | for $t<t_0$ the right-hand side of the bound above falls below every tolerance at some finite $m^\ast\ge1$ (a statement about the scalar majorant; it is not composed with the main bound, whose $r$ and angles depend on $m^\ast$) | `apd:thm:truncation_threshold_entangled` (existence) |

#### Light cone

| Declaration | Statement | Paper label |
|---|---|---|
| `PauliString.layer_weight_le` | one disjoint-support layer: $\lvert q\rvert \le k_h\,\lvert p\rvert$ for every $q$ in the branching set `oneLayer L p` | `apd:thm:lightcone` (weight growth) |
| `PauliString.reachable_weight_le` | $L$ layers: $\lvert q\rvert \le k_h^{L}\,\lvert p\rvert$ for every $q$ in `reachable Ls p` | `apd:thm:lightcone` (weight growth) |
| `PauliString.card_lowSet_le_pow` | $\#\lbrace P : \lvert P\rvert\le w\rbrace \le 4^w n^w$ for $w\le n$ (strings up to phase) | counting step of `apd:thm:lightcone` / `apd:thm:runtime` |
| `LayerWitness.gamma_layers_weight_four`, `LayerWitness.gamma_weight_bound_false`, `LayerCounterexample.actual_discard_exceeds_gamma_bound` | tightness of $k_h^{L}$: the bound is attained at $L=2$, and $L$ is the number of *layers* of a step, which is $\Upsilon\Gamma$ for a $p$-th order formula over $\Gamma$ disjoint-support groups. A second-order step with $\Gamma=2$ reaches weight $6 > w^\ast k_h^{\Gamma}=4$ with a nonzero coefficient, within the bound $w^\ast k_h^{\Upsilon\Gamma}=16$ | — |

#### The model is the physical one

| Declaration | Statement |
|---|---|
| `rot_eq_exp` | the closed-form rotation $\cos(\theta/2) + i\sin(\theta/2)\,G$ equals the matrix exponential $\exp(i\tfrac{\theta}{2}G)$ |
| `PauliString.toMatrix_eq_phase_tensor` | the matrix of a Pauli string is a phase times the Kronecker product of single-qubit Pauli matrices |
| `PauliString.pauli_rotation_branch` | $e^{i G \delta t/2} P e^{-i G \delta t/2} = \cos(\delta t)\,P + i\sin(\delta t)\,GP$ for anticommuting $G,P$ (`apd:eq:pauli_rotation_branch`) |
| `PauliString.truncOp_univ`, `sum_norm_coeff_sq` | completeness of the Pauli expansion and Parseval for the normalized Pauli 2-norm |

### Hypotheses of the main bound

`pauliNorm_layerStep_error_le_model_of_source_regime` assumes exactly:

* every layer is a list of Hermitian Pauli strings of weight $\le k_h$ with pairwise **disjoint supports**
  (`IsLayer`), $k_h \ge 2$, and a Trotter step is a block of $\Gamma \ge 1$ such layers, repeated $r$ times
  (for a $p$-th order product formula, $\Gamma$ counts all layers of the step);
* every conjugation angle satisfies $\lvert\sin\theta\rvert \le a$ with $0 \le a \le \alpha t/r$, where $\alpha > 0$ and $t \ge 0$ (the layer hypotheses are stated for every index of the family `layers`, of which a step uses the first $\Gamma$);
* the observable has no Pauli component of weight above $k_o$;
* $m^\ast \ge 1$, $r \ge 5$, $r \ge m^\ast$, $8(m^\ast+1)^2 \le r\,\Gamma$ (`Admissible`), and
  $r \ge 8e^2 (k_o+k_h-1)\,\alpha t$.

The statement concerns operators only, so no state appears (the step to expectation values is not
formalized, see below), and there is no assumption on the geometry or on the number of qubits.
The constant $2$ in $t_0$ is the bound $c_0 \le 2$ (`cZero_le_two`), in which $B = 4e\beta$ and
$\beta = 2e\,(k_o+k_h-1)\sin\delta t$ is the expansion parameter of the multi-jump analysis; the last
hypothesis above gives $B \le 1$. The paper's remark that $c_0 \to 1$ as $r\to\infty$ is not formalized.

### Not formalized

This is a formalization of the *norm-level* analysis, not of every statement of the paper:

* the step from the Pauli 2-norm of the discarded operator to an **expectation value** in a given
  state (the average over a state 2-design, or the bound for sufficiently entangled states) is not
  part of this repository;
* the **Trotter error** $\lVert e^{iHt} O e^{-iHt} - \widetilde U^{\dagger r} O \widetilde U^{r}\rVert$ is not formalized;
* of the **runtime** theorem only the counting step is formalized; the branch count
  $\prod_\gamma 2^{w^\ast k_h^{\gamma-1}}$ of `apd:thm:lightcone` is not;
* the weight half of the light-cone lemma is proved for `reachable` (`Pauli/LayerWitness.lean`), a
  combinatorially defined set that follows both branches of every anticommuting rotation and ignores
  angles and cancellations. No theorem of the library relates `reachable` to the coefficients of a
  conjugated operator, so `layer_weight_le` and `reachable_weight_le` bound where coefficients can
  appear; statements about actual coefficients are proved separately (`Pauli/LayerFlow.lean`,
  `Pauli/LayerCounterexample.lean`).

### Trust base

Everything is checked by the Lean kernel from Mathlib; there are no `sorry`s, no added axioms,
and no `native_decide`. *Axiom-free is not assumption-free*: what each theorem assumes is in its
statement, and what a definition means has to be read. The definitions a reader should check are
few: `PauliString` and `toMatrix` (`Pauli/Basic.lean`, `Pauli/Matrix.lean`), `rot`
(`Rotation.lean`), `coeff`, `pauliNorm`, `highNorm` (`Pauli/Coeff.lean`), `truncOp`
(`Pauli/Truncate.lean`), `IsLayer` (`Pauli/LayerWitness.lean`), `layerStepTraj` and
`layerBlockEnd` (`Pauli/LayerError.lean`), `layerConj` (`Pauli/LayerFlow.lean`), `wt`, `herm`, `highSet` (`Pauli/Coeff.lean`), `rungWeight` (`Ladder/Defs.lean`), `Admissible` (`Constants/C0.lean`), `tZeroModel` and `decayBase` (`Constants/Total.lean`). The bridge theorems listed under
"The model is the physical one" tie them to the usual matrices.

## How to check

```bash
git clone https://github.com/Jue-Xu/Lean4LPD && cd Lean4LPD
lake exe cache get        # prebuilt Mathlib
lake build                # builds the library; prints the axiom report of Lean4LPD/Audit.lean
for t in tests/*.lean; do lake env lean "$t"; done      # non-vacuity and necessity witnesses
lake env lean Lean4LPD/Audit.lean > audit.log 2>&1 && python3 scripts/check_axioms.py audit.log
python3 scripts/c0_scan.py   # numerical companion to Constants/C0.lean (no Lean needed)
```

Prerequisites: [elan](https://lean-lang.org/install/), which fetches the pinned toolchain, and `python3` for the two scripts.
Expected output: `lake build` finishes without errors; every test prints only `#print axioms` reports and no `error:` line;
the axiom gate prints `156 declarations audited (0 axiom-free, 156 using only standard axioms)`. `#print axioms` is
transitive, so a `sorry` anywhere below a listed theorem would show up there as `sorryAx`. Declaration names in this file are
relative to the namespace `Lean4LPD`.

The tests instantiate the headline theorems of the truncation-error chain at nondegenerate points (for instance a layer with a
genuine two-rung jump, so that the multi-jump sector is not vacuous) and exhibit a witness for
every hypothesis that is claimed to be necessary.

## Module structure

```
Lean4LPD/
├── Rotation.lean            — closed-form Pauli rotation, unitarity, conjugation rules
├── RotationExp.lean         — rot = matrix exponential
├── BlockNorm.lean, Schur.lean — submatrix norm ≤ norm; the Schur test for the ℓ² operator norm
├── Pauli/
│   ├── Basic.lean           — Pauli strings (binary symplectic form with phase), group law
│   ├── Weight.lean          — support, weight, weight change under multiplication
│   ├── Matrix.lean, Trace.lean, Tensor.lean — matrices, trace orthogonality, Kronecker form
│   ├── Coeff.lean           — Pauli coefficients, Pauli 2-norm, Parseval, high-weight norm
│   ├── Count.lean           — number of Pauli strings of weight ≤ w
│   ├── Branch.lean          — the rotation branch rule
│   ├── Flow.lean            — damped local norm flow; the Pauli ladder
│   ├── Truncate.lean, Discard.lean, TrotterTruncate.lean — truncation, the discarded operator X_d
│   ├── TruncationError.lean — telescoping / triangle bound in Pauli 2-norm
│   ├── LayerWitness.lean    — disjoint-support layers, the light cone, tightness
│   ├── LayerCounterexample.lean — second-order step: a nonzero coefficient at weight 6 (the exponent counts layers)
│   ├── LayerFlow.lean       — layer inflow (Schur test)
│   ├── LayerLadder.lean     — the multi-jump recursion for actual Pauli layers
│   ├── LayerError.lean      — assembly: the truncation-error bound
│   └── DiscardWitness.lean  — a concrete two-qubit non-vacuity witness
├── Ladder/                  — the abstract damped ladder (no quantum content)
│   ├── Defs.lean, Recursion.lean, HockeyStick.lean, Weighted.lean — single-jump cumulation
│   ├── MultiJump.lean       — first-passage majorant
│   └── ChainBound.lean, Assembly.lean — summing the inflow over Trotter steps
├── Constants/
│   ├── Entry.lean, PartFactor.lean, ChainWeights.lean — entry and part factors
│   ├── StepSum.lean         — Σ_d C(dΓ, K) ≤ ((r+1)Γ)^{K+1}/(Γ (K+1)!)
│   ├── C0.lean              — c₀ ≤ 2 and the necessity of its hypotheses
│   ├── Total.lean, AssemblyBound.lean — the threshold t₀ and the total bound
│   └── Threshold.lean       — existence of the truncation rung for a target error
└── Audit.lean               — #print axioms for every headline theorem
tests/                       — non-vacuity and necessity witnesses (run by CI)
scripts/                     — check_axioms.py (CI gate), c0_scan.py (numerics for C0.lean)
```

## Citation

If you use this formalization, please cite the paper above and this repository.

## License

Apache 2.0, see [LICENSE](LICENSE).
