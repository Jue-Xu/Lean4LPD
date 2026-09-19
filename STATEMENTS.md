# Statements: paper labels and Lean declarations

The docstrings of this library cite statements of

Jue Xu, Chu Zhao, Xiangran Zhang, Shuchen Zhu, Qi Zhao,
*Classical Simulation of Noiseless Quantum Dynamics without Randomness*, [arXiv:2601.15770](https://arxiv.org/abs/2601.15770)

by their LaTeX labels, for example `apd:thm:local_flow_k_local` (labels beginning with `apd:` belong to the
supplementary material). The labels and statements are those of the current version of the paper's supplementary
material. The first arXiv version organizes the truncation analysis differently and does not contain all of the statements
below (for instance the layer-inflow and multi-jump lemmas); this file therefore states every result in full, and the
[index](#index-of-labels) lists every label. For every statement in the chain it gives

1. the mathematical statement, written out in the notation of the paper, so that this file can be read on its own;
2. the Lean declarations that prove it, and the module that contains them;
3. the relation between the Lean statement and the paper's statement, which is one of
   * **faithful**: same hypotheses and same conclusion, up to the dictionary below;
   * **stronger**: Lean proves more (fewer hypotheses, a better constant, or a more general object), and the difference is stated;
   * **weaker**: Lean proves less, and the difference is stated (typically a bound in the normalized Pauli 2-norm
     where the paper bounds an expectation value, or existence where the paper gives a rate);
   * **not formalized**.

Everything formalized here is a statement about operators in the normalized Pauli 2-norm. No statement about a
quantum state, an expectation value or the Trotter error is formalized; the [last section](#13-what-is-not-formalized)
lists what is outside the library. The column *Module* names a Lean module: `Pauli.Flow` is the file
`Lean4LPD/Pauli/Flow.lean`. Declaration names are relative to the root namespace `Lean4LPD`.

## Notation

* **Pauli strings.** There are $n$ qubits. A Pauli string is $P \in \lbrace I,X,Y,Z\rbrace^{\otimes n}$, its support
  $\mathrm{supp}(P)$ is the set of qubits carrying a non-identity factor, and its weight is $\lvert P\rvert = \lvert\mathrm{supp}(P)\rvert$.
* **Expansion and norm.** Every operator is $O=\sum_P x_P P$ with $x_P = 2^{-n}\mathrm{Tr}(PO)$. The normalized Pauli 2-norm is
  $\lVert O\rVert_{\bar 2} = \bigl(2^{-n}\mathrm{Tr}\,O^\dagger O\bigr)^{1/2} = \bigl(\sum_P \lvert x_P\rvert^2\bigr)^{1/2}$,
  the $\ell_2$ norm of the Pauli coefficients, so every Pauli string has norm one. $O_{\ge w}$ is the part of the expansion on
  strings of weight at least $w$. An observable is $k_o$-local if $x_P = 0$ whenever $\lvert P\rvert > k_o$.
* **Half-angle convention.** A gate is $e^{-iG\delta t/2}$ with $G$ a Hermitian Pauli string. In the Heisenberg picture it
  acts by $P \mapsto e^{iG\delta t/2} P e^{-iG\delta t/2}$ and rotates an anticommuting $P$ by the *conjugation angle* $\delta t$.
  A Hamiltonian term $\alpha_l G_l$ evolved for a time $\tau$ has conjugation angle $2\alpha_l\tau$; with
  $\alpha := 2\max_l\lvert\alpha_l\rvert$ and substeps of duration $\tau \le t/r$ this gives $\sin\delta t \le \alpha t/r$.
* **Layers.** The Hamiltonian is $k_h$-local, $k_h \ge 2$, and its terms are grouped into $\Gamma$ layers; within a layer the
  generators have pairwise disjoint supports (so they commute). One step of a $p$-th order product formula consists of
  $\Upsilon\Gamma$ layers, with $\Upsilon = 2\cdot 5^{p/2-1}$ for even $p$ and $\Upsilon = 1$ for the first-order formula.
* **Rungs.** $w_m = k_o + (m-1)(k_h-1)$ for $m \ge 1$ is the largest weight reachable from weight $k_o$ with $m-1$ anticommuting
  $k_h$-local rotations. With $c = k_o/(k_h-1)$ one has $w_m = (k_h-1)(m-1+c)$; in particular $w_2 = k_o+k_h-1$. The expansion
  parameter of the multi-jump analysis is $\beta = 2e\,w_2\sin\delta t$.
* **High-weight norm.** $\mathcal N^{(g)}_{\ge m} = \lVert O^{(g)}_{\ge w_m+1}\rVert_{\bar 2}$, the norm of the part of the evolved
  observable strictly above rung $m$, after $g$ rotations (or $T$ layers). For $\nu \le 0$ one sets
  $\mathcal N_{\ge \nu} := \lVert O\rVert_{\bar 2}$ (the reservoir below the first rung).
* **LPD.** With $\widetilde U$ one Trotter step and $\Pi_{\le w}$ the projection onto Pauli weights at most $w$, the LPD
  trajectory is $\tilde O^{(0)}_{\le w^\ast} = O$,
  $\tilde O^{(d)}_{\le w^\ast} = \Pi_{\le w^\ast}\bigl(\widetilde U^\dagger\, \tilde O^{(d-1)}_{\le w^\ast}\, \widetilde U\bigr)$,
  and $\mathrm{LPD}_r(O) = \tilde O^{(r)}_{\le w^\ast}$. The threshold is parameterized as
  $w^\ast = k_o + m^\ast(k_h-1) = w_{m^\ast+1}$. The operator discarded at the end of step $d$ is $X_d$ (Section 9).

### Dictionary

| Paper | Lean |
|---|---|
| $\lVert O\rVert_{\bar 2}$ | `PauliString.pauliNorm O`, for `O : Matrix (Bits n) (Bits n) ℂ` |
| $x_P$ | `PauliString.coeff O p`, where `p : PauliIndex n` is a Pauli string up to phase and `PauliString.herm p` its Hermitian representative |
| $\lVert O_{\ge w+1}\rVert_{\bar 2}$ | `PauliString.highNorm w O` |
| $w_m$, $m \ge 1$ | `rungWeight ko kh m` (natural number; truncated subtraction gives `rungWeight ko kh 0 = ko`, which is not $w_0$), `rungW (kh-1) c m` (real) |
| $e^{iG\theta/2}\, O\, e^{-iG\theta/2}$ | `rot (toMatrix G) θ * O * rot (toMatrix G) (-θ)`; the argument of `rot` is the conjugation angle |
| conjugation by one layer | `PauliString.layerConj L O`, with `L : List (PauliString n × ℝ)` a list of (generator, conjugation angle) |
| layer hypothesis | `PauliString.IsLayer kh L`: pairwise disjoint supports and weight at most `kh` |
| $\varepsilon^{(m)}_j$, $E_m$, $\beta$ | `epsJump`, `entryFactor`, `betaOf`, applied to `(kh-1) (ko/(kh-1)) a`, where `a` bounds the absolute sines |
| $\Pi_{\le w}$ | `PauliString.truncOp (highSet n w)ᶜ` |
| $\tilde O^{(d)}_{\le w^\ast}$, $\widetilde U^{\dagger r} O\, \widetilde U^{r}$ | `PauliString.layerStepTraj layers Γ wstar O d`, `((PauliString.layerBlockEnd layers Γ) ^ r) O` |
| $X_{d+1}$ | `PauliString.discardedLayerStep layers Γ wstar O d` (Lean counts steps from zero) |
| $c_0$, $t_0$ | `cZero r m Γ B` with `B` standing for $4e\beta$; `tZero`, `tZeroModel` |
| $m^\ast$, $w^\ast$ | `m` and `rungWeight ko kh (m + 1)` in the theorems of Section 10 |

In the Lean theorems about Trotter steps, `Γ` is the number of layers in one step. For a $p$-th order formula it is to be
instantiated with $\Upsilon\Gamma$ in the notation above, which is also how the paper's theorem treats higher orders.
In declaration names, `source` refers to the paper: a `…_source` lemma is stated with the paper's constant, and
`…_of_source_regime` assumes the paper's step-count conditions.

## 1. Definitions and the model

**Pauli basis (`def:pauli_basis`).** The normalized Pauli basis is $\lbrace 2^{-n/2}P\rbrace$ with
$\mathrm{Tr}(s s') = \delta_{s,s'}$ for its elements, and every operator has a unique expansion in it.

**Norm (`def:norm`).** $\lVert A\rVert_{\bar 2} := 2^{-n/2}\sqrt{\mathrm{Tr}(AA^\dagger)}$, which equals the Pauli 2-norm
$(\sum_P\lvert x_P\rvert^2)^{1/2}$.

**Support and weight (`def:support`, `def:pauli_weight`).** $\mathrm{supp}(O) = \bigcup_{P : x_P \ne 0}\mathrm{supp}(P)$, and
$\lvert P\rvert = \lvert\mathrm{supp}(P)\rvert$.

**High-weight norm (`apd:eq:def_high_weight_norm`).**

$$\mathcal N^{(g)}_{\ge m} := \bigl\lVert O^{(g)}_{\ge w_m+1}\bigr\rVert_{\bar 2}
= \Bigl(\sum_{w > w_m} \bigl\lVert O^{(g)}_{=w}\bigr\rVert_{\bar 2}^{2}\Bigr)^{1/2},
\qquad w_m = k_o + (m-1)(k_h-1).$$

**Product formula (`apd:eq:suzuki`).** $S_p(t) = S_{p-2}(u_p t)^2\, S_{p-2}((1-4u_p)t)\, S_{p-2}(u_p t)^2$ with
$u_p = 1/(4-4^{1/(p-1)})$ and
$S_2(t) = \prod_{\gamma=1}^{\Gamma} e^{-iH_\gamma t/2}\prod_{\gamma=\Gamma}^{1} e^{-iH_\gamma t/2}$; a step of $S_p$ has
$\Upsilon\Gamma$ layers.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `def:pauli_basis` | `PauliString`, `PauliString.toMatrix`, `PauliString.toMatrix_mul`, `PauliString.toMatrix_eq_phase_tensor`, `PauliIndex`, `PauliString.herm`, `PauliString.coeff`, `PauliString.coeff_toMatrix_herm`, `PauliString.truncOp_univ`, `PauliString.sum_coeff_smul_toMatrix_herm` | `Pauli.Basic`, `Pauli.Matrix`, `Pauli.Tensor`, `Pauli.Coeff`, `Pauli.Truncate` | faithful |
| `def:norm` | `PauliString.pauliNormSq`, `PauliString.pauliNorm`, `PauliString.pauliNormSq_eq_trace`, `PauliString.sum_norm_coeff_sq`, `PauliString.norm_coeffVec` | `Pauli.Coeff` | faithful |
| `def:support`, `def:pauli_weight` | `PauliString.support`, `PauliString.weight`, `PauliString.wt` | `Pauli.Weight`, `Pauli.Coeff` | faithful for Pauli strings |
| `apd:eq:def_high_weight_norm` | `PauliString.highSet`, `PauliString.highNorm`, `PauliString.pauliNorm_truncOp_highSet`, `rungWeight`, `rungW`, `PauliString.rungWeight_cast_eq_rungW` | `Pauli.Coeff`, `Pauli.Discard`, `Ladder.Defs`, `Constants.Entry`, `Pauli.LayerLadder` | faithful |
| `apd:eq:suzuki` | none | | not formalized |

**Relation.** A Pauli string is the triple $(x,z,k)$ standing for $i^{k}X^{x}Z^{z}$, and `toMatrix` is the corresponding monomial
matrix. Three bridge theorems tie this model to the usual matrices: `PauliString.toMatrix_mul` (the group law is matrix
multiplication), `PauliString.toMatrix_eq_phase_tensor` (the matrix is a phase times the Kronecker product of single-qubit
Pauli matrices) and `rot_eq_exp` (Section 2). Lean works with the unnormalized Hermitian representatives and the
$2^{-n}$-normalized trace pairing, which is the same as the paper's normalized basis. Both halves of the basis property are
proved: orthonormality, as `coeff_toMatrix_herm` (the coefficient of $P_q$ at $p$ is $\delta_{pq}$), and completeness, as
`truncOp_univ` and `sum_coeff_smul_toMatrix_herm` ($O = \sum_P x_P P$). Parseval is `sum_norm_coeff_sq`, and
`pauliNormSq_eq_trace` is the trace formula. The support of a general operator is not defined in Lean; locality of the
observable enters every theorem as the coefficient condition `∀ p, ko < wt p → coeff O p = 0`, which only asks that every
string of $O$ has weight at most $k_o$ and therefore also covers sums of many $k_o$-local terms. The observable is an arbitrary complex
matrix: Hermiticity of $O$ is never assumed. The product formula is not formalized: the list of layers of a step, and hence the
number of layers per step, is an input of the Lean theorems.

## 2. Rotation branch rule

**Statement (`apd:eq:pauli_rotation_branch`).** For Pauli strings $G$ (Hermitian) and $P$,

$$e^{iG\delta t/2}\, P\, e^{-iG\delta t/2} =
\begin{cases} P, & [G,P] = 0,\\ \cos(\delta t)\,P + i\sin(\delta t)\,GP, & \lbrace G,P\rbrace = 0.\end{cases}$$

If $\lvert G\rvert \le k_h$, the new string $GP$ differs in weight from $P$ by at most $k_h-1$.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:eq:pauli_rotation_branch` | `rot`, `rot_conj_of_commute`, `rot_conj_of_anticommute`, `rot_eq_exp`, `PauliString.pauli_rotation_branch`, `PauliString.pauli_rotation_branch_anticommute_hermitian`, `PauliString.pauli_rotation_branch_anticommute_bounds`, `PauliString.commute_or_anticommute` | `Rotation`, `RotationExp`, `Pauli.Branch`, `Pauli.Basic` | stronger |

**Relation.** `rot G θ` is the closed form $\cos(\theta/2) + i\sin(\theta/2)\,G$, and `rot_eq_exp` proves that it equals
$\exp(i\tfrac{\theta}{2}G)$ whenever $G^2 = 1$, so the exponential form is a theorem and not part of the model. The two
conjugation rules hold in any complex algebra for an involution $G$; `pauli_rotation_branch` specializes them to Pauli strings,
where the case distinction is exhaustive because two Pauli strings either commute or anticommute (`commute_or_anticommute`).
Stronger than the paper's statement in generality (any complex algebra, any real angle) and in that `pauli_rotation_branch_anticommute_bounds` proves, together with the weight bound
$\lvert P\rvert-(k_h-1) \le \lvert GP\rvert \le \lvert P\rvert+(k_h-1)$ and that $GP$ is not a scalar multiple of $P$. On coefficient
vectors the rule is `PauliString.coeff_conj` and `PauliString.coeffVec_conj`, and `PauliString.norm_rotAct` shows that this action
preserves the $\ell_2$ norm (module `Pauli.Flow`).

## 3. Damped local norm flow

**Statement (`apd:thm:local_flow_k_local`, `apd:eq:worst_local_flow_k_local`).** Let $O$ be $k_o$-local, let
$U_g = \prod_{l=1}^{g} e^{-iG_l\delta t/2}$ with $\lvert G_l\rvert \le k_h$, and $O^{(g)} = U_g^\dagger O U_g$. Then

$$\mathcal N^{(g)}_{\ge m} \le \mathcal N^{(g-1)}_{\ge m} + \sin(\delta t)\, \mathcal N^{(g-1)}_{\ge m-1}.$$

Truncating Pauli coefficients can only decrease every $\mathcal N_{\ge m}$.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:thm:local_flow_k_local`, `apd:eq:worst_local_flow_k_local` | `PauliString.local_flow_k_local`, `PauliString.highNorm_conj_le_highNorm`, `PauliString.highNorm_conj_le_pauliNorm`, `PauliString.highNorm_conj_le` | `Pauli.Flow` | stronger |
| truncation decreases the high-weight norms | `PauliString.highNorm_truncOp_le`, `PauliString.pauliNorm_truncOp_le` | `Pauli.Truncate` | faithful |

**Relation.** `local_flow_k_local` is the displayed inequality for one rotation and $m \ge 2$, for an arbitrary matrix $O$ (the
locality of $O$ is not used by this step) and with $\lvert\sin\theta\rvert$ in place of $\sin\delta t$, so no sign or range
condition on the angle is needed and every rotation may have its own angle. Its general form `highNorm_conj_le_highNorm` holds
for any two thresholds with $w' + (k_h-1) \le w$. The first rung is covered by the same two theorems: if $k_o \ge k_h-1$ take
$w' = w_0 = k_o-(k_h-1)$, and otherwise every string lies above $w_0$, so $\mathcal N_{\ge 0}$ is the full norm and the statement is
`highNorm_conj_le_pauliNorm`. The ladder structures of Section 5 use the full norm at rung zero, which is all that the
cumulation needs. The inflow block is bounded in `PauliString.norm_restr_high_rotAct_low`: each high-weight string has at most
one partner, of weight at least $\lvert s\rvert-(k_h-1)$, and the transition amplitude is $\lvert\sin\theta\rvert$.

## 4. Layer inflow

**Statement (`apd:thm:layer_inflow`, `apd:eq:layer_inflow`).** Let $V_\gamma$ be one layer of rotations whose generators have
pairwise disjoint supports and weight at most $k_h$, each with conjugation angle at most $\delta t \le \pi/2$, and let $A$ be
its orthogonal action on Pauli coefficient vectors. Split the strings into $R = \lbrace s : \lvert s\rvert > w_m\rbrace$ and
$B = R^c$, and write $A_{RB} = \sum_{j\ge1}A^{(j)}$, where $A^{(j)}$ collects the branches in which exactly $j$ rotations of the
layer act nontrivially (raising the weight by at most $j(k_h-1)$, that is, $j$ rungs). Then, in the $\ell_2$ operator norm,

$$\bigl\lVert A^{(j)}\bigr\rVert \le \binom{w_{m+j}}{j}\sin^j(\delta t) \le \frac{\bigl(w_{m+j}\sin\delta t\bigr)^j}{j!}.$$

**Necessity of disjoint supports (`apd:rmk:disjoint`).** For the commuting star layer $\lbrace X_1X_j\rbrace_{j=2}^{L+1}$ the
weight-one string $Z_1$ anticommutes with all $L$ generators and reaches weight $L+1$ within one layer, so no bound of the form
above that is independent of the system size holds for layers that are merely commuting.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:thm:layer_inflow`, `apd:eq:layer_inflow` (binomial form) | `PauliString.layerInflowMatrix`, `PauliString.norm_layerInflowMatrix_le`, `PauliString.norm_layerInflowMatrix_le_layerSigma` | `Pauli.LayerFlow` | stronger |
| `apd:eq:layer_inflow` (factorial form) | `PauliString.norm_layerInflowMatrix_le_factorial`, `PauliString.layer_factor_eq_epsJump` | `Pauli.LayerFlow`, `Pauli.LayerLadder` | stronger |
| Schur test, row and column sums | `l2_opNorm_le_schur`, `PauliString.row_sum_norm_layerInflowMatrix_le`, `PauliString.col_sum_norm_layerInflowMatrix_le`, `PauliString.card_antiLayer_le_weight` | `Schur`, `Pauli.LayerFlow` | faithful |
| decomposition $A_{RB} = \sum_j A^{(j)}$ | `PauliString.layerAct_eq_sum_layerJump`, `PauliString.restr_layerAct_low_eq_sum_inflow`, `PauliString.layerInflowMatrix_zero`, `PauliString.norm_restr_layerAct_le_sum_inflow` | `Pauli.LayerFlow` | faithful |
| layer action is conjugation and is orthogonal | `PauliString.coeffVec_layerConj`, `PauliString.norm_layerAct` | `Pauli.LayerFlow` | faithful |
| `apd:rmk:disjoint` | none (the case $L = 2$ is checked as an example in `tests/LayerFlow.lean`) | | not formalized |

**Relation.** `norm_layerInflowMatrix_le` reads
$\lVert A^{(j)}\rVert \le \binom{w+j(k_h-1)}{j}\sigma^j$ for every threshold $w$ (not only rung weights) and every
$\sigma \ge \max_l\lvert\sin\theta_l\rvert$; with $w = w_m$ it is the paper's display, since $w_m + j(k_h-1) = w_{m+j}$
(`PauliString.rungWeight_add_jump`). Stronger than the paper's statement in that there is no condition on the angles at all (in
particular no $\delta t \le \pi/2$), and the row and column sums are proved for the actual matrix entries, so cancellations
between branches are allowed for. The hypothesis is `IsLayer kh`, that is, pairwise disjoint supports together with
$\lvert G\rvert \le k_h$ for every generator of the layer. The decomposition into exactly-$j$-jump components holds for any ordered list of rotations;
disjointness is used for the count $\lvert\mathcal A(s)\rvert \le \lvert s\rvert$ of anticommuting generators
(`card_antiLayer_le_weight`) and for commutation within the layer.

## 5. Cumulation

**Statement (`apd:cor:norm_cumulation_jump`, `apd:eq:layer_cumulation`).** Let $O$ be $k_o$-local, so that
$\mathcal N^{(0)}_{\ge m} = 0$ for $m \ge 1$.

(i) After any $g$ single rotations,

$$\mathcal N^{(g)}_{\ge m} \le \binom{g}{m}\sin^m(\delta t)\,\lVert O\rVert_{\bar 2}.$$

(ii) After any $T$ disjoint-support layers, counting single-jump inflow only,

$$\mathcal N^{(T)}_{\ge m} \le \binom{T}{m}\sin^m(\delta t)\prod_{j=2}^{m+1}w_j\cdot\lVert O\rVert_{\bar 2}.$$

Both bounds hold along the LPD trajectory, with truncations interleaved.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:cor:norm_cumulation_jump` (i) | `Ladder`, `Ladder.cumulation`, `sum_range_choose`, `PauliString.pauliLadder`, `PauliString.pauliLadderTrunc` | `Ladder.Defs`, `Ladder.Recursion`, `Ladder.HockeyStick`, `Pauli.Flow`, `Pauli.Truncate` | faithful |
| `apd:cor:norm_cumulation_jump` (ii), `apd:eq:layer_cumulation` | `WeightedLadder`, `WeightedLadder.cumulation`, `layer_cumulation`, `weighted_prod_eq`, `satLadder_cumulation_eq` | `Ladder.Weighted` | weaker |

**Relation.** `Ladder.cumulation` derives (i) from the four properties of an abstract ladder (non-negativity, a reservoir
bounded by $M$, a vanishing initial condition, and the recursion of Section 3). `pauliLadder` constructs that ladder for the
Pauli model and `pauliLadderTrunc` for the trajectory truncated to an arbitrary family of retained sets, so (i) is
`Ladder.cumulation` applied to either structure; this one-line composition is not given a name of its own. The hypotheses are
Hermitian generators of weight at most $k_h$, $\lvert\sin\theta_g\rvert \le a$ for every rotation, and the coefficient form of
$k_o$-locality. For (ii), `layer_cumulation` proves the display for every sequence obeying the single-jump layer recursion
$N_m^{(T+1)} \le N_m^{(T)} + w_{m+1}a\,N_{m-1}^{(T)}$. Weaker than a statement about Pauli layers, because that recursion is a
hypothesis: a physical layer also has multi-jump inflow, and the statement that holds for actual layers is the majorant of
Section 6, whose all-single-jump term is the display (ii) times $E_1/\varepsilon^{(1)}_1$ (`chain_diag`). `satLadder_cumulation_eq`
shows that the constant in (ii) is attained by a sequence satisfying the recursion with equality.

## 6. Multi-jump recursion and first-passage majorant

**Mechanism (`apd:rmk:multijump`).** Within one layer a string can be hit by $j \ge 2$ anticommuting rotations and climb $j$ rungs
at once. By Section 4 the corresponding block has norm at most

$$\varepsilon^{(m)}_j := \frac{\bigl(w_{m+j}\sin\delta t\bigr)^j}{j!}.$$

A $j$-jump carries the same power $\sin^j\delta t$ as $j$ single jumps but occupies one layer slot and feeds rung $m$ from rung
$m-j$; multi-jumps are therefore additive inflows and are carried through the ladder by the statements below.

**Statement (`apd:thm:first_passage`).** Under the hypotheses of Section 4 and $\beta \lt 1$, along the LPD trajectory of a $k_o$-local $O$, for
every rung $m \ge 1$ and every layer (`apd:eq:multijump_recursion`),

$$\mathcal N^{(T)}_{\ge m} \le \mathcal N^{(T-1)}_{\ge m} + \sum_{j\ge1}\varepsilon^{(m)}_j\,\mathcal N^{(T-1)}_{\ge m-j},$$

and consequently, for every $m \ge 1$ and $T \ge 0$ (`apd:eq:composition_majorant`),

$$\mathcal N^{(T)}_{\ge m} \le \lVert O\rVert_{\bar 2}\sum_{k=1}^{\min(m,T)}\binom{T}{k}
\sum_{0 \lt \nu_1 \lt \dots \lt \nu_k = m} E_{\nu_1}\prod_{i=2}^{k}\varepsilon^{(\nu_i)}_{\nu_i-\nu_{i-1}},
\qquad E_\nu := \sum_{j\ge\nu}\varepsilon^{(\nu)}_j.$$

The right-hand side is non-decreasing in $T$, and its term with $k = m$ and all $\nu_i = i$ is the bound (ii) of Section 5
times $E_1/\varepsilon^{(1)}_1$.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:rmk:multijump` | `epsJump`, `entryFactor`, `betaOf` (definitions) | `Constants.Entry` | faithful |
| `apd:eq:multijump_recursion` | `PauliString.highNorm_layerConj_le_multi`, `PauliString.layerN_step`, `PauliString.pauliMultiLadder` | `Pauli.LayerLadder` | faithful |
| `apd:thm:first_passage`, `apd:eq:composition_majorant` | `MultiLadder`, `chain`, `MultiLadder.majorant`, `MultiLadder.le_majorant`, `PauliString.layerN_le_majorant` | `Ladder.MultiJump`, `Pauli.LayerLadder` | faithful |
| monotonicity in $T$; the all-ones term | `MultiLadder.majorant_mono`, `chain_diag`, `chain_eq_zero_of_lt`, `MultiLadder.majorant_eq_sum_range` | `Ladder.MultiJump`, `Ladder.Assembly` | faithful |

**Relation.** The docstrings cite the recursion and the majorant under the label of the remark that introduces them,
`apd:rmk:multijump`. `highNorm_layerConj_le_multi` is the recursion for one layer and an arbitrary matrix, written with the reservoir
convention already substituted:
$\mathcal N^{(T)}_{\ge m} \le \mathcal N^{(T-1)}_{\ge m} + \sum_{1\le j \lt m}\varepsilon^{(m)}_j\,\mathcal N^{(T-1)}_{\ge m-j} + E_m\lVert O\rVert_{\bar 2}$,
where the jumps with $j \ge m$, including every overshoot, are collected in the entry factor. `layerN_step` is the same along a
trajectory truncated to an arbitrary family of retained sets, and `pauliMultiLadder` packages it as a `MultiLadder`.
`chain ε E k m` is defined by peeling off the last jump ($\mathrm{chain}_1(m) = E_m$ and
$\mathrm{chain}_{k+2}(m) = \sum_{1\le j \lt m}\varepsilon^{(m)}_j\,\mathrm{chain}_{k+1}(m-j)$); unfolding the recursion gives the sum over
$0 \lt \nu_1 \lt \dots \lt \nu_k = m$ of the display. Lean sums $k$ from $0$ to $T$; the extra terms vanish (`chain_eq_zero_of_lt`).
`le_majorant` is the abstract induction (Pascal's rule) and `layerN_le_majorant` its instance for Pauli layers. Lean carries the
hypothesis $\beta \lt 1$, under which the series $E_m$ converges (`summable_epsJump_tail`, in `Pauli.LayerLadder`): `entryFactor` is a
`tsum`, which Lean sets to zero for a divergent series, whereas the display holds trivially when $E_m = \infty$. In the regime of
Section 10, $\beta \le 1/(4e)$. The example
mentioned in the paper's remark (a triple jump of $Z_1Z_2Z_3$) is checked at coefficient level in `tests/LayerFlow.lean`
(`triple_jump_magnitude`), and `tests/MultiJumpWitness.lean` contains the
analogous double jump of $Z_0Z_2$ under the layer $\lbrace X_0X_1, X_2X_3\rbrace$, with strictly positive mass above rung two
after a single layer (`physical_N_two_pos`).

## 7. Entry factor and part factor

**Statement (`apd:thm:entry_factor`, `apd:eq:entry_bound`).** If $\beta \lt 1$, then
$\varepsilon^{(\nu)}_{j+1} \le \beta\,\varepsilon^{(\nu)}_j$ for all $j \ge \nu \ge 1$, and hence

$$E_\nu \le \frac{\varepsilon^{(\nu)}_\nu}{1-\beta} \le \varepsilon^{(\nu)}_\nu\,(1+2\beta) \le \varepsilon^{(\nu)}_\nu\,(1+4e\beta),$$

the last two inequalities for $\beta \le 1/2$. Moreover $r \ge 8e^2 w_2\,\alpha t$ implies $4e\beta \le 1$.

**Statement (`apd:thm:part_factor`, `apd:eq:part_factor`).** A part of size $j \ge 1$ ending at the boundary $\sigma \ge j$ costs,
relative to the $j$ single jumps that it replaces,

$$\rho(j,\sigma) := \frac{\varepsilon^{(\sigma)}_j}{\prod_{\nu=\sigma-j+1}^{\sigma}\varepsilon^{(\nu)}_1}
= \frac{(\sigma+j-1+c)^j}{j!\,\prod_{i=\sigma-j+1}^{\sigma}(i+c)} \le \Bigl(\frac94\Bigr)^{j-1},$$

with equality for $j = 1$, and for $j = \sigma = 2$ with $k_o = 0$.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:thm:entry_factor`, `apd:eq:entry_bound` | `epsJump_ratio`, `entryFactor_le_geom`, `entryFactor_le`, `one_add_two_mul_le_source` | `Constants.Entry` | faithful |
| $r \ge 8e^2w_2\alpha t$ gives $4e\beta \le 1$ and $\beta \le 1/2$ | `source_entry_inflation_le_one`, `source_beta_le_half` | `Pauli.LayerError` | faithful |
| `apd:thm:part_factor`, `apd:eq:part_factor` | `partFactor`, `epsJump_mul_chainWeight_eq_partFactor`, `partFactor_one`, `partFactor_le`, `partFactor_le_of_one_le`, `partFactor_antitone`, `partFactor_at_diag`, `diagFactor_le` | `Constants.PartFactor`, `Constants.ChainWeights` | faithful |

**Relation.** The three inequalities of `apd:eq:entry_bound` are `entryFactor_le_geom` (for $\beta \lt 1$), `entryFactor_le` (for
$\beta \le 1/2$) and `one_add_two_mul_le_source`; the term ratio is `epsJump_ratio`. The constant carried into $c_0$ is
$1+4e\beta$ in the paper and in Lean alike. In Lean $k_h-1$ is any positive real and $c$ any non-negative real. `partFactor j s`
is $\rho$ as a function of the single variable $s = \sigma + c$, a real number with $s \ge j$; the first equality of the
display is `epsJump_mul_chainWeight_eq_partFactor` (in product form), monotonicity in $s$ is `partFactor_antitone`, the value
at $s = j$ is $(2j-1)^j/(j!)^2$ (`partFactor_at_diag`, equal to $9/4$ at $j = 2$), and the bound is `partFactor_le` for
$j \ge 2$ and `partFactor_one` for $j = 1$.

## 8. Summed inflow and the constant $c_0$

**Statement (`apd:thm:multijump_sum`, `apd:eq:multijump_sum`).** Let one Trotter step consist of $\Gamma$ disjoint-support
layers followed by the truncation at $w^\ast = w_{m^\ast+1}$, and assume $\sin\delta t \le \alpha t/r$ and $\beta \le 1/2$. Then
the norm discarded over all $r$ steps obeys

$$\sum_{d=1}^{r}\bigl\lVert\tilde O^{(d)}_{\ge w^\ast+1}\bigr\rVert_{\bar 2} \le
(1+4e\beta)\,\exp\Bigl[\frac94\,\frac{(m^\ast+1)^2}{(r+1)\,\Gamma}\Bigr]
\Bigl(\frac{r+1}{r}\,\Gamma\,\alpha t\Bigr)^{m^\ast+1}\frac{\prod_{j=2}^{m^\ast+2}w_j}{(m^\ast+1)!}\cdot\lVert O\rVert_{\bar 2}.$$

Here $\tilde O^{(d)}_{\ge w^\ast+1}$ is the high-weight part at the end of step $d$, before the truncation; it has the norm of
$X_d$ (Section 9).

**Statement (`apd:thm:c0_bound`, `apd:eq:multijump_factor`, `apd:eq:c0`).** Relaxing $(r+1)\Gamma \ge r\Gamma$, the correction
relative to the single-jump sector is

$$(1+4e\beta)\,\exp\Bigl[\frac94\,\frac{(m^\ast+1)^2}{r\,\Gamma}\Bigr]
\qquad\text{under}\qquad r \ge \frac{8\,(m^\ast+1)^2}{\Gamma}\quad\text{and}\quad r \ge 8e^2w_2\,\alpha t,$$

and taking the $(m^\ast+1)$-th root of the product of the three $r$-dependent factors gives the constant

$$c_0 := \frac{r+1}{r}\,\exp\Bigl[\frac94\,\frac{m^\ast+1}{r\,\Gamma}\Bigr]\,(1+4e\beta)^{1/(m^\ast+1)}
\le \frac65\cdot\frac{64}{55}\cdot\sqrt2 \lt 2 \qquad\text{for } m^\ast \ge 1 \text{ and } r \ge 5.$$

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| slot sum $\sum_{d=1}^{r}\binom{d\Gamma}{K} \le ((r+1)\Gamma)^{K+1}/(\Gamma\,(K+1)!)$ | `sum_choose_mul_le` | `Constants.StepSum` | faithful |
| one step is bounded by $\Gamma$ times the majorant at its end; sum over steps | `MultiLadder.block_inflow_le`, `MultiLadder.sum_block_inflow_le`, `PauliString.sum_pauliNorm_discardedLayerStep_le_chain` | `Ladder.ChainBound`, `Pauli.LayerError` | faithful |
| weight of a decomposition; sum over the excess $D$ | `chain_le_weighted_choose`, `chain_epsJump_le_weighted_choose_source`, `sum_factorial_sectors_le_exp`, `slot_polynomial_le_exp`, `chain_slot_sum_le_exp` | `Ladder.ChainBound`, `Constants.ChainWeights`, `Constants.AssemblyBound` | faithful |
| `apd:thm:multijump_sum`, `apd:eq:multijump_sum` | `MultiLadder.sum_block_epsJump_le_exp_source`, `PauliString.layerStepMass_reset`, `PauliString.layerStepMass_inflow` | `Constants.AssemblyBound`, `Pauli.LayerError` | faithful |
| `apd:eq:multijump_factor`; definition of $c_0$ | `cZero`, `Admissible`, `cZero_pow_nat`, `sector_bound_le_cZero` | `Constants.C0`, `Constants.AssemblyBound` | faithful |
| `apd:thm:c0_bound`, `apd:eq:c0` | `cZero_le_two_sharp`, `cZero_le_two` | `Constants.C0` | faithful |

**Relation.** `sum_block_epsJump_le_exp_source` is `apd:eq:multijump_sum` for any `MultiLadder` with the weights of the model and
any per-step mass that vanishes at the start of each step and obeys the multi-jump inflow; its right-hand side keeps the bound
$a$ on the sines explicit, as $((r+1)\Gamma a)^{m^\ast+1}$, and `sector_bound_le_cZero` inserts $a \le \alpha t/r$ and relaxes
$(r+1)\Gamma$ to $r\Gamma$ in the exponential. For Pauli layers the two hypotheses are theorems: `layerStepMass_reset` (the
mass above the cutoff vanishes at the start of every step, by $k_o$-locality for the first step and by the preceding cut
afterwards) and `layerStepMass_inflow`. `cZero r m G B` is the $c_0$ of the display with $B$ standing for $4e\beta$, and
`cZero_pow_nat` is the identity $c_0^{m^\ast+1} = (\tfrac{r+1}{r})^{m^\ast+1}\exp[\tfrac94(m^\ast+1)^2/(r\Gamma)]\,(1+B)$.
`Admissible r m G` is the conjunction $1 \le r$, $0 \le m$, $0 \lt G$, $m \le r$, $8(m+1)^2 \le rG$, with all arguments real.
`cZero_le_two_sharp` proves $c_0 \le \tfrac{384}{275}\sqrt2$, which is the paper's $\tfrac65\cdot\tfrac{64}{55}\cdot\sqrt2$, for
`Admissible r m G`, $m \ge 1$, $r \ge 5$ and $0 \le B \le 1$; `cZero_le_two_without_m_le_r` shows that $m \le r$ and $G \gt 0$ are not
needed for it. $B \le 1$ is supplied by `source_entry_inflation_le_one` (Section 7).

**The hypotheses $r \ge 5$ and $m^\ast \ge 1$ of $c_0 \le 2$ cannot be dropped.** Each numerical point below satisfies `Admissible` and $0 \le B \le 1$; the fourth row is a general statement for $B \ge 1$ without `Admissible`, which meets the admitted range at $B = 1$. No witness is given for the remaining hypotheses.

| Hypothesis | Witness $(r, m^\ast, \Gamma, B)$ | Value of $c_0$ | Lean declaration |
|---|---|---|---|
| $r \ge 5$ cannot be dropped, even for $B = 0$ | $(1, 1, 32, 0)$ | $2e^{9/64} \approx 2.30$ | `two_lt_cZero_of_admissible` |
| $r \ge 5$ cannot be replaced by $r \ge 4$ | $(4, 1, 8, 1)$ | $\tfrac54 e^{9/64}\sqrt2 \approx 2.03$ | `two_lt_cZero_of_admissible_four` |
| $m^\ast \ge 1$ cannot be dropped | $(5, 0, 2, 1)$ | $\tfrac{12}{5} e^{9/40} \approx 3.01$ | `two_lt_cZero_of_m_zero` |
| at $m^\ast = 0$ no condition on $r$ or $\Gamma$ helps | every $r \gt 0$, $\Gamma \gt 0$, $B \ge 1$ | $c_0 \gt 2$ | `two_lt_cZero_of_m_zero_general` |
| $m^\ast \ge 2$ does not replace $r \ge 5$ | $(2, 2, 36, 1)$ | $\tfrac32 e^{3/32}\,2^{1/3} \approx 2.08$ | `two_lt_cZero_of_m_two` |

Further sufficient conditions are proved in the same module: `cZero_le_two_of_three_le_m` ($m^\ast \ge 3$, with no condition on
$r$ beyond `Admissible`), `cZero_le_two_of_gamma_le_six` and `cZero_le_two_of_gamma_le_seven` ($m^\ast \ge 1$ and a cap on the
number of layers per step). Without $m^\ast \ge 1$ and $r \ge 5$ one still has $c_0 \le 4e^{9/32}$ (`cZero_le_four_mul_exp`,
attained at $(1,0,8,1)$ by `cZero_eq_four_mul_exp_at_worst`) and $c_0 \le 10/3$ once $m^\ast \ge 1$
(`cZero_le_ten_thirds_of_one_le_m`). `scripts/c0_scan.py` evaluates the same points in floating point.

## 9. Telescoping and the discarded operator

**Statement (`apd:eq:step_component`).** The operator discarded at the end of Trotter step $d$ is

$$X_d := (1-\Pi_{\le w^\ast})\;\widetilde U^\dagger\,\tilde O^{(d-1)}_{\le w^\ast}\,\widetilde U .$$

**Statement (`apd:thm:triangle`).** The difference between the untruncated and the truncated evolution telescopes,

$$\tilde O^{(r)} - \tilde O^{(r)}_{\le w^\ast} = \sum_{d=1}^{r}\widetilde U^{\dagger (r-d)}\,X_d\,\widetilde U^{\,r-d},
\qquad \tilde O^{(r)} := \widetilde U^{\dagger r} O\,\widetilde U^{r},$$

and, for an input state all of whose intermediate Trotter evolutions satisfy the paper's entanglement condition, the error of
the expectation value
$\Delta\tilde\mu_{\le w^\ast} := \lvert\langle\psi\rvert(\tilde O^{(r)} - \tilde O^{(r)}_{\le w^\ast})\lvert\psi\rangle\rvert$
obeys

$$\Delta\tilde\mu_{\le w^\ast} \le \sqrt2\,\sum_{d=1}^{r}\bigl\lVert\tilde O^{(d)}_{\ge w^\ast+1}\bigr\rVert_{\bar 2}.$$

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:eq:step_component` | `PauliString.discardedStep`, `PauliString.discardedStep_eq_truncOp`, `PauliString.pauliNorm_discardedStep`, `PauliString.discardedLayerStep`, `PauliString.pauliNorm_discardedLayerStep` | `Pauli.TrotterTruncate`, `Pauli.LayerError` | faithful |
| the LPD trajectory | `PauliString.truncOp`, `PauliString.coeff_truncOp`, `PauliString.trotterStepTraj`, `PauliString.trotterTraj_at_boundary`, `PauliString.layerStepTraj`, `PauliString.layerScheduledTraj_at_boundary` | `Pauli.Truncate`, `Pauli.TrotterTruncate`, `Pauli.LayerError` | faithful |
| `apd:thm:triangle`, telescoping identity | `PauliString.trotterStep_telescoping`, `PauliString.layerStep_telescoping` | `Pauli.TruncationError`, `Pauli.LayerError` | faithful |
| `apd:thm:triangle`, conclusion | `PauliString.pauliNorm_trotterStep_error_le`, `PauliString.pauliNorm_trotterTraj_error_le`, `PauliString.pauliNorm_trotterStep_error_le_highNorm`, `PauliString.pauliNorm_layerStep_error_le` | `Pauli.TruncationError`, `Pauli.LayerError` | weaker |

**Relation.** `discardedStep_eq_truncOp` identifies the discarded operator with the high-weight projection of the operator
before the cut, and `pauliNorm_discardedStep` (for layered steps, `pauliNorm_discardedLayerStep`) gives
$\lVert X_d\rVert_{\bar 2} = \lVert\tilde O^{(d)}_{\ge w^\ast+1}\rVert_{\bar 2}$; the underlying identity is
`PauliString.pauliNorm_sub_truncOp_highSet_compl` in `Pauli.Discard`. The step-indexed trajectory and the trajectory indexed by
rotations (or layers) with a cut after every block are defined independently, and their agreement at step boundaries is a
theorem. Lean counts steps from zero, so `discardedStep … d` is $X_{d+1}$ and the exponent `r - 1 - d` is the paper's $r-d$. The
conclusion is formalized at the norm level only:

$$\bigl\lVert\tilde O^{(r)} - \tilde O^{(r)}_{\le w^\ast}\bigr\rVert_{\bar 2} \le \sum_{d=1}^{r}\lVert X_d\rVert_{\bar 2},$$

assuming only that the generators are Hermitian (so that the remaining evolution preserves the norm,
`PauliString.pauliNorm_blockEnd_pow`). Weaker than the paper's proposition: there is no state, no expectation value and no factor
$\sqrt2$ in Lean. A two-qubit instance in which the discarded operator is nonzero is in `Pauli.DiscardWitness`.

## 10. The truncation-error bound

**Lean statement.** `PauliString.pauliNorm_layerStep_error_le_model_of_source_regime` (module `Pauli.LayerError`) reads

```lean
theorem pauliNorm_layerStep_error_le_model_of_source_regime
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a α t : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hα : 0 < α) (ht : 0 ≤ t) (haA : a ≤ α * t / (r : ℝ))
    (hsteps : 8 * (Real.exp 1) ^ 2 * ((ko : ℝ) + kh - 1) * α * t ≤ (r : ℝ))
    (hadm : Admissible (r : ℝ) (m : ℝ) (Γ : ℝ)) (hm : 1 ≤ m) (hr : 5 ≤ r)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      decayBase (Γ : ℝ) (kh : ℝ) α t ^ (m + 1) *
        (Real.exp 1 * ((m : ℝ) + 1)) ^ ((ko : ℝ) / (kh - 1 : ℕ)) * pauliNorm O
```

In the notation of the paper: a Trotter step is the block of layers `layers 0`, …, `layers (Γ-1)`, each a list of Hermitian
Pauli generators of weight at most $k_h \ge 2$ with pairwise disjoint supports, and the same block is repeated $r$ times; every
conjugation angle has $\lvert\sin\theta\rvert \le a \le \alpha t/r$; $O$ is $k_o$-local; $m^\ast \ge 1$, $r \ge 5$, $r \ge m^\ast$,
$8(m^\ast+1)^2 \le r\Gamma$ and $r \ge 8e^2(k_o+k_h-1)\alpha t$. Then, with $w^\ast = k_o+m^\ast(k_h-1)$,

$$\bigl\lVert\,\widetilde U^{\dagger r} O\,\widetilde U^{r} - \mathrm{LPD}_r(O)\,\bigr\rVert_{\bar 2}
\le \Bigl(\frac{t}{t_0}\Bigr)^{m^\ast+1}\bigl(e\,(m^\ast+1)\bigr)^{k_o/(k_h-1)}\,\lVert O\rVert_{\bar 2},
\qquad t_0 = \frac{1}{2\,\Gamma\,(k_h-1)\,\alpha}.$$

`tZeroModel Γ kh α` is this $t_0$ and `decayBase Γ kh α t` is $t/t_0$. The inequality holds for every $t \ge 0$; it is a decaying
bound in $m^\ast$ when $t \lt t_0$ (`decayBase_lt_one`, `pow_decayBase_antitone`). No hypothesis on a state, on the geometry or on
the number of qubits enters. `tests/LayerError.lean` applies the theorem to a three-qubit circuit whose discarded operators are
nonzero (`model_bound_instance`).

**Paper statement (`apd:thm:one_step_truncation_error`, `apd:eq:total_truncation_error`, `apd:eq:time_condition`).** Let $H$ be
$k_h$-local, $k_h \ge 2$, with $\Gamma$ layers of pairwise disjoint supports, let $O$ be $k_o$-local, and let the input state
satisfy the hypothesis of `apd:thm:triangle`. With $\alpha = 2\max_l\lvert\alpha_l\rvert$, $w^\ast = k_o+m^\ast(k_h-1)$,
$c = k_o/(k_h-1)$, $m^\ast \ge 1$ and $r \ge \max\bigl(5,\ m^\ast,\ 8(m^\ast+1)^2/\Gamma,\ 8e^2(k_o+k_h-1)\alpha t\bigr)$,

$$\Delta\tilde\mu_{\le w^\ast} \le 2\sqrt2\,\Bigl(\frac{t}{t_0}\Bigr)^{m^\ast+1}(m^\ast+2)\,\bigl(e\,(m^\ast+2)\bigr)^{c}\,\lVert O\rVert_{\bar 2},
\qquad t \lt t_0 := \frac{1}{c_0\,\Gamma\,(k_h-1)\,\alpha},$$

where $c_0 \le 2$, and $\Gamma$ is replaced by $\Upsilon\Gamma$ for a $p$-th order formula. The norm-level display behind it
(`apd:eq:total_high_weight_norm`), with all jump sectors included through $c_0$ as in Section 8, is

$$\sum_{d=1}^{r}\bigl\lVert\tilde O^{(d)}_{\ge w^\ast+1}\bigr\rVert_{\bar 2}
\le \bigl(c_0\,\Gamma\,\alpha t\bigr)^{m^\ast+1}\frac{\prod_{j=2}^{m^\ast+2}w_j}{(m^\ast+1)!}\,\lVert O\rVert_{\bar 2}
\le \bigl(c_0\,\Gamma\,(k_h-1)\,\alpha t\bigr)^{m^\ast+1}(m^\ast+2)\,\bigl(e\,(m^\ast+2)\bigr)^{c}\,\lVert O\rVert_{\bar 2},$$

and the bound decays in $m^\ast$ under the condition $t \lt t_0$ (`apd:eq:time_condition`).

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:eq:total_high_weight_norm`, first inequality | `MultiLadder.sum_block_epsJump_le_cZero`, `PauliString.sum_pauliNorm_discardedLayerStep_le_cZero`, `PauliString.pauliNorm_layerStep_error_le_cZero` | `Constants.AssemblyBound`, `Pauli.LayerError` | faithful |
| rung product and its estimate | `prod_rungW_eq`, `prod_add_one_le_factorial_exp_rpow`, `prod_shift_le`, `prod_shifted_le_factorial_exp_rpow` | `Constants.StepSum`, `Constants.AssemblyBound` | stronger |
| `apd:eq:total_high_weight_norm`, second inequality | `total_truncation_error`, `total_truncation_error_product_bound` | `Constants.Total`, `Constants.AssemblyBound` | stronger prefactor, with $c_0$ replaced by $2$ |
| `apd:eq:time_condition` | `tZero`, `tZeroModel`, `tZeroModel_le_tZero`, `lt_tZero_of_lt_tZeroModel`, `decayBase`, `decayBase_lt_one`, `pow_decayBase_antitone`, `tZero_anti` | `Constants.C0`, `Constants.Total` | faithful, with $c_0$ replaced by $2$ |
| `apd:thm:one_step_truncation_error`, `apd:eq:total_truncation_error` | `PauliString.pauliNorm_layerStep_error_le_model`, `PauliString.pauliNorm_layerStep_error_le_model_of_source_regime` | `Pauli.LayerError` | weaker (norm level only); at that level stronger in the prefactor, with $c_0$ replaced by $2$ |

**Relation.** The chain from the Lean theorems to the paper's displays is as follows.

1. `sum_pauliNorm_discardedLayerStep_le_cZero` is the first inequality of `apd:eq:total_high_weight_norm` for the actual
   discarded operators, with the instance-dependent constant $c_0$ = `cZero r m Γ (4eβ)` retained. It assumes only the layer
   data, the $k_o$-locality of $O$, $\beta \le 1/2$, $r \ge 1$ and $a \le \alpha t/r$, and holds for every $m^\ast \ge 0$.
   `pauliNorm_layerStep_error_le_cZero` is the same bound for the error norm, by Section 9.
2. `prod_rungW_eq` gives $\prod_{j=2}^{m^\ast+2}w_j = (k_h-1)^{m^\ast+1}\prod_{i=1}^{m^\ast+1}(i+c)$, and
   `prod_add_one_le_factorial_exp_rpow` gives $\prod_{i=1}^{n}(i+c) \le n!\,(en)^c$. Together,
   $\prod_{j=2}^{m^\ast+2}w_j/(m^\ast+1)! \le (k_h-1)^{m^\ast+1}(e(m^\ast+1))^c$. Since
   $(e(m^\ast+1))^c \le (m^\ast+2)(e(m^\ast+2))^c$, this is stronger than the paper's statement of the second inequality, whose
   prefactor is $(m^\ast+2)(e(m^\ast+2))^c$; the estimate in the paper's form is also proved
   (`prod_shift_le`, `prod_shifted_le_factorial_exp_rpow`).
3. `total_truncation_error_product_bound` is a statement about real numbers: any $S$ bounded as in step 1 satisfies
   $S \le (t/t_0)^{m^\ast+1}(e(m^\ast+1))^c M$ with $t_0 = 1/(2\Gamma(k_h-1)\alpha)$, provided `Admissible r m Γ`, $m^\ast \ge 1$,
   $r \ge 5$ and $0 \le 4e\beta \le 1$. This is where $c_0 \le 2$ (`cZero_le_two`) is used: the constant $2$ in `tZeroModel` is
   the paper's bound $c_0 \le 2$. Applied to the error norm it yields the theorem displayed at the top of this section; applied to
   $S = \sum_d\lVert X_d\rVert_{\bar 2}$ it yields the norm-level display of the paper with $c_0$ replaced by $2$ and with the
   smaller prefactor of step 2.
4. `source_entry_inflation_le_one` derives $4e\beta \le 1$ from $r \ge 8e^2(k_o+k_h-1)\alpha t$, which is how
   `…_of_source_regime` follows from `pauliNorm_layerStep_error_le_model`.

Consequently Lean proves the paper's norm-level estimate, read with the uniform constant $c_0 = 2$, for the error norm (the theorem above); for the sum $\sum_d\lVert X_d\rVert_{\bar 2}$ that the paper's display bounds, it follows by composing `sum_pauliNorm_discardedLayerStep_le_cZero` with `total_truncation_error_product_bound`, a composition that has no name in the library. Both have a
better prefactor. With the instance-dependent $c_0 \lt 2$ the paper's base $t/t_0$ is smaller than Lean's, while Lean's prefactor
is smaller than the paper's; the instance-dependent constant is available in Lean in the form of step 1. Using the literal $2$
makes $t_0$ a function of $\Gamma$, $k_h$ and $\alpha$ alone, so that $t/t_0$ is fixed before $m^\ast$ and $r$ are chosen, and it is
conservative: `tZeroModel_le_tZero` proves $1/(2\Gamma(k_h-1)\alpha) \le 1/(c_0\Gamma(k_h-1)\alpha)$, hence $t \lt$ `tZeroModel`
implies the paper's time condition. The hypotheses of the Lean theorem are those of the paper's theorem, one for one
(`Admissible` encodes $r \ge m^\ast$ and $r \ge 8(m^\ast+1)^2/\Gamma$), except that Lean has no hypothesis on a state. The paper's
theorem additionally converts the norm-level bound into a bound on the expectation value $\Delta\tilde\mu_{\le w^\ast}$, through
`apd:thm:triangle` and under its hypothesis on the state; this is the origin of the factor $\sqrt2$ (the paper states the weaker $2\sqrt2$), and it is a step outside
this repository.

**Remark (`apd:rmk:comparison`).** The paper remarks that the rung-weighted product $\prod_j w_j$ cancels the factorial of the
slot count, so that the threshold carries $\Gamma(k_h-1)$ and no factor exponential in $\Gamma$. In Lean this cancellation is
the algebra of `total_truncation_error`, where $(k_h-1)^{m^\ast+1}$ from `prod_rungW_eq` is absorbed exactly into
$(t/t_0)^{m^\ast+1}$. The numerical comparisons of the remark are not formalized.

## 11. Threshold existence

**Statement (`apd:thm:truncation_threshold_entangled`, `eq:truncation_weight_bound`).** Under the hypotheses of
`apd:thm:one_step_truncation_error` and for $t \lt t_0$, the truncation threshold

$$w^\ast = k_o + (k_h-1)\,m^\ast, \qquad
m^\ast \in O\Bigl(\frac{\log(1/\epsilon) + \bigl(1+\tfrac{k_o}{k_h-1}\bigr)\log\log(1/\epsilon)}{\log(t_0/t)}\Bigr),$$

suffices for a truncation error of at most $\epsilon\,\lVert O\rVert_{\bar 2}$.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:thm:truncation_threshold_entangled`, `eq:truncation_weight_bound` | `norm_majorant_tendsto_zero`, `exists_norm_threshold`, `exists_eventual_norm_threshold`, `exists_uniform_norm_threshold`, `exists_uniform_weight_cutoff`, `exists_model_norm_threshold`, `exists_admissible_step_count` | `Constants.Threshold` | weaker |

**Relation.** Weaker than the paper's corollary in three respects: existence only, norm level only, and a statement about the scalar majorant only, which is not composed in Lean with the theorem of Section 10 (there $r$, and with it the angles, must be chosen after $m^\ast$, and `Constants.Threshold` does not assume that a fixed family of angles still satisfies $a \le \alpha t/r$ when $r$ changes). `norm_majorant_tendsto_zero`
proves that the right-hand side of Section 10, $q^{m+1}(e(m+1))^c M$, tends to zero as $m \to \infty$ for every $0 \le q \lt 1$, and
`exists_model_norm_threshold` concludes that for $t \lt$ `tZeroModel` every tolerance $\epsilon \gt 0$ is met by some finite
$m^\ast \ge 1$. `exists_uniform_weight_cutoff` states the same for a family of errors with a common majorant, in terms of the
weight $w = k_o+(k_h-1)m$, and `exists_admissible_step_count` provides a step number with $r \ge 5$, $r \ge m^\ast$ and any two
further lower bounds. The explicit logarithmic rate of `eq:truncation_weight_bound` is not formalized, and the tolerance in Lean
refers to the norm-level bound, not to an expectation value.

## 12. Light cone

**Statement (`apd:thm:lightcone`).** Let the observable have Pauli strings of weight at most $w^\ast$, polynomially many, and
let one Trotter step consist of $\Gamma$ (for the $p$-th order formula, $\Upsilon\Gamma$) layers of $k_h$-local rotations with
pairwise disjoint supports within each layer. If $w^\ast \in O(1)$, the number of Pauli strings in the observable at the end of
one step, before truncation, is $O(n^{w^\ast})$. The argument has three parts:

* (count) there are at most $\sum_{w=1}^{w^\ast}3^w\binom{n}{w} \le (3en/w^\ast)^{w^\ast}$ strings of weight at most $w^\ast$;
* (weight) within a layer a string of weight $w$ meets at most $w$ rotations, each raising the weight by at most $k_h-1$, so after
  layer $\gamma$ the weight is at most $w^\ast k_h^{\gamma}$, and at most $w^\ast k_h^{\Upsilon\Gamma}$ at the end of the step;
* (branches) each rotation that is met at most doubles the number of strings, so every initial string has at most
  $\prod_{\gamma=1}^{\Upsilon\Gamma}2^{w^\ast k_h^{\gamma-1}} \le 2^{w^\ast k_h^{\Upsilon\Gamma}}$ descendants.

**Statement (`apd:thm:runtime`).** For $t \lt t_0$, tolerance $\epsilon$, a $k_o$-local observable with $\lVert O\rVert_{\bar 2} = 1$ and
an input state as in `apd:thm:triangle`, LPD approximates the expectation value to within $2\epsilon$ in time
$O((r+1)\,n^{w^\ast})$ and memory $O(n^{w^\ast})$, with $w^\ast$ from Section 11 and $r$ the number of Trotter steps required by the
Trotter error.

| Paper label | Lean declaration | Module | Relation |
|---|---|---|---|
| `apd:thm:lightcone`, count (also the counting step of `apd:thm:runtime`) | `PauliString.lowSet`, `PauliString.card_lowSet_le`, `PauliString.card_lowSet_le_pow` | `Pauli.Count` | faithful in the scaling $n^{w}$, with a different explicit constant |
| `apd:thm:lightcone`, a string meets at most $\lvert s\rvert$ rotations of a layer | `PauliString.card_antiLayer_le_weight` | `Pauli.LayerFlow` | faithful |
| `apd:thm:lightcone`, weight growth | `PauliString.branch`, `PauliString.oneLayer`, `PauliString.reachable`, `PauliString.card_cover_le`, `PauliString.layer_weight_le`, `PauliString.reachable_weight_le` | `Pauli.LayerWitness` | faithful, for the over-approximation `reachable` |
| tightness of the weight bound; the exponent counts layers | `LayerWitness.gamma_layers_weight_le`, `LayerWitness.gamma_layers_weight_four`, `LayerWitness.gamma_weight_bound_false`, `LayerWitness.gamma_weight_bound_false_unmerged`, `LayerCounterexample.pf2_coeff_polynomial`, `LayerCounterexample.pf2_coeff_ne_zero`, `LayerCounterexample.actual_discard_exceeds_gamma_bound` | `Pauli.LayerWitness`, `Pauli.LayerCounterexample` | no counterpart in the paper |
| `apd:thm:lightcone`, branch count and the conclusion $O(n^{w^\ast})$ | none | | not formalized |
| `apd:thm:runtime` | none beyond the count above | | not formalized |

**Relation.** `card_lowSet_le` and `card_lowSet_le_pow` prove, for $w \le n$,

$$\#\lbrace P : \lvert P\rvert \le w\rbrace \le \binom{n}{w}4^w \le 4^w n^w,$$

counting Pauli strings up to phase and including the identity. The constant differs from the paper's $(3en/w^\ast)^{w^\ast}$ and
neither dominates the other for all $n$ and $w$; the scaling $n^{w}$ is the same, and the Lean bound is uniform in $w$.
`layer_weight_le` states $\lvert q\rvert \le k_h\lvert p\rvert$ for every $q$ in `oneLayer L p`, and `reachable_weight_le` states
$\lvert q\rvert \le k_h^{L}\lvert p\rvert$ for every $q$ in `reachable Ls p` with $L$ the number of layers, under `IsLayer kh` for each
layer and $k_h \ge 1$. `reachable` is a combinatorial over-approximation of the set of strings with a nonzero coefficient after
conjugation: it follows both branches of every anticommuting rotation and ignores cancellations. No theorem of the library
relates it to the coefficients of an evolved operator, so these two theorems bound where coefficients can appear and do not by
themselves make a statement about a particular operator. Statements about actual coefficients are proved separately, in
`Pauli.LayerFlow` (Section 4: the $j$-jump component vanishes above weight $w + j(k_h-1)$,
`PauliString.layerJump_apply_eq_zero_of_weight_lt`) and in `Pauli.LayerCounterexample`.

**The exponent $\Upsilon\Gamma$ cannot be replaced by $\Gamma$.** The paper states its bounds for $\Gamma$ layers per step and replaces
$\Gamma$ by $\Upsilon\Gamma$ for a $p$-th order formula; the following witness shows that this replacement is needed already for the
weight bound. Take $n = 8$, $k_h = 2$ and the two brickwork layers
$L_1 = \lbrace X_0Z_1, X_2X_3, Z_4X_5, X_6X_7\rbrace$ and $L_2 = \lbrace X_1Z_2, X_3X_4, X_5X_6\rbrace$, so $\Gamma = 2$, with input
$Z_3$ and cutoff $w^\ast = 1$.

* After the two layers $L_1, L_2$ the largest reachable weight is exactly $4 = w^\ast k_h^{2}$, so the bound of
  `reachable_weight_le` is attained (`gamma_layers_weight_le`, `gamma_layers_weight_four`).
* In the layer sequence of a second-order step, $L_1, L_2, L_1$ or $L_1, L_2, L_2, L_1$, a string $P_6$ of weight $6 \gt 4$ is
  reachable (`gamma_weight_bound_false`, `gamma_weight_bound_false_unmerged`).
* This is a statement about actual coefficients and not only about `reachable`: after one second-order step
  $L_1, L_2, L_2, L_1$ with all conjugation angles equal to $\theta$, the coefficient of $P_6$ in the conjugated $Z_3$ is
  $-4\cos^2\theta\sin^5\theta$ (`pf2_coeff_polynomial`), which is nonzero for $0 \lt \theta \lt \pi/2$ (`pf2_coeff_ne_zero`), and it
  belongs to the operator discarded at $w^\ast = 1$ (`actual_discard_exceeds_gamma_bound`). The bound $w^\ast k_h^{\Upsilon\Gamma} = 16$
  for the four layers of this step is respected.

## 13. What is not formalized

* **Expectation values.** The step from the normalized Pauli 2-norm of the discarded operators to the error of an expectation
  value in a given state is outside this repository: neither the average over a state 2-design nor the bound for sufficiently
  entangled states is formalized. This concerns the conclusions of `apd:thm:triangle`, `apd:thm:one_step_truncation_error` and
  `apd:thm:truncation_threshold_entangled`, all of which are formalized at the norm level only (Sections 9 to 11).
* **Trotter error.** $\lVert e^{iHt} O e^{-iHt} - \widetilde U^{\dagger r} O\,\widetilde U^{r}\rVert$ is not formalized, and neither is the
  product formula `apd:eq:suzuki`: the layers of a step and the bound $\lvert\sin\theta\rvert \le \alpha t/r$ on their conjugation
  angles are inputs of the Lean theorems.
* **Runtime.** Of `apd:thm:runtime` only the counting step `card_lowSet_le_pow` is formalized. The branch-count half of
  `apd:thm:lightcone`, $\prod_\gamma 2^{w^\ast k_h^{\gamma-1}}$, and therefore its conclusion on the number of strings at the end
  of a step, is not.
* **`reachable`.** The weight half of `apd:thm:lightcone` is proved for the over-approximation `reachable` (Section 12).
* **Logarithmic rate.** The explicit rate of `eq:truncation_weight_bound` is not formalized; existence of the threshold is
  (Section 11).
* **Single-jump layer cumulation.** `apd:eq:layer_cumulation` is proved for abstract sequences only (Section 5); for Pauli layers
  the formalized statement is the majorant with all jump lengths (Section 6).
* **Examples in remarks.** The star layer of `apd:rmk:disjoint` (beyond the case $L = 2$ in the tests), the triple-jump example of
  `apd:rmk:multijump` and the numerical comparisons of `apd:rmk:comparison` are not formalized.

## Index of labels

| Label | Section | Relation |
|---|---|---|
| `def:norm` | [1](#1-definitions-and-the-model) | faithful |
| `def:pauli_basis` | [1](#1-definitions-and-the-model) | faithful |
| `def:support`, `def:pauli_weight` | [1](#1-definitions-and-the-model) | faithful for Pauli strings |
| `apd:eq:def_high_weight_norm` | [1](#1-definitions-and-the-model) | faithful |
| `apd:eq:suzuki` | [1](#1-definitions-and-the-model) | not formalized |
| `apd:eq:pauli_rotation_branch` | [2](#2-rotation-branch-rule) | stronger |
| `apd:thm:local_flow_k_local`, `apd:eq:worst_local_flow_k_local` | [3](#3-damped-local-norm-flow) | stronger |
| `apd:thm:layer_inflow`, `apd:eq:layer_inflow` | [4](#4-layer-inflow) | stronger |
| `apd:rmk:disjoint` | [4](#4-layer-inflow) | not formalized |
| `apd:cor:norm_cumulation_jump` (i) | [5](#5-cumulation) | faithful |
| `apd:cor:norm_cumulation_jump` (ii), `apd:eq:layer_cumulation` | [5](#5-cumulation) | weaker (abstract recursion only) |
| `apd:rmk:multijump` | [6](#6-multi-jump-recursion-and-first-passage-majorant) | faithful (definitions); its example is not formalized |
| `apd:thm:first_passage`, `apd:eq:multijump_recursion`, `apd:eq:composition_majorant` | [6](#6-multi-jump-recursion-and-first-passage-majorant) | faithful |
| `apd:thm:entry_factor`, `apd:eq:entry_bound` | [7](#7-entry-factor-and-part-factor) | faithful |
| `apd:thm:part_factor`, `apd:eq:part_factor` | [7](#7-entry-factor-and-part-factor) | faithful |
| `apd:thm:multijump_sum`, `apd:eq:multijump_sum` | [8](#8-summed-inflow-and-the-constant-c_0) | faithful |
| `apd:thm:c0_bound`, `apd:eq:multijump_factor`, `apd:eq:c0` | [8](#8-summed-inflow-and-the-constant-c_0) | faithful |
| `apd:eq:step_component` | [9](#9-telescoping-and-the-discarded-operator) | faithful |
| `apd:thm:triangle` | [9](#9-telescoping-and-the-discarded-operator) | identity faithful; conclusion weaker (norm level only) |
| `apd:eq:total_high_weight_norm` | [10](#10-the-truncation-error-bound) | first inequality faithful; second with a stronger prefactor and $c_0$ replaced by $2$ |
| `apd:eq:time_condition` | [10](#10-the-truncation-error-bound) | faithful, with $c_0$ replaced by $2$ |
| `apd:thm:one_step_truncation_error`, `apd:eq:total_truncation_error` | [10](#10-the-truncation-error-bound) | weaker (norm level only); at that level stronger in the prefactor |
| `apd:rmk:comparison` | [10](#10-the-truncation-error-bound) | the cancellation is formalized; the numerical comparisons are not |
| `apd:thm:truncation_threshold_entangled`, `eq:truncation_weight_bound` | [11](#11-threshold-existence) | weaker (existence, norm level) |
| `apd:thm:lightcone` | [12](#12-light-cone) | count and weight growth formalized (weight growth for `reachable`); branch count not formalized |
| `apd:thm:runtime` | [12](#12-light-cone) | not formalized beyond the counting step |
