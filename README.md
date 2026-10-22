# Edge universality of Wigner matrices: a necessary and sufficient condition, in Lean 4

This repository is a Lean 4 + Mathlib formalization of

> J. O. Lee and J. Yin, *A necessary and sufficient condition for edge universality of Wigner matrices*, arXiv:1206.2251 (published in Duke Math. J. 163 (2014)).

The formalized source is arXiv:1206.2251v2. Both directions of Theorem 1.2 are formalized at k = 1 (the largest eigenvalue) for real symmetric Wigner matrices, the sufficiency direction in the GOE-comparison form (4.9) (see *Scope and the form of E2* below). Let x₁₂ be an off-diagonal entry. If s⁴ P(|x₁₂| ≥ s) → 0 (condition (1.4)), the distribution of N^{2/3}(λ_N − 2) is that of the GOE up to a shift N^{−δ} and an additive error ε_N → 0 (the comparison (4.9)). If (1.4) fails, then limsup_N P(λ_N ≥ 3) > 0 (this is (1.6)), and N^{2/3}(λ_N − 2) is not tight and has no limit in distribution. The development contains no `sorry`, and the endpoint theorems depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. The revised paper [`paper-revised/main.pdf`](paper-revised/main.pdf) is the version of arXiv:1206.2251v2 that matches the Lean proof; its Appendix A lists the changes.

**No external inputs.** Nothing is assumed. Every result that the paper takes from other works and uses in its proof — the local semicircle law, the norm bound, delocalization and rigidity of [15] (Lemma 3.1), the edge universality of [16] (Theorem 3.3, Lemma 3.5), the Green function comparison of [26] behind Lemma 5.6 and Theorem 3.6, and, in place of the finite-rank determinant criterion of [34], the matrix determinant lemma — is proved in this repository, from Mathlib only. To make this possible, some details of the proof differ from the version published in the *Duke Mathematical Journal*; see *Differences from the published proof* below.

- Lean: `leanprover/lean4:v4.36.0-rc1` (`lean-toolchain`).
- Mathlib: `v4.36.0-rc1`, revision `625d8914199bc567cca9b91f90e8e5afafa5ae51` (`lake-manifest.json`).

## Main theorems

All four theorems are in the namespace `WEdgeNS`. In each, `ν` is the law of the off-diagonal entries x_ij (i < j) and `ν'` is the law of the diagonal entries x_ii.

### Necessity: `WEdgeNS.E1`, `WEdgeNS.E1_not_tight`, `WEdgeNS.E1_no_limit`

File: `WEdgeNS/E1/Necessity.lean`.

```lean
theorem E1 (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | 3 ≤ lambdaMax (wignerMatrix N ω)}).toReal
```

If (1.4) fails, then P(λ_N ≥ 3) ≥ c for some c > 0 and infinitely many N. Equivalently, limsup_N P(λ_N ≥ 3) > 0, which is (1.6).

```lean
theorem E1_not_tight (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ,
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | K < |edgeScaled N ω|}).toReal
```

If (1.4) fails, there is c > 0 such that P(|N^{2/3}(λ_N − 2)| > K) ≥ c for every K and infinitely many N. In particular N^{2/3}(λ_N − 2) is not tight.

```lean
theorem E1_no_limit (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ s : ℝ, ContinuousAt (cdf μ) s →
        Tendsto (fun N => edgeCdf ν ν' N s) atTop (𝓝 (cdf μ s))
```

If (1.4) fails, N^{2/3}(λ_N − 2) converges in distribution to no probability law on ℝ. In particular it does not converge to the Tracy–Widom law, which is not defined in the Lean development.

### Sufficiency: `WEdgeNS.E2`

File: `WEdgeNS/E2/Sufficiency.lean`.

```lean
theorem E2 (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : TailCond ν) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ N in atTop, ∀ s : ℝ,
      goeCdf N (s - (N : ℝ) ^ (-δ)) - ε N ≤ edgeCdf ν ν' N s ∧
      edgeCdf ν ν' N s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + ε N
```

Write X_N = N^{2/3}(λ_N − 2). If (1.4) holds, there are δ > 0 and a sequence ε_N → 0 such that, for all sufficiently large N and all s ∈ ℝ,

P_GOE(X_N ≤ s − N^{−δ}) − ε_N ≤ P(X_N ≤ s) ≤ P_GOE(X_N ≤ s + N^{−δ}) + ε_N.

Both δ and the sequence ε are chosen before N. The sequence does not depend on s.

### Definitions

File: `WEdgeNS/Model/Wigner.lean`. For each N, the entries live on their own product space (`entryLaw`): the x_ii are i.i.d. with law `ν'`, the x_ij (i < j) are i.i.d. with law `ν`, and all of them are independent. The matrix is H_N = N^{−1/2}(x_ij) (`wignerMatrix`).

`WignerLaws` is the hypothesis of Definition 1.1 (real symmetric case). Both laws are probability measures and have finite second moments. `ν` has mean 0 and variance 1, and `ν'` has mean 0.

```lean
structure WignerLaws (ν ν' : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  prob' : IsProbabilityMeasure ν'
  sq_int : Integrable (fun x : ℝ => x ^ 2) ν
  sq_int' : Integrable (fun x : ℝ => x ^ 2) ν'
  mean : ∫ x, x ∂ν = 0
  var : ∫ x, x ^ 2 ∂ν = 1
  mean' : ∫ x, x ∂ν' = 0
```

`TailCond` is condition (1.4), lim_{s→∞} s⁴ P(|x₁₂| ≥ s) = 0. The negation `¬ TailCond ν` says that s⁴ P(|x₁₂| ≥ s) does not tend to 0; the paper writes this as "lim ≠ 0", and the limit need not exist.

```lean
def TailCond (ν : Measure ℝ) : Prop :=
  Tendsto (fun s : ℝ => s ^ 4 * (ν {x | s ≤ |x|}).toReal) atTop (𝓝 0)
```

λ_N is `lambdaMax`, the supremum of the real spectrum. For N ≥ 1 this is the largest eigenvalue of H_N. `edgeScaled N ω` is N^{2/3}(λ_N − 2), and `edgeCdf ν ν' N` is its distribution function.

```lean
noncomputable def lambdaMax {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  sSup (spectrum ℝ A)

noncomputable def edgeScaled (N : ℕ) (ω : Entries N) : ℝ :=
  (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (wignerMatrix N ω) - 2)

noncomputable def edgeCdf (ν ν' : Measure ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  (entryLaw ν ν' N {ω | edgeScaled N ω ≤ s}).toReal
```

`goeCdf N` is the same distribution function for the GOE of Definition 1.1, with x_ij ~ N(0, 1) and x_ii ~ N(0, 2).

```lean
noncomputable def goeCdf (N : ℕ) (s : ℝ) : ℝ :=
  edgeCdf (gaussianReal 0 1) (gaussianReal 0 2) N s
```

Each endpoint file also contains a compiled `example` at which all the hypotheses hold. For `E1`, it takes `ν' = ν` with `ν` the law given by `exists_wignerLaws_not_tailCond` (`WEdgeNS/E1/Tail.lean`). For `E2`, it is Rademacher off-diagonal entries with N(0, 2) diagonal entries.

## Scope and the form of E2

- The formalization covers k = 1 (the largest eigenvalue) and real symmetric matrices. The joint law of the k largest eigenvalues for k ≥ 2 and the Hermitian case are not formalized.
- `E2` is the GOE comparison (4.9) for H_N. The shift N^{−δ} is kept, for some δ > 0. The additive error of the paper, N^{−δ}, is replaced by a sequence ε_N → 0 that is uniform in s and fixed before N.
- **Why the error is ε_N rather than N^{−δ}.** Under (1.4) alone, an additive error N^{−δ} is false, for every δ > 0. The counterexample is a law with P(|x₁₂| ≥ s) of order 1/(s⁴ log s). It satisfies (1.4) but has no fourth moment, like the corrected example of Remark 1.3 of the revised paper; Remark 4.1 of the revised paper gives this argument. With N(0, 2) diagonal entries, some entry satisfies |h_ij| ≥ 4 with probability at least 1/(8192 log N), and together with small diagonal entries this forces λ_N > 7/2. For the GOE, P(λ_N ≥ 5/2) ≤ e^{−N/16}. So the lower half of (4.9) fails at s = N^{2/3} for all large N.
- If E|x₁₂|^{4+a} < ∞ and E|x₁₁|^{2+b} < ∞, one expects an error of the form N^{−δ′}; this is not proved here (Remark 4.1 of the revised paper).
- *Remark (not a formalized theorem).* Suppose the GOE distribution functions `goeCdf N` converge weakly to a distribution function F. Then `E2` and monotonicity give `edgeCdf ν ν' N s → F(s)` at every continuity point s of F, for every pair of laws satisfying `WignerLaws` and (1.4). By Tracy–Widom [45], F is the Tracy–Widom law F₁, which gives the sufficiency direction of Theorem 1.2 at k = 1. Neither the Tracy–Widom law nor this deduction is part of the Lean development.

## Differences from the published proof

The revised paper [`paper-revised/main.pdf`](paper-revised/main.pdf) (LaTeX source in `paper-revised/`) is arXiv:1206.2251v2 with the changes needed to match the Lean proof: its statements and proofs are the ones formalized here. This section summarizes the differences between the revised paper and the published version. Appendix A of the revised paper lists every change, with its location. The base text is arXiv:1206.2251v2; the version published in Duke Math. J. 163 (2014) is not in the repository, and differences between it and v2, if any, are not recorded.

- **Main theorem (Theorem 1.2).** It is stated for real symmetric Wigner matrices and the largest eigenvalue (k = 1). The Hermitian case and k ≥ 2 are mentioned in Remark 1.4, and they are not proved.
  - Sufficiency: (1.5) is the GOE comparison with a shift N^{−δ} and an additive error ε_N → 0 uniform in s, instead of convergence to the Tracy–Widom law. Remark 1.5 deduces the Tracy–Widom limit from it and [44, 45]; this deduction is outside the formalization.
  - Necessity: the hypothesis reads "s⁴ P(|x₁₂| ≥ s) does not tend to 0", and the theorem adds that N^{2/3}(λ_N − 2) is not tight and has no limit in distribution.
  - The example of Remark 1.3 is corrected (density c|x|^{−5}(log|x|)^{−1}). The new Remark 4.1 uses it to show that ε_N cannot be replaced by N^{−δ}.
- **Corrected intermediate statements.** None of them changes Theorem 1.2.
  - Definition 2.4: the bounded support condition in probability, with the tail-variance condition (2.4′), and its almost sure form.
  - Lemma 3.1: ζ-high probability, intersections in (3.2), (3.3) and (3.6), and a > 12ζ with an offset K in (3.7)–(3.8).
  - Theorem 3.3 and Lemma 3.5; Theorems 3.6 and 3.7; Lemma 3.8: entries bounded almost surely where the proof needs it, and explicit quantifiers.
  - Lemmas 5.1 and 5.2: two moments matched on the diagonal, an explicit support, and a corrected construction.
  - Lemmas 5.4–5.6: explicit quantifiers; Lemma 5.6 under weaker hypotheses.
  - Lemma 6.5: matched order 4 off the diagonal and 2 on it, 1 ≤ ζ ≤ φ², and products with conjugate and centred factors.
  - The iteration of Section 6 in sum and max form, and the new Lemma 6.6.
- **Changed proof routes.**
  - Section 4: (4.26) is proved by a one-sided barrier and a Rayleigh-quotient lower bound, without the GOE eigenvalue gap (4.41) or Remark 3.4. The determinant criterion of [34] is replaced by the matrix determinant lemma, proved in the text.
  - Lemma 3.1: the exceptional event of Definition 2.4 is removed by an explicit truncation, and the proof follows [15] at level ζ.
  - Lemma 3.5 is derived from Lemma 5.6, with the comparison step of [16].
  - Sections 5–6 follow the paper's own iterated expansion, with each step written out. Lemma 3.8 is proved from the sum form (6.33) of the iteration.
- **Misprints.** The misprints of the paper are corrected; they are listed in Appendix A and in the table below. The corrections to [15] and [16] are in Remark 3.9, and those to [26] are in the proof of Lemma 5.6.

## Misprints found in the paper and in cited works

These misprints are also listed in Appendix A of the revised paper. "Checked" records the text against which the correction was verified.

| Location | Printed | Corrected | Checked |
|---|---|---|---|
| (3.2), (3.3) | ⋃_{z∈S(C)} | ⋂: for all z ∈ S(C) and all i, j | against the PDF |
| (3.6) | ⋃_j | ⋂_j: for all j = 1, …, N | against the PDF |
| (3.12) | ⋃_j | ⋂_j: for all j | against the PDF |
| Definition 6.3, before (6.19), Lemmas 6.4–6.5, (6.53) | k ∈ ℝ, k ∈ ℝ^s, I^a_{b,c} ⊂ ℝ^a | ℕ, ℕ^s, ℕ^a | against the PDF |
| (6.104) | P_{γ,k}(R_ij R_ji) | P_{γ,k}(R_ij R̄_ij) | against the PDF |
| (6.105) | F^{(s)}(x_R) missing inside E; k_t ∈ I^{2s}_{3/φ,k} | F^{(s)}(x_R) inside E; k_t ∈ I²_{3/φ,\|k_t\|} | — |
| (4.22) | D̃_ij = 1_{H̃_ij H^C_ij ≤ 3/4} | 1_{\|H̃_ij H^C_ij\| ≤ 3/4} | against the PDF text |
| (6.85), second term on the left | η² Σ_ij G̃_ij G̃_ji | η² Σ_ij G̃_ij \overline{G̃_ij} | against the PDF text |
| [15], proof of Lemma 5.13, (5.95) | the quantity X | X needs an extra term (Nη)^{−1} (an omitted term in the proof, not a typographical slip) | — |
| [16], Lemma 6.8 | "assuming that a, b, i, j are all distinct" | b, d, i, j all distinct | against [16] arXiv v3 |
| [16], (6.75), second line | ½F″ E_bd (Q^{(0)}_1)² | ½F″ E_bd (Q^{(1)}_0)², as in the first line and (6.74) | against [16] arXiv v3 |

## Repository layout

The Lean sources are in `WEdgeNS/`, and the root module `WEdgeNS.lean` imports them all.

| Directory | Contents |
|---|---|
| `Model/` | The Wigner model of Definition 1.1, the GOE, the general entry-law classes (Definitions 2.1, 2.3, 2.4), and the ensembles of Sections 3–4 |
| `E1/` | The necessary condition: (1.6), non-tightness, and no limit in distribution |
| `Semicircle/` | The semicircle law, m_sc, classical locations, and counting and rigidity from the Stieltjes transform |
| `Resolvent/` | Resolvents, minors, finite resolvent expansions, and spectral consequences |
| `Perturbation/` | The finite-rank determinant criterion (4.32) and a one-sided barrier |
| `Probability/` | Product-space tools, high moments and large deviation bounds for linear, bilinear and quadratic forms |
| `Moments/` | Moment matching (Lemmas 5.1, 5.2 and Remark 5.3) |
| `LocalLaw/` | Lemma 3.1: the local semicircle law, norm bound, delocalization, rigidity, and bounds outside the spectrum |
| `Comparison/` | The Green function comparison for small support (Sections 5–6, Lemmas 3.8, 5.4, 5.5, 6.5, Theorem 3.6) |
| `EdgeUniv/` | Edge universality for large and small support (Lemma 3.5, Theorem 3.7) |
| `Reduction/` | Section 4: the cutoff, the coupling, the sparse perturbation, and the comparison of the edge of H_N with the cut-off matrix |
| `E2/` | The sufficient condition, in the form of the GOE comparison (4.9) |

All differences between the revised paper and the published version are listed in Appendix A of [`paper-revised/main.pdf`](paper-revised/main.pdf).

## Building

```bash
git clone https://github.com/JYin80/Lean-WEdgeNS_arXiv1206.2251.git
cd Lean-WEdgeNS_arXiv1206.2251
lake exe cache get   # download the compiled Mathlib
lake build
```

`lake build` also prints the `#print axioms` lines contained in the endpoint files. To check an endpoint theorem directly:

```bash
printf 'import WEdgeNS\n#print axioms WEdgeNS.E2\n' > /tmp/Axioms.lean
lake env lean /tmp/Axioms.lean
```

The expected output is

```
'WEdgeNS.E2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same check applies to `WEdgeNS.E1`, `WEdgeNS.E1_not_tight` and `WEdgeNS.E1_no_limit`.

## How it was made

The Lean code was written by Claude agents (Anthropic) under the direction of Jun Yin. The mathematics follows the paper and the cited works named above. Every theorem is checked by Lean.

## Citation and license

Please cite the paper:

```bibtex
@article{LeeYin2014,
  author  = {Lee, Ji Oon and Yin, Jun},
  title   = {A necessary and sufficient condition for edge universality of {W}igner matrices},
  journal = {Duke Mathematical Journal},
  volume  = {163},
  year    = {2014},
  eprint  = {1206.2251},
  archivePrefix = {arXiv}
}
```

License: Apache License 2.0; see [`LICENSE`](LICENSE).
