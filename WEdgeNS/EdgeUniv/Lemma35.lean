import WEdgeNS.EdgeUniv.ClaimLargeQ
import WEdgeNS.EdgeUniv.LargeQInputs
import WEdgeNS.EdgeUniv.InputsComparison

/-!
# Edge universality for large support (Lemma 3.5)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Both laws of a pair of Lemma 3.5 are probability laws. -/
private lemma lemma35_prob (C0 φs : ℝ) :
    ∀ N (Lv Lw : EntryLaws N), LargeQGoePair C0 φs N Lv Lw → Lv.IsProb ∧ Lw.IsProb := by
  rintro N Lv Lw ⟨hv, rfl⟩
  exact ⟨hv.1.isProb, (goeLaws_isGenWigner N).isProb⟩

/-- The event of Lemma 5.6 holds with high probability for the first laws of the pairs of Lemma 3.5,
for every `C` from some `C₀` on. -/
private lemma lemma35_inputs_left {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ C₀ > (0 : ℝ), ∀ C ≥ C₀,
      HighProbOn 1 (fun N L => ∃ Lw, LargeQGoePair C0 φs N L Lw)
        (fun N _ => edgeInputEvent N C) := by
  obtain ⟨C₀, hC₀, h⟩ := edgeInput_largeQ hC0 hφs hφs'
  refine ⟨C₀, hC₀, fun C hC => ?_⟩
  obtain ⟨c, hc, C', hC', N0, h'⟩ := h C hC
  exact ⟨c, hc, C', hC', N0, fun N hN L ⟨Lw, hL, _⟩ => h' N hN L hL⟩

/-- The event of Lemma 5.6 holds with high probability for the second laws of the pairs of
Lemma 3.5 (the GOE), for every `C` from some `C₀` on. -/
private lemma lemma35_inputs_right (C0 φs : ℝ) :
    ∃ C₀ > (0 : ℝ), ∀ C ≥ C₀,
      HighProbOn 1 (fun N L => ∃ Lv, LargeQGoePair C0 φs N Lv L)
        (fun N _ => edgeInputEvent N C) := by
  obtain ⟨C₀, hC₀, h⟩ := edgeInput_goe
  refine ⟨C₀, hC₀, fun C hC => ?_⟩
  obtain ⟨c, hc, C', hC', N0, h'⟩ := h C hC
  exact ⟨c, hc, C', hC', N0, fun N hN L ⟨Lv, _, hL⟩ => h' N hN L hL⟩

/-- The Claim ((3.16)–(3.19)) is the comparison hypothesis (5.15) of Lemma 5.6 for the pairs of
Lemma 3.5, with `κ = φs - 1/3`. -/
private lemma lemma35_greenComp {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    GreenCompHyp (LargeQGoePair C0 φs) (φs - 1 / 3) := by
  intro CF
  obtain ⟨ε₀, hε₀, C, hC, h⟩ := green_comparison_largeQ (CF := CF) hC0 hφs hφs'
  refine ⟨ε₀, hε₀, C, hC, fun ε hε hε' => ?_⟩
  obtain ⟨N0, hN0⟩ := h ε hε hε'
  refine ⟨N0, fun N hN Lv Lw hp F hF hF' E₁ E₂ h1 h2 => ?_⟩
  obtain ⟨hv, rfl⟩ := hp
  have := (hN0 N hN Lv hv F hF hF').2 E₁ E₂ h1 h2
  rwa [show (1 : ℝ) / 3 - φs + C * ε = -(φs - 1 / 3) + C * ε by ring] at this

/-- Lemma 3.5: a law of Definition 2.1 with `E h_ii² ≤ (1 + C0)/N` and `|h_ij| ≤ N^{-φs}`
almost surely, `1/3 < φs ≤ 1/2`, against the GOE: (3.10) for every `s ∈ ℝ`, with `δ` and `N0`
depending only on `(C0, φs)`. -/
theorem edge_universality_largeQ {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, LargeQClass C0 φs N L → ∀ s : ℝ,
      goeCdf N (s - (N : ℝ) ^ (-δ)) - (N : ℝ) ^ (-δ) ≤ edgeCdfL L s ∧
      edgeCdfL L s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + (N : ℝ) ^ (-δ) := by
  obtain ⟨δ, hδ, N0, h⟩ := edge_universality_of_inputs (Pair := LargeQGoePair C0 φs)
    (by linarith) (lemma35_prob C0 φs) (lemma35_inputs_left hC0 hφs hφs')
    (lemma35_inputs_right C0 φs) (lemma35_greenComp hC0 hφs hφs')
  refine ⟨δ, hδ, N0, fun N hN L hL s => ?_⟩
  have h' := h N hN L (goeLaws N) ⟨hL, rfl⟩ s
  simpa only [goeCdf_eq_edgeCdfL] using h'

/-! ### Checks -/

open private lawA lawA_isGenWigner lawA_supp diagA
  from WEdgeNS.EdgeUniv.LargeQClass

/-- The pair predicate `LargeQGoePair 1 (2/5)` satisfies every hypothesis of
`edge_universality_of_inputs` with `κ = 2/5 - 1/3 > 0`, and it holds for the Rademacher laws
against the GOE at every `N ≥ 32` (generalized Wigner with diagonal variance `2/N`, entries bounded
by `N^{-2/5}`). -/
example : (0 : ℝ) < 2 / 5 - 1 / 3 ∧
    (∀ N (Lv Lw : EntryLaws N), LargeQGoePair 1 (2 / 5) N Lv Lw → Lv.IsProb ∧ Lw.IsProb) ∧
    (∃ C₀ > (0 : ℝ), ∀ C ≥ C₀, HighProbOn 1 (fun N L => ∃ Lw, LargeQGoePair 1 (2 / 5) N L Lw)
      (fun N _ => edgeInputEvent N C)) ∧
    (∃ C₀ > (0 : ℝ), ∀ C ≥ C₀, HighProbOn 1 (fun N L => ∃ Lv, LargeQGoePair 1 (2 / 5) N Lv L)
      (fun N _ => edgeInputEvent N C)) ∧
    GreenCompHyp (LargeQGoePair 1 (2 / 5)) (2 / 5 - 1 / 3) ∧
    (∀ᶠ N : ℕ in atTop, LargeQGoePair 1 (2 / 5) N (radLaws N) (goeLaws N)) :=
  ⟨by norm_num, lemma35_prob 1 (2 / 5),
    lemma35_inputs_left zero_le_one (by norm_num) (by norm_num), lemma35_inputs_right 1 (2 / 5),
    lemma35_greenComp zero_le_one (by norm_num) (by norm_num), by
      filter_upwards [eventually_ge_atTop 32] with N hN
      exact ⟨⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS hN⟩, rfl⟩⟩

/-- Lemma 3.5 at `C0 = 1`, `φs = 2/5` for the Rademacher laws: with one `δ > 0`, for all large `N`
and every `s`, (3.10) holds for `radLaws N` against the GOE. -/
example : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ s : ℝ,
    goeCdf N (s - (N : ℝ) ^ (-δ)) - (N : ℝ) ^ (-δ) ≤ edgeCdfL (radLaws N) s ∧
    edgeCdfL (radLaws N) s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + (N : ℝ) ^ (-δ) := by
  obtain ⟨δ, hδ, N0, h⟩ := edge_universality_largeQ (C0 := 1) (φs := 2 / 5) zero_le_one
    (by norm_num) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_ge_atTop (max N0 32)] with N hN s
  exact h N (le_trans (le_max_left _ _) hN) (radLaws N)
    ⟨radLaws_isGenWigner (by omega : 0 < N), radLaws_boundedSupportAS
      (le_trans (le_max_right _ _) hN)⟩ s

/-- Theorem 3.3 is Lemma 3.5 at `C0 = 1` (diagonal variance exactly `2/N`), for entries bounded by
`N^{-φs}` almost surely. -/
example {φs : ℝ} (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, L.IsGenWigner 1 →
      (∀ i, ∫ x, x ^ 2 ∂(L.diag i) = 2 / N) → L.BoundedSupportAS ((N : ℝ) ^ φs) → ∀ s : ℝ,
      goeCdf N (s - (N : ℝ) ^ (-δ)) - (N : ℝ) ^ (-δ) ≤ edgeCdfL L s ∧
      edgeCdfL L s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + (N : ℝ) ^ (-δ) := by
  obtain ⟨δ, hδ, N0, h⟩ := edge_universality_largeQ (C0 := 1) zero_le_one hφs hφs'
  exact ⟨δ, hδ, N0, fun N hN L hL _ hS => h N hN L ⟨hL, hS⟩⟩

/-- Lemma 3.5 and Theorem 3.3 at a nondegenerate point: `N = 1024`, `φs = 2/5`,
`C0 = 1`; diagonal variance `2/N` ≠ off-diagonal variance `1/N`; the support `N^{-2/5} = 1/16` is
attained by the diagonal entries. -/
example : LargeQClass 1 (2 / 5) 1024 lawA ∧ (∀ i, ∫ x, x ^ 2 ∂(lawA.diag i) = 2 / (1024 : ℕ)) := by
  refine ⟨⟨lawA_isGenWigner, lawA_supp⟩, fun _ => ?_⟩
  simp only [lawA]
  rw [integral_unifList]
  norm_num [diagA]

#print axioms edge_universality_largeQ

end WEdgeNS
