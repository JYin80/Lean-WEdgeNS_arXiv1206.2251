import WEdgeNS.EdgeUniv.Lemma35
import WEdgeNS.EdgeUniv.SmallQBridge
import WEdgeNS.Comparison.GreenCompare

/-!
# Edge universality for small support (Theorem 3.7)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The comparison hypothesis (5.15) of Lemma 5.6 for the pairs of Theorem 3.7, with rate
`N^{-φs+Cε}`: Lemma 5.5 applies to a test function with four derivatives, since it needs three. -/
private lemma thm37_greenCompHyp {C1 φs : ℝ} (hφs : 0 < φs) :
    GreenCompHyp (SmallQPair C1 φs) φs := by
  intro CF
  obtain ⟨ε₀, hε₀, C, hC, h⟩ := green_comparison_smallQ (CF := CF) (C1 := C1) hφs
  refine ⟨ε₀, hε₀, C, hC, fun ε hε hε' => ?_⟩
  obtain ⟨N0, hN0⟩ := h ε hε hε'
  refine ⟨N0, fun N hN Lv Lw hp F hF hF' E₁ E₂ h1 h2 => ?_⟩
  have hF3 : ContDiff ℝ 3 F := hF.of_le (by norm_num)
  have hF3' : ∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF :=
    fun n hn x => hF' n (by simp only [Finset.mem_Icc] at hn ⊢; omega) x
  exact (hN0 N hN Lv Lw hp.1 hp.2 F hF3 hF3').2 E₁ E₂ h1 h2

/-- Theorem 3.7: (3.14) for every `s ∈ ℝ`, with `δ` and `N0` depending only on
`(C1, φs)`, uniformly over the laws of Theorem 3.6 with the almost-sure support condition. -/
theorem edge_universality_smallQ {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, SmallQClass C1 φs N L → ∀ s : ℝ,
      goeCdf N (s - (N : ℝ) ^ (-δ)) - (N : ℝ) ^ (-δ) ≤ edgeCdfL L s ∧
      edgeCdfL L s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + (N : ℝ) ^ (-δ) := by
  obtain ⟨δ1, hδ1, N1, h1⟩ := edge_universality_of_inputs hφs
    (fun _ _ _ h => SmallQPair.isProb h) (edgeInput_smallQPair_v hφs)
    edgeInput_smallQPair_w (thm37_greenCompHyp (C1 := C1) hφs)
  obtain ⟨N2, h2⟩ := SmallQPair.largeQClass (C1 := C1) (φs := φs)
  obtain ⟨δ2, hδ2, N3, h3⟩ := edge_universality_largeQ (C0 := max C1 1) (φs := 2 / 5)
    (le_max_of_le_right zero_le_one) (by norm_num) (by norm_num)
  set δ0 := min δ1 δ2 with hδ0
  have hδ0pos : 0 < δ0 := lt_min hδ1 hδ2
  refine ⟨δ0 / 2, by positivity,
    max (max N1 N2) (max N3 (max 3 ⌈(4 : ℝ) ^ (1 / δ0)⌉₊)), fun N hN L hL s => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN1, hN2⟩, hN3, hN4, hN5⟩ := hN
  obtain ⟨Lw, hLw⟩ : ∃ Lw, L.IsMomentMatch Lw C1 := exists_isMomentMatch hN4 hL.1
  have hp : SmallQPair C1 φs N L Lw := ⟨hL, hLw⟩
  have hA := h1 N hN1 L Lw hp
  have hB := h3 N hN3 Lw (h2 N hN2 L Lw hp)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have e1 : (N : ℝ) ^ (-δ1) ≤ (N : ℝ) ^ (-δ0) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by simp [hδ0])
  have e2 : (N : ℝ) ^ (-δ2) ≤ (N : ℝ) ^ (-δ0) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by simp [hδ0])
  have e3 := two_mul_rpow_neg_le hδ0pos ((Nat.le_ceil _).trans (by exact_mod_cast hN5))
  have hd : (N : ℝ) ^ (-δ1) + (N : ℝ) ^ (-δ2) ≤ (N : ℝ) ^ (-(δ0 / 2)) := by linarith
  exact sandwich_trans (monotone_goeCdf N) hd hA hB s

/-! ### Compiled checks -/

open private pm_radLaws_class from WEdgeNS.Comparison.PairMoments
open private lawV lawW lawV_momentCond lawV_supp lawVW_isMomentMatch
  from WEdgeNS.Comparison.Classes

/-- A law of the class of Theorem 3.7 at a nondegenerate point, together with a Lemma 5.1 match:
`N = 16`, `C1 = 2`, `φs = 1/4`. The off-diagonal entries of `lawV` take the extreme values
`±N^{-1/4} = ±1/2` with probability `1/5`. -/
example : (0 : ℝ) < 1 / 4 ∧ SmallQClass 2 (1 / 4) 16 lawV ∧ SmallQPair 2 (1 / 4) 16 lawV lawW :=
  ⟨by norm_num, ⟨lawV_momentCond, lawV_supp⟩,
    ⟨⟨lawV_momentCond, lawV_supp⟩, lawVW_isMomentMatch⟩⟩

/-- The conclusion of Theorem 3.7 holds for the Rademacher laws at every large `N`
(`C1 = 2`, `φs = 2/5`, off-diagonal entries `±N^{-1/2}`, diagonal entries `±√2 N^{-1/2}`). -/
example : ∃ δ : ℝ, 0 < δ ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ s : ℝ,
    goeCdf N (s - (N : ℝ) ^ (-δ)) - (N : ℝ) ^ (-δ) ≤ edgeCdfL (radLaws N) s ∧
    edgeCdfL (radLaws N) s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + (N : ℝ) ^ (-δ) := by
  obtain ⟨δ, hδ, N0, h⟩ := edge_universality_smallQ (C1 := 2) (φs := 2 / 5) (by norm_num)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 pm_radLaws_class
  exact ⟨δ, hδ, max N0 N1, fun N hN s =>
    h N (le_of_max_le_left hN) (radLaws N) (hN1 N (le_of_max_le_right hN)).1 s⟩

#print axioms edge_universality_smallQ

end WEdgeNS
