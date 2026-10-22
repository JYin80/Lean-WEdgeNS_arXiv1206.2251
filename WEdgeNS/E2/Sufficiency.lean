import WEdgeNS.Reduction.Comparison
import WEdgeNS.EdgeUniv.Thm37

/-!
# Edge universality under the tail condition
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- E2 (Theorem 1.2, sufficiency, `k = 1`, GOE-comparison form (4.9)). -/
theorem E2 (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : TailCond ν) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ N in atTop, ∀ s : ℝ,
      goeCdf N (s - (N : ℝ) ^ (-δ)) - ε N ≤ edgeCdf ν ν' N s ∧
      edgeCdf ν ν' N s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + ε N := by
  have := hW.prob
  have := hW.prob'
  have he0 : (0 : ℝ) < 1 / 100 := by norm_num
  have he30 : (1 / 100 : ℝ) < 1 / 30 := by norm_num
  have he2 : (1 / 100 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨C1, N1, hcls⟩ := truncLawsNorm_smallQClass hW h14 he0 he2
  obtain ⟨d, hd, N2, h37⟩ :=
    edge_universality_smallQ (C1 := C1) (φs := 3 * (1 / 100 : ℝ) / 4) (by norm_num)
  have hclose := tendsto_coupleLaw_edge_close hW h14 he0 he30
  set p : ℕ → ℝ := fun N : ℕ => (coupleLaw ν ν' (1 / 100) N {u | (N : ℝ) ^ (-(1 : ℝ) / 24) <
      |edgeScaled N (coupleMap (cutoffMean ν ((N : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))))
          (cutoffMean ν' ((N : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)))) u) -
        (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (normSmall ν (1 / 100) u) - 2)|}).toReal with hp
  set δ : ℝ := min d (1 / 24) / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-d)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop
  have hpowδ : Tendsto (fun N : ℕ => (N : ℝ) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  refine ⟨δ, hδ, fun N => (N : ℝ) ^ (-d) + p N, by simpa using hpow.add hclose, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (max N1 N2)),
    eventually_cutoff_mass_ne_zero (ν := ν) (ν' := ν') he2,
    hpowδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N hN hmass hhalf
  obtain ⟨hS, hS'⟩ := hmass
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hN
  have hx0 : (0 : ℝ) < N := by linarith
  -- the shifts: `N^{-1/24} + N^{-d} ≤ N^{-δ}`
  have hshift : (N : ℝ) ^ (-(1 : ℝ) / 24) + (N : ℝ) ^ (-d) ≤ (N : ℝ) ^ (-δ) := by
    have h1 : (N : ℝ) ^ (-(1 : ℝ) / 24) ≤ (N : ℝ) ^ (-δ - δ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by
        have := min_le_right d (1 / 24); rw [hδdef]; linarith)
    have h2 : (N : ℝ) ^ (-d) ≤ (N : ℝ) ^ (-δ - δ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by
        have := min_le_left d (1 / 24); rw [hδdef]; linarith)
    have h3 : (N : ℝ) ^ (-δ - δ) = (N : ℝ) ^ (-δ) * (N : ℝ) ^ (-δ) := by
      rw [sub_eq_add_neg, Real.rpow_add hx0]
    have h4 : 0 ≤ (N : ℝ) ^ (-δ) := Real.rpow_nonneg hx0.le _
    nlinarith
  have := isProbabilityMeasure_coupleLaw (ε := 1 / 100) hS hS'
  set P := coupleLaw ν ν' (1 / 100) N with hP
  set XH : CoupleSpace N → ℝ := fun u => edgeScaled N (coupleMap
    (cutoffMean ν ((N : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))))
    (cutoffMean ν' ((N : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)))) u) with hXH
  set XS : CoupleSpace N → ℝ := fun u =>
    (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (normSmall ν (1 / 100) u) - 2) with hXS
  set t : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 24) with ht
  have hbad : p N = (P {u | t < |XH u - XS u|}).toReal := rfl
  -- comparison of the two edge statistics on the coupling space
  have hsand : ∀ a b : ℝ, (∀ u, |XH u - XS u| ≤ t → (XS u ≤ a → XH u ≤ b)) →
      (P {u | XS u ≤ a}).toReal ≤ (P {u | XH u ≤ b}).toReal + p N := by
    intro a b hab
    rw [hbad, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    refine ENNReal.toReal_mono (by finiteness) ((measure_mono ?_).trans (measure_union_le _ _))
    intro u hu
    by_cases h : t < |XH u - XS u|
    · exact Or.inr h
    · exact Or.inl (hab u (not_lt.mp h) hu)
  have hsand' : ∀ a b : ℝ, (∀ u, |XH u - XS u| ≤ t → (XH u ≤ a → XS u ≤ b)) →
      (P {u | XH u ≤ a}).toReal ≤ (P {u | XS u ≤ b}).toReal + p N := by
    intro a b hab
    rw [hbad, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    refine ENNReal.toReal_mono (by finiteness) ((measure_mono ?_).trans (measure_union_le _ _))
    intro u hu
    by_cases h : t < |XH u - XS u|
    · exact Or.inr h
    · exact Or.inl (hab u (not_lt.mp h) hu)
  intro s
  have hH : ∀ s, edgeCdf ν ν' N s = (P {u | XH u ≤ s}).toReal := fun s =>
    edgeCdf_eq_coupleLaw hS hS' s
  have hS0 : ∀ s, edgeCdfL (truncLawsNorm ν ν' (1 / 100) N) s = (P {u | XS u ≤ s}).toReal :=
    fun s => edgeCdfL_truncLawsNorm_eq hS hS' s
  have hL := hcls N hN1
  constructor
  · -- lower bound
    have h1 := (h37 N hN2 _ hL (s - t)).1
    have h2 := hsand (s - t) s (fun u hu h => by
      have := (abs_le.mp hu).2; linarith)
    have h3 := monotone_goeCdf N (show s - (N : ℝ) ^ (-δ) ≤ s - t - (N : ℝ) ^ (-d) by linarith)
    rw [hH, ← hS0] at *
    linarith
  · -- upper bound
    have h1 := (h37 N hN2 _ hL (s + t)).2
    have h2 := hsand' s (s + t) (fun u hu h => by
      have := (abs_le.mp hu).1; linarith)
    have h3 := monotone_goeCdf N (show s + t + (N : ℝ) ^ (-d) ≤ s + (N : ℝ) ^ (-δ) by linarith)
    rw [hH, ← hS0] at *
    linarith

#print axioms E2

/-- `E2` at Rademacher off-diagonal entries and `N(0, 2)` diagonal entries: all hypotheses
hold at once, with non-Gaussian off-diagonal entries. -/
example := E2 rademacher (gaussianReal 0 2) rademacher_wignerLaws rademacher_tailCond

end WEdgeNS
