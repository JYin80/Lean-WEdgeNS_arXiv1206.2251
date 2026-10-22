import WEdgeNS.Comparison.Taylor

/-!
# Green function comparison for small support (Lemma 5.5)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Telescoping (6.85) along the lexicographic interpolation (3.21): if every swap changes the
expectation of `G` by at most `w(e) b`, then the expectations under `Lv` and `Lw` differ by at
most `(3/2) b`, since the weights `w(e)` of (6.102)–(6.103) sum to at most `3/2`. -/
private lemma greenCompare_swap_sum {N : ℕ} {Lv Lw : EntryLaws N} (G : Entries N → ℝ) {b : ℝ}
    (hb : 0 ≤ b)
    (h : ∀ e : Fin N ⊕ OffDiag N,
      |∫ ω, G ω ∂(interp (lexPos N) (lexPos N e) Lv Lw).law -
        ∫ ω, G ω ∂(interp (lexPos N) (lexPos N e - 1) Lv Lw).law| ≤ swapWeight N e * b) :
    |∫ ω, G ω ∂Lv.law - ∫ ω, G ω ∂Lw.law| ≤ 3 / 2 * b := by
  set g : ℕ → ℝ := fun γ => ∫ ω, G ω ∂(interp (lexPos N) γ Lv Lw).law with hg
  have htel := sub_eq_sum_lexPos (N := N) (fun γ => ((g γ : ℝ) : ℂ))
  have htop : g (N * (N + 1) / 2) = ∫ ω, G ω ∂Lv.law := by
    simp only [hg, interp_lexPos_top]
  have hzero : g 0 = ∫ ω, G ω ∂Lw.law := by
    simp only [hg, interp_lexPos_zero]
  rw [← htop, ← hzero]
  have h1 : |g (N * (N + 1) / 2) - g 0| =
      ‖((g (N * (N + 1) / 2) : ℝ) : ℂ) - ((g 0 : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, htel]
  calc ‖∑ e : Fin N ⊕ OffDiag N, (((g (lexPos N e) : ℝ) : ℂ) - ((g (lexPos N e - 1) : ℝ) : ℂ))‖
      ≤ ∑ e : Fin N ⊕ OffDiag N,
          ‖((g (lexPos N e) : ℝ) : ℂ) - ((g (lexPos N e - 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ e : Fin N ⊕ OffDiag N, swapWeight N e * b := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact h e
    _ = (∑ e : Fin N ⊕ OffDiag N, swapWeight N e) * b := by rw [Finset.sum_mul]
    _ ≤ 3 / 2 * b := mul_le_mul_of_nonneg_right (sum_swapWeight_le N) hb

/-- Lemma 5.5, (5.14) and (5.15), with the constant of (5.12) renamed `CF`:
`ε₀` and `C` depend on `(CF, C1, φs)` only. -/
theorem green_comparison_smallQ {CF C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ (Lv Lw : EntryLaws N), SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 →
      ∀ F : ℝ → ℝ, ContDiff ℝ 3 F →
        (∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (etaEdge N ε ^ 2 * ∑ i, ∑ j,
                ‖resolventC (symOfEntries ω) ⟨E, etaEdge N ε⟩ i j‖ ^ 2) ∂Lv.law -
            ∫ ω, F (etaEdge N ε ^ 2 * ∑ i, ∑ j,
                ‖resolventC (symOfEntries ω) ⟨E, etaEdge N ε⟩ i j‖ ^ 2) ∂Lw.law| ≤
            (N : ℝ) ^ (-φs + C * ε)) ∧
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (N * ∫ y in E₁..E₂,
                (stieltjesM (symOfEntries ω) ⟨y, etaEdge N ε⟩).im) ∂Lv.law -
            ∫ ω, F (N * ∫ y in E₁..E₂,
                (stieltjesM (symOfEntries ω) ⟨y, etaEdge N ε⟩).im) ∂Lw.law| ≤
            (N : ℝ) ^ (-φs + C * ε)) := by
  obtain ⟨ε₀, hε₀, C, hC, h⟩ := swap_green_le (CF := CF) (C1 := C1) hφs
  refine ⟨ε₀, hε₀, C + 1, by linarith, fun ε hε hεε₀ => ?_⟩
  obtain ⟨N0, hN0⟩ := h ε hε hεε₀
  have hev : ∀ᶠ N : ℕ in atTop, (3 / 2 : ℝ) ≤ (N : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  refine ⟨max N0 N1, fun N hN Lv Lw hv hw F hF hFd => ?_⟩
  have hNε : (3 / 2 : ℝ) ≤ (N : ℝ) ^ ε := hN1 N (le_of_max_le_right hN)
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, Nat.cast_zero, Real.zero_rpow hε.ne'] at hNε; norm_num at hNε
    · exact_mod_cast h0
  have hfin : (3 / 2 : ℝ) * (N : ℝ) ^ (-φs + C * ε) ≤ (N : ℝ) ^ (-φs + (C + 1) * ε) := by
    rw [show -φs + (C + 1) * ε = ε + (-φs + C * ε) by ring, Real.rpow_add hNpos ε (-φs + C * ε)]
    exact mul_le_mul_of_nonneg_right hNε (Real.rpow_nonneg hNpos.le _)
  have key : ∀ X ∈ edgeObs N ε,
      |∫ ω, F (X (symOfEntries ω)) ∂Lv.law - ∫ ω, F (X (symOfEntries ω)) ∂Lw.law| ≤
        (N : ℝ) ^ (-φs + (C + 1) * ε) := fun X hX =>
    (greenCompare_swap_sum (fun ω => F (X (symOfEntries ω))) (Real.rpow_nonneg hNpos.le _)
      (hN0 N (le_of_max_le_left hN) Lv Lw hv hw F hF hFd X hX)).trans hfin
  exact ⟨fun E hE => key (obsPoint N ε E) (Or.inl ⟨E, hE, rfl⟩),
    fun E₁ E₂ h₁ h₂ => key (obsInt N ε E₁ E₂) (Or.inr ⟨E₁, E₂, h₁, h₂, rfl⟩)⟩

/-! ### Compiled checks

The hypotheses of `green_comparison_smallQ` hold together: for every large `N` with the Rademacher
laws matched with themselves (`C1 = 2`, `φs = 2/5`), and at `N = 16` with two different laws
`lawV ≠ lawW` (`C1 = 2`, `φs = 1/4`, `ε = 1/10`), `F = sin` with `CF = 1`, `E = 2` and a window
`[E₁, E₂]` of positive length inside `I_ε`. -/

open private pm_radLaws_class from WEdgeNS.Comparison.PairMoments
open private lawV lawW lawV_momentCond lawV_supp lawVW_isMomentMatch diagV diagW
  from WEdgeNS.Comparison.Classes

/-- The class `SmallQClass 2 (2/5) N` and its matched pairs are nonempty for every large `N`. -/
example : ∀ᶠ N : ℕ in atTop, ∃ Lv Lw : EntryLaws N,
    SmallQClass 2 (2 / 5) N Lv ∧ Lv.IsMomentMatch Lw 2 := by
  filter_upwards [pm_radLaws_class] with N h
  exact ⟨radLaws N, radLaws N, h⟩

/-- All hypotheses of `green_comparison_smallQ` at one point: `N = 16`, `C1 = 2`, `φs = 1/4`,
`ε = 1/10`, the different laws `lawV`, `lawW`, `F = sin`, `CF = 1`, the energy `E = 2` of (5.14)
and the energies `E₁ < E₂` of (5.15) at the two ends of `I_ε`. -/
example : (0 : ℝ) < 1 / 4 ∧ (0 : ℝ) < 1 / 10 ∧
    SmallQClass 2 (1 / 4) 16 lawV ∧ lawV.IsMomentMatch lawW 2 ∧ lawV ≠ lawW ∧
    ContDiff ℝ 3 Real.sin ∧
    (∀ n ∈ Finset.Icc 1 3, ∀ x, |iteratedDeriv n Real.sin x| ≤ 1 * (1 + |x|) ^ (1 : ℝ)) ∧
    |(2 : ℝ) - 2| ≤ ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) ∧
    |(2 - ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10)) - 2| ≤
      ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) ∧
    |(2 + ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10)) - 2| ≤
      ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) ∧
    2 - ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) <
      2 + ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) := by
  have hp : (0 : ℝ) < ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨by norm_num, by norm_num, ⟨lawV_momentCond, lawV_supp⟩, lawVW_isMomentMatch, ?_,
    sin_regularity_cond.1, sin_regularity_cond.2, by simpa using hp.le, ?_, ?_, by linarith⟩
  · intro h
    have h0 := congrArg (fun L : EntryLaws 16 => L.diag 0 {0}) h
    simp only [lawV, lawW, unifList, diagV, diagW, Measure.smul_apply,
      listSum_apply _ (measurableSet_singleton (0 : ℝ))] at h0
    norm_num [Set.indicator] at h0
  · rw [show 2 - ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) - 2 =
      -((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) by ring, abs_neg, abs_of_pos hp]
  · rw [show 2 + ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) - 2 =
      ((16 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 10) by ring, abs_of_pos hp]

#print axioms green_comparison_smallQ

end WEdgeNS
