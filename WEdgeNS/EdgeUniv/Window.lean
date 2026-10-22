import WEdgeNS.Model.HighProb
import WEdgeNS.Model.Transfer

/-!
# Composition of comparisons and the range of `s`
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Composition of two comparisons (proof of Theorem 3.7 after (5.28)):
shifts and additive errors add. -/
theorem sandwich_trans {F G K : ℝ → ℝ} (hK : Monotone K) {a b d : ℝ} (hd : a + b ≤ d)
    (h1 : ∀ s, G (s - a) - a ≤ F s ∧ F s ≤ G (s + a) + a)
    (h2 : ∀ s, K (s - b) - b ≤ G s ∧ G s ≤ K (s + b) + b) :
    ∀ s, K (s - d) - d ≤ F s ∧ F s ≤ K (s + d) + d := by
  intro s
  have l1 := (h1 s).1
  have u1 := (h1 s).2
  have l2 := (h2 (s - a)).1
  have u2 := (h2 (s + a)).2
  have m1 : K (s - d) ≤ K (s - a - b) := hK (by linarith)
  have m2 : K (s + a + b) ≤ K (s + d) := hK (by linarith)
  constructor <;> linarith

/-- `s ↦ P_GOE(N^{2/3}(λ_N - 2) ≤ s)` is monotone. -/
theorem monotone_goeCdf (N : ℕ) : Monotone (goeCdf N) := by
  intro s t hst
  unfold goeCdf edgeCdf
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => le_trans hω hst)

/-- The shift `2N^{-δ₀}` is at most `N^{-δ₀/2}` once `N ≥ 4^{1/δ₀}`. -/
theorem two_mul_rpow_neg_le {δ₀ : ℝ} (hδ : 0 < δ₀) {N : ℕ} (hN : (4 : ℝ) ^ (1 / δ₀) ≤ N) :
    2 * (N : ℝ) ^ (-δ₀) ≤ (N : ℝ) ^ (-(δ₀ / 2)) := by
  have h4 : (1 : ℝ) ≤ 4 ^ (1 / δ₀) := Real.one_le_rpow (by norm_num) (by positivity)
  have hN0 : (0 : ℝ) < N := by linarith
  have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (δ₀ / 2) := by
    have e : ((4 : ℝ) ^ (1 / δ₀)) ^ (δ₀ / 2) = 2 := by
      rw [← Real.rpow_mul (by norm_num), show 1 / δ₀ * (δ₀ / 2) = (1 / 2 : ℝ) by field_simp,
        show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h := Real.rpow_le_rpow (by positivity) hN (by positivity : (0 : ℝ) ≤ δ₀ / 2)
    rwa [e] at h
  have hsplit : (N : ℝ) ^ (-δ₀) = (N : ℝ) ^ (-(δ₀ / 2)) * (N : ℝ) ^ (-(δ₀ / 2)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have ha : 0 < (N : ℝ) ^ (-(δ₀ / 2)) := Real.rpow_pos_of_pos hN0 _
  have hinv : (N : ℝ) ^ (-(δ₀ / 2)) * (N : ℝ) ^ (δ₀ / 2) = 1 := by
    rw [← Real.rpow_add hN0]; simp
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h2 ha.le, ha]


/-- Abstract `s`-range lemma. Two distribution functions `F`, `G` with values in `[0,1]`, `G`
monotone, that compare on `[-W, W]` up to a shift `a ≥ 0` and an error `b`, and have tails of mass
at most `p` outside, compare on all of `ℝ` with shift and error `d ≥ max a (max b p)`. -/
theorem sandwich_extend_range {F G : ℝ → ℝ} (hF0 : ∀ s, 0 ≤ F s) (hF1 : ∀ s, F s ≤ 1)
    (hG0 : ∀ s, 0 ≤ G s) (hG1 : ∀ s, G s ≤ 1) (hGm : Monotone G) {W a b p d : ℝ}
    (ha : 0 ≤ a) (had : a ≤ d) (hbd : b ≤ d) (hpd : p ≤ d)
    (hFl : ∀ s, s < -W → F s ≤ p) (hGl : ∀ s, s < -W → G s ≤ p)
    (hFr : ∀ s, W ≤ s → 1 - p ≤ F s) (hGr : ∀ s, W ≤ s → 1 - p ≤ G s)
    (hwin : ∀ s, -W ≤ s → s ≤ W → G (s - a) - b ≤ F s ∧ F s ≤ G (s + a) + b) :
    ∀ s, G (s - d) - d ≤ F s ∧ F s ≤ G (s + d) + d := by
  intro s
  have hdn : 0 ≤ d := ha.trans had
  by_cases hs1 : s < -W
  · refine ⟨?_, ?_⟩
    · have := hGl (s - d) (by linarith)
      linarith [hF0 s]
    · linarith [hFl s hs1, hG0 (s + d)]
  · have hs1 : -W ≤ s := not_lt.1 hs1
    by_cases hs2 : W ≤ s
    · refine ⟨?_, ?_⟩
      · linarith [hFr s hs2, hG1 (s - d)]
      · linarith [hGr (s + d) (by linarith), hF1 s]
    · have hs2 : s < W := not_le.1 hs2
      obtain ⟨h1, h2⟩ := hwin s hs1 hs2.le
      have m1 : G (s - d) ≤ G (s - a) := hGm (by linarith)
      have m2 : G (s + a) ≤ G (s + d) := hGm (by linarith)
      constructor <;> linarith

/-- `s ↦ P(N^{2/3}(λ_N - 2) ≤ s)` is monotone. -/
theorem monotone_edgeCdfL {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) : Monotone (edgeCdfL L) := by
  intro s t hst
  have := isProbabilityMeasure_law hL
  unfold edgeCdfL
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => le_trans hω hst)

/-- `0 ≤ edgeCdfL L ≤ 1` for a probability law. -/
theorem edgeCdfL_mem_Icc {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (s : ℝ) :
    0 ≤ edgeCdfL L s ∧ edgeCdfL L s ≤ 1 := by
  have := isProbabilityMeasure_law hL
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold edgeCdfL
  have h := ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := L.law)
      (s := {ω | (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2) ≤ s}))
  simpa using h

/-- Left tail: if `|N^{2/3}(λ_N - 2)| ≤ W` on `A`, then `P(N^{2/3}(λ_N - 2) ≤ s) ≤ P(Aᶜ)` for
`s < -W`. -/
theorem edgeCdfL_le_of_lt_neg {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {A : Set (Entries N)}
    {W s : ℝ}
    (hA : ∀ ω ∈ A, |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ W)
    (hs : s < -W) : edgeCdfL L s ≤ (L.law Aᶜ).toReal := by
  have := isProbabilityMeasure_law hL
  unfold edgeCdfL
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
  intro hωA
  have h2 := (abs_le.1 (hA ω hωA)).1
  have hω' : (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2) ≤ s := hω
  linarith

/-- Right tail: if `|N^{2/3}(λ_N - 2)| ≤ W` on `A`, then `1 - P(Aᶜ) ≤ P(N^{2/3}(λ_N - 2) ≤ s)` for
`s ≥ W`. -/
theorem one_sub_le_edgeCdfL_of_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {A : Set (Entries N)}
    {W s : ℝ}
    (hA : ∀ ω ∈ A, |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ W)
    (hs : W ≤ s) : 1 - (L.law Aᶜ).toReal ≤ edgeCdfL L s := by
  have := isProbabilityMeasure_law hL
  unfold edgeCdfL
  have hsub : A ⊆ {ω | (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2) ≤ s} :=
    fun ω hω => (le_abs_self _).trans ((hA ω hω).trans hs)
  have h1 : (1 : ENNReal) ≤ L.law A + L.law Aᶜ := by
    calc (1 : ENNReal) = L.law Set.univ := (measure_univ).symm
      _ = L.law (A ∪ Aᶜ) := by rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
  have h3 : (1 : ℝ) ≤ (L.law A).toReal + (L.law Aᶜ).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h1
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at this
  have h4 := ENNReal.toReal_mono (measure_ne_top L.law _) (measure_mono (μ := L.law) hsub)
  linarith

/-- The range shift of the sandwiches: `φ^C + 2 ≤ φ^{C+1}` for `N ≥ 21` (there `φ ≥ 3`). -/
theorem phi_rpow_add_two_le {N : ℕ} (hN : 21 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    phi N ^ C + 2 ≤ phi N ^ (C + 1) := by
  have h21 : (21 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 3 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he := Real.exp_one_lt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    have h0 := Real.exp_pos 1
    calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by gcongr
      _ ≤ 21 := by norm_num
      _ ≤ N := h21
  have hphi : 3 ≤ phi N := hlog.trans (log_le_phi (by omega))
  have h1 : 1 ≤ phi N ^ C := Real.one_le_rpow (by linarith) hC
  rw [Real.rpow_add_one (by linarith)]
  nlinarith

/-! ## Nondegenerate instances -/

/-- `sandwich_trans` for `K` the clamp of `s` to `[0,1]`, `F = K`, `G = K(· + 1/20)`,
`a = b = 1/10`, `d = 1/5`. -/
example : ∀ s : ℝ, (fun s : ℝ => min (max s 0) 1) (s - 1 / 5) - 1 / 5 ≤ (fun s : ℝ => min (max s 0) 1) s ∧
    (fun s : ℝ => min (max s 0) 1) s ≤ (fun s : ℝ => min (max s 0) 1) (s + 1 / 5) + 1 / 5 := by
  have hK : Monotone (fun s : ℝ => min (max s 0) 1) := fun x y h => by
    simp only
    exact min_le_min (max_le_max h le_rfl) le_rfl
  refine sandwich_trans (F := fun s : ℝ => min (max s 0) 1)
    (G := fun s : ℝ => min (max (s + 1 / 20) 0) 1) hK (a := 1 / 10) (b := 1 / 10) (d := 1 / 5)
    (by norm_num) (fun s => ⟨?_, ?_⟩) (fun s => ⟨?_, ?_⟩)
  · have := hK (show s - 1 / 10 + 1 / 20 ≤ s by linarith)
    simp only at this ⊢
    linarith
  · have := hK (show s ≤ s + 1 / 10 + 1 / 20 by linarith)
    simp only at this ⊢
    linarith
  · have := hK (show s - 1 / 10 ≤ s + 1 / 20 by linarith)
    simp only at this ⊢
    linarith
  · have := hK (show s + 1 / 20 ≤ s + 1 / 10 by linarith)
    simp only at this ⊢
    linarith

/-- `monotone_goeCdf` at `N = 3`. -/
example : goeCdf 3 (-1) ≤ goeCdf 3 0 := monotone_goeCdf 3 (by norm_num)

/-- `two_mul_rpow_neg_le` at `δ₀ = 1/2`, `N = 81`: `2 / 9 ≤ 1 / 3`. -/
example : 2 * ((81 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ((81 : ℕ) : ℝ) ^ (-((1 / 2 : ℝ) / 2)) :=
  two_mul_rpow_neg_le (by norm_num) (by
    rw [show (1 : ℝ) / (1 / 2) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num)

/-- `sandwich_extend_range` at step functions (nonzero shifts, `W = 1`, `a = 1/5 < d = 1/4`). -/
example : ∀ s : ℝ,
    (if (1 / 10 : ℝ) ≤ s - 1 / 4 then (1 : ℝ) else 0) - 1 / 4 ≤ (if (0 : ℝ) ≤ s then (1 : ℝ) else 0) ∧
    (if (0 : ℝ) ≤ s then (1 : ℝ) else 0) ≤ (if (1 / 10 : ℝ) ≤ s + 1 / 4 then (1 : ℝ) else 0) + 1 / 4 := by
  have h := sandwich_extend_range
    (F := fun s : ℝ => if (0 : ℝ) ≤ s then (1 : ℝ) else 0)
    (G := fun s : ℝ => if (1 / 10 : ℝ) ≤ s then (1 : ℝ) else 0)
    (W := 1) (a := 1 / 5) (b := 1 / 10) (p := 0) (d := 1 / 4)
    (fun s => by split_ifs <;> norm_num) (fun s => by split_ifs <;> norm_num)
    (fun s => by split_ifs <;> norm_num) (fun s => by split_ifs <;> norm_num)
    (fun s t hst => by
      show (if (1 / 10 : ℝ) ≤ s then (1 : ℝ) else 0) ≤ if (1 / 10 : ℝ) ≤ t then (1 : ℝ) else 0
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (le_trans h1 hst) h2
      · norm_num
      · exact le_rfl)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s hs => by split_ifs <;> first | (exfalso; linarith) | norm_num)
    (fun s hs => by split_ifs <;> first | (exfalso; linarith) | norm_num)
    (fun s hs => by split_ifs <;> first | (exfalso; linarith) | norm_num)
    (fun s hs => by split_ifs <;> first | (exfalso; linarith) | norm_num)
    (fun s h1 h2 => by
      show (if (1 / 10 : ℝ) ≤ s - 1 / 5 then (1 : ℝ) else 0) - 1 / 10 ≤ (if (0 : ℝ) ≤ s then (1 : ℝ) else 0) ∧
        (if (0 : ℝ) ≤ s then (1 : ℝ) else 0) ≤ (if (1 / 10 : ℝ) ≤ s + 1 / 5 then (1 : ℝ) else 0) + 1 / 10
      split_ifs <;> first | (exfalso; linarith) | (constructor <;> norm_num))
  simpa using h

/-- `monotone_edgeCdfL` for the GOE law at `N = 3`. -/
example : edgeCdfL (goeLaws 3) (-1) ≤ edgeCdfL (goeLaws 3) 0 :=
  monotone_edgeCdfL (goeLaws_momentCond (le_refl 3)).isProb (by norm_num)

/-- `edgeCdfL_mem_Icc` for the GOE law at `N = 3`, `s = 0`. -/
example : 0 ≤ edgeCdfL (goeLaws 3) 0 ∧ edgeCdfL (goeLaws 3) 0 ≤ 1 :=
  edgeCdfL_mem_Icc (goeLaws_momentCond (le_refl 3)).isProb 0

/-- `edgeCdfL_le_of_lt_neg` at `N = 3`, the GOE law, and `A = {|N^{2/3}(λ_N - 2)| ≤ 1}`. -/
example : edgeCdfL (goeLaws 3) (-2) ≤ ((goeLaws 3).law
    {ω | |((3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ 1}ᶜ).toReal :=
  edgeCdfL_le_of_lt_neg (goeLaws_momentCond (le_refl 3)).isProb (fun ω hω => hω) (by norm_num)

/-- `one_sub_le_edgeCdfL_of_le` at `N = 3`, the GOE law, `A = {|N^{2/3}(λ_N - 2)| ≤ 1}`,
`s = W = 1`. -/
example : 1 - ((goeLaws 3).law
    {ω | |((3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ 1}ᶜ).toReal ≤
    edgeCdfL (goeLaws 3) 1 :=
  one_sub_le_edgeCdfL_of_le (goeLaws_momentCond (le_refl 3)).isProb (fun ω hω => hω) le_rfl

/-- `phi_rpow_add_two_le` at `N = 100`, `C = 1`. -/
example : phi 100 ^ (1 : ℝ) + 2 ≤ phi 100 ^ ((1 : ℝ) + 1) :=
  phi_rpow_add_two_le (N := 100) (by norm_num) (by norm_num)

#print axioms sandwich_trans
#print axioms monotone_goeCdf
#print axioms two_mul_rpow_neg_le
#print axioms sandwich_extend_range
#print axioms monotone_edgeCdfL
#print axioms edgeCdfL_mem_Icc
#print axioms edgeCdfL_le_of_lt_neg
#print axioms one_sub_le_edgeCdfL_of_le
#print axioms phi_rpow_add_two_le

end WEdgeNS
