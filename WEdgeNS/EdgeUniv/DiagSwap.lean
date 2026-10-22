import WEdgeNS.EdgeUniv.RBound
import WEdgeNS.EdgeUniv.WardReduction

/-!
# One diagonal replacement in the Claim
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### The expansion (3.30) for a diagonal entry -/

/-- The off-diagonal sum `Σ_{i ≠ j} |G_ij|²` of (3.33). -/
private def diagSwapOff {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else ‖G i j‖ ^ 2

/-- The coefficient of `v` in the expansion of `Σ_{i ≠ j} |S_ij|²` around `R` for `V = v E^{aa}`:
`Σ_{i ≠ j} -2 Re(conj(R_ij) R_ia R_aj)`. -/
private def diagSwapLin {N : ℕ} (a : Fin N) (G : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else -2 * (starRingEnd ℂ (G i j) * (G i a * G a j)).re

/-- `(A V M)_ij = A_ia v M_aj` for `V = v E^{aa}`. -/
private lemma diagSwap_mul_entryMat_mul {N : ℕ} (a : Fin N) (v : ℝ)
    (A M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (A * (v • entryMat (Sum.inl a)).map (fun x : ℝ => (x : ℂ)) * M) i j = A i a * v * M a j := by
  have hV : ∀ k l, ((v • entryMat (Sum.inl a)).map (fun x : ℝ => (x : ℂ))) k l =
      if k = a then (if l = a then (v : ℂ) else 0) else 0 := by
    intro k l
    by_cases hk : k = a <;> by_cases hl : l = a <;> simp [entryMat, entryPairs, hk, hl]
  simp only [Matrix.mul_apply, hV, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, ite_mul, zero_mul]

/-- (3.30) for `e = (a, a)`: `S = R - v R E^{aa} R + v² R E^{aa} R E^{aa} S` entrywise, with
`S = G(H)`, `R = G(Q)` and `v = h_aa`. -/
private lemma diagSwap_expansion {N : ℕ} (a : Fin N) (ω : Entries N) {z : ℂ} (hz : 0 < z.im)
    (i j : Fin N) :
    resolventC (symOfEntries ω) z i j =
      resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) z i j -
        (entryVal (Sum.inl a) ω : ℂ) * resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) z i a *
          resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) z a j +
        (entryVal (Sum.inl a) ω : ℂ) ^ 2 *
          resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) z i a *
          resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) z a a *
          resolventC (symOfEntries ω) z a j := by
  set e : Fin N ⊕ OffDiag N := Sum.inl a with he
  have hH := symOfEntries_isHermitian ω
  have hQ := symOfEntries_isHermitian (zeroEntry e ω)
  have hdec := symOfEntries_eq_zeroEntry_add e ω
  set v := entryVal e ω with hv
  have hVH : (v • entryMat e).IsHermitian := by
    have : v • entryMat e = symOfEntries ω - symOfEntries (zeroEntry e ω) := by
      rw [hdec]; abel
    rw [this]
    exact hH.sub hQ
  have hexp := resolventC_expansion_right hQ hVH hz 1
  rw [← hdec] at hexp
  set S := resolventC (symOfEntries ω) z with hS
  set R := resolventC (symOfEntries (zeroEntry e ω)) z with hR
  set Vc := (v • entryMat e).map (fun x : ℝ => (x : ℂ)) with hVc
  have h2 : (-(R * Vc)) ^ 2 * S = R * Vc * (R * Vc * S) := by
    rw [neg_sq, pow_two, Matrix.mul_assoc]
  have hentry := congrFun (congrFun hexp i) j
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, Matrix.one_mul, pow_one, h2,
    Matrix.add_apply, Matrix.add_apply, Matrix.neg_mul, Matrix.neg_apply,
    diagSwap_mul_entryMat_mul a v R R i j, diagSwap_mul_entryMat_mul a v R (R * Vc * S) i j,
    diagSwap_mul_entryMat_mul a v R S a j] at hentry
  rw [hentry]
  ring

/-! ### Deterministic bounds on the event -/

/-- The row sums of the entry bounds `2` (diagonal) and `P` (off-diagonal). -/
private lemma diagSwap_sum_bd {N : ℕ} (a : Fin N) {P : ℝ} (hP0 : 0 ≤ P) :
    (∑ i : Fin N, (if i = a then (2 : ℝ) else P)) ≤ 2 + N * P ∧
    (∑ j : Fin N, (if a = j then (2 : ℝ) else P)) ≤ 2 + N * P ∧
    (∑ i : Fin N, (if i = a then (2 : ℝ) else P) ^ 2) ≤ 4 + N * P ^ 2 ∧
    (∑ j : Fin N, (if a = j then (2 : ℝ) else P) ^ 2) ≤ 4 + N * P ^ 2 := by
  have h1 : ∀ i : Fin N, (if i = a then (2 : ℝ) else P) ≤ (if i = a then 2 else 0) + P := by
    intro i; split_ifs <;> linarith
  have h2 : ∀ j : Fin N, (if a = j then (2 : ℝ) else P) ≤ (if a = j then 2 else 0) + P := by
    intro j; split_ifs <;> linarith
  have h3 : ∀ i : Fin N, (if i = a then (2 : ℝ) else P) ^ 2 ≤ (if i = a then 4 else 0) + P ^ 2 := by
    intro i; split_ifs <;> nlinarith
  have h4 : ∀ j : Fin N, (if a = j then (2 : ℝ) else P) ^ 2 ≤ (if a = j then 4 else 0) + P ^ 2 := by
    intro j; split_ifs <;> nlinarith
  refine ⟨(Finset.sum_le_sum fun i _ => h1 i).trans ?_,
    (Finset.sum_le_sum fun j _ => h2 j).trans ?_,
    (Finset.sum_le_sum fun i _ => h3 i).trans ?_, (Finset.sum_le_sum fun j _ => h4 j).trans ?_⟩ <;>
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq]

/-- A double sum over `i ≠ j` of terms bounded by `c₁ b_ia b_aj + c₂ b_ia² b_aj²`. -/
private lemma diagSwap_sum_le {N : ℕ} (a : Fin N) {P c₁ c₂ : ℝ} (hP0 : 0 ≤ P) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hNP : 2 ≤ (N : ℝ) * P) (hNP2 : 4 ≤ (N : ℝ) * P ^ 2)
    {g : Fin N → Fin N → ℝ}
    (hg : ∀ i j, i ≠ j → |g i j| ≤
      c₁ * ((if i = a then 2 else P) * (if a = j then 2 else P)) +
        c₂ * ((if i = a then 2 else P) ^ 2 * (if a = j then 2 else P) ^ 2)) :
    |∑ i, ∑ j, if i = j then 0 else g i j| ≤
      4 * c₁ * (N : ℝ) ^ 2 * P ^ 2 + 4 * c₂ * (N : ℝ) ^ 2 * P ^ 4 := by
  obtain ⟨s1, s2, s3, s4⟩ := diagSwap_sum_bd a hP0
  set b1 : Fin N → ℝ := fun i => if i = a then 2 else P with hb1
  set b2 : Fin N → ℝ := fun j => if a = j then 2 else P with hb2
  have hb1n : ∀ i, 0 ≤ b1 i := fun i => by simp only [hb1]; split_ifs <;> linarith
  have hb2n : ∀ j, 0 ≤ b2 j := fun j => by simp only [hb2]; split_ifs <;> linarith
  have hpt : ∀ i j, |(if i = j then 0 else g i j)| ≤
      c₁ * (b1 i * b2 j) + c₂ * (b1 i ^ 2 * b2 j ^ 2) := by
    intro i j
    by_cases hij : i = j
    · simp only [hij, ite_true, abs_zero]
      have := hb1n j; have := hb2n j
      positivity
    · simp only [hij, ite_false]
      exact hg i j hij
  have hsum : ∑ i, ∑ j, (c₁ * (b1 i * b2 j) + c₂ * (b1 i ^ 2 * b2 j ^ 2)) =
      c₁ * ((∑ i, b1 i) * (∑ j, b2 j)) + c₂ * ((∑ i, b1 i ^ 2) * (∑ j, b2 j ^ 2)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hA : (∑ i, b1 i) * (∑ j, b2 j) ≤ 4 * (N : ℝ) ^ 2 * P ^ 2 := by
    have e1 : ∑ i, b1 i ≤ 2 * (N * P) := by linarith
    have e2 : ∑ j, b2 j ≤ 2 * (N * P) := by linarith
    have n1 : 0 ≤ ∑ i, b1 i := Finset.sum_nonneg fun i _ => hb1n i
    have n2 : 0 ≤ ∑ j, b2 j := Finset.sum_nonneg fun j _ => hb2n j
    calc (∑ i, b1 i) * (∑ j, b2 j) ≤ (2 * (N * P)) * (2 * (N * P)) :=
          mul_le_mul e1 e2 n2 (by linarith)
      _ = 4 * (N : ℝ) ^ 2 * P ^ 2 := by ring
  have hB : (∑ i, b1 i ^ 2) * (∑ j, b2 j ^ 2) ≤ 4 * (N : ℝ) ^ 2 * P ^ 4 := by
    have e1 : ∑ i, b1 i ^ 2 ≤ 2 * (N * P ^ 2) := by linarith
    have e2 : ∑ j, b2 j ^ 2 ≤ 2 * (N * P ^ 2) := by linarith
    have n1 : 0 ≤ ∑ i, b1 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have n2 : 0 ≤ ∑ j, b2 j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    calc (∑ i, b1 i ^ 2) * (∑ j, b2 j ^ 2) ≤ (2 * (N * P ^ 2)) * (2 * (N * P ^ 2)) :=
          mul_le_mul e1 e2 n2 (by linarith)
      _ = 4 * (N : ℝ) ^ 2 * P ^ 4 := by ring
  calc |∑ i, ∑ j, if i = j then 0 else g i j|
      ≤ ∑ i, ∑ j, |(if i = j then 0 else g i j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (c₁ * (b1 i * b2 j) + c₂ * (b1 i ^ 2 * b2 j ^ 2)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = _ := hsum
    _ ≤ c₁ * (4 * (N : ℝ) ^ 2 * P ^ 2) + c₂ * (4 * (N : ℝ) ^ 2 * P ^ 4) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hc₁) (mul_le_mul_of_nonneg_left hB hc₂)
    _ = _ := by ring

/-- `|w + d|² - |w|² = 2 Re(conj(w) d) + |d|²`. -/
private lemma diagSwap_normSq_add (w d : ℂ) :
    ‖w + d‖ ^ 2 - ‖w‖ ^ 2 = 2 * (starRingEnd ℂ w * d).re + ‖d‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  have : (w * starRingEnd ℂ d).re = (starRingEnd ℂ w * d).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  rw [this]; ring

/-- The expansion (3.30) in the off-diagonal sum of (3.33), deterministically: if
`S = R - v R E^{aa} R + v² R E^{aa} R E^{aa} S`, all entries of `R` and `S` are bounded by `2` on
the diagonal and by `P ≤ 1` off it, and `|v| ≤ 1/2`, then
`|Σ_{i≠j} |S_ij|² - Σ_{i≠j} |R_ij|²| ≤ 32 |v| N² P³`, and removing the linear term
`v Σ_{i ≠ j} -2 Re(conj(R_ij) R_ia R_aj)` leaves at most `32 v² N² P³`. -/
private lemma diagSwap_off_sub_le {N : ℕ} (a : Fin N) {R S : Matrix (Fin N) (Fin N) ℂ} {v P : ℝ}
    (hexp : ∀ i j, S i j = R i j - (v : ℂ) * R i a * R a j +
      (v : ℂ) ^ 2 * R i a * R a a * S a j)
    (hR : ∀ k l, ‖R k l‖ ≤ if k = l then 2 else P) (hS : ∀ k l, ‖S k l‖ ≤ if k = l then 2 else P)
    (hv : |v| ≤ 1 / 2) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hNP : 2 ≤ (N : ℝ) * P)
    (hNP2 : 4 ≤ (N : ℝ) * P ^ 2) :
    |diagSwapOff S - diagSwapOff R| ≤ 32 * |v| * (N : ℝ) ^ 2 * P ^ 3 ∧
    |diagSwapOff S - diagSwapOff R - v * diagSwapLin a R| ≤ 32 * v ^ 2 * (N : ℝ) ^ 2 * P ^ 3 := by
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have hv2 : v ^ 2 ≤ |v| / 2 := by
    rw [← sq_abs]; nlinarith
  have hRaa : ‖R a a‖ ≤ 2 := by simpa using hR a a
  -- the increment `δ_ij = S_ij - R_ij` and its two parts
  have hδ : ∀ i j, S i j = R i j + (-((v : ℂ) * (R i a * R a j)) +
      (v : ℂ) ^ 2 * R i a * R a a * S a j) := fun i j => by rw [hexp]; ring
  have hbd : ∀ i j, ‖-((v : ℂ) * (R i a * R a j)) + (v : ℂ) ^ 2 * R i a * R a a * S a j‖ ≤
      2 * |v| * ((if i = a then 2 else P) * (if a = j then 2 else P)) := by
    intro i j
    have h1 := hR i a
    have h2 := hR a j
    have h3 := hS a j
    have n1 : 0 ≤ ‖R i a‖ := norm_nonneg _
    have n2 : 0 ≤ ‖R a j‖ := norm_nonneg _
    have n3 : 0 ≤ ‖S a j‖ := norm_nonneg _
    have hb1 : 0 ≤ (if i = a then (2 : ℝ) else P) := by split_ifs <;> linarith
    have hb2 : 0 ≤ (if a = j then (2 : ℝ) else P) := by split_ifs <;> linarith
    calc ‖-((v : ℂ) * (R i a * R a j)) + (v : ℂ) ^ 2 * R i a * R a a * S a j‖
        ≤ |v| * (‖R i a‖ * ‖R a j‖) + v ^ 2 * ‖R i a‖ * ‖R a a‖ * ‖S a j‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ |v| * ((if i = a then 2 else P) * (if a = j then 2 else P)) +
          (|v| / 2) * (if i = a then 2 else P) * 2 * (if a = j then 2 else P) := by
          gcongr
      _ = 2 * |v| * ((if i = a then 2 else P) * (if a = j then 2 else P)) := by ring
  have hoffR : ∀ i j, i ≠ j → ‖R i j‖ ≤ P := fun i j h => by simpa [h] using hR i j
  refine ⟨?_, ?_⟩
  · have hdiff : diagSwapOff S - diagSwapOff R =
        ∑ i, ∑ j, if i = j then 0 else (‖S i j‖ ^ 2 - ‖R i j‖ ^ 2) := by
      unfold diagSwapOff
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [hdiff]
    refine (diagSwap_sum_le a hP0 (c₁ := 4 * |v| * P) (c₂ := 4 * v ^ 2) (by positivity)
      (by positivity) hNP hNP2 fun i j hij => ?_).trans ?_
    · rw [hδ i j, diagSwap_normSq_add]
      set d := -((v : ℂ) * (R i a * R a j)) + (v : ℂ) ^ 2 * R i a * R a a * S a j
      have hd := hbd i j
      have hr := hoffR i j hij
      have hre : |(starRingEnd ℂ (R i j) * d).re| ≤ ‖R i j‖ * ‖d‖ := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj]
      have hd0 : 0 ≤ ‖d‖ := norm_nonneg _
      have hX : 0 ≤ (if i = a then (2 : ℝ) else P) * (if a = j then 2 else P) := by
        split_ifs <;> positivity
      calc |2 * (starRingEnd ℂ (R i j) * d).re + ‖d‖ ^ 2|
          ≤ 2 * (‖R i j‖ * ‖d‖) + ‖d‖ ^ 2 := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg ‖d‖)]
            linarith
        _ ≤ 2 * (P * (2 * |v| * ((if i = a then 2 else P) * (if a = j then 2 else P)))) +
            (2 * |v| * ((if i = a then 2 else P) * (if a = j then 2 else P))) ^ 2 := by
            gcongr
        _ = 4 * |v| * P * ((if i = a then 2 else P) * (if a = j then 2 else P)) +
            4 * v ^ 2 * ((if i = a then 2 else P) ^ 2 * (if a = j then 2 else P) ^ 2) := by
            rw [mul_pow, mul_pow, sq_abs]; ring
    · have hP4 : P ^ 4 ≤ P ^ 3 := pow_le_pow_of_le_one hP0 hP1 (by norm_num)
      have hN : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
      have h1 : v ^ 2 * P ^ 4 ≤ |v| * P ^ 3 := by
        have : v ^ 2 ≤ |v| := by linarith
        exact mul_le_mul this hP4 (by positivity) hv0
      nlinarith
  · have hdiff : diagSwapOff S - diagSwapOff R - v * diagSwapLin a R =
        ∑ i, ∑ j, if i = j then 0 else
          (‖S i j‖ ^ 2 - ‖R i j‖ ^ 2 -
            v * (-2 * (starRingEnd ℂ (R i j) * (R i a * R a j)).re)) := by
      unfold diagSwapOff diagSwapLin
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [hdiff]
    refine (diagSwap_sum_le a hP0 (c₁ := 4 * v ^ 2 * P) (c₂ := 4 * v ^ 2) (by positivity)
      (by positivity) hNP hNP2 fun i j hij => ?_).trans ?_
    · rw [hδ i j, diagSwap_normSq_add]
      set d := -((v : ℂ) * (R i a * R a j)) + (v : ℂ) ^ 2 * R i a * R a a * S a j
      have hd := hbd i j
      have hr := hoffR i j hij
      have hlin : 2 * (starRingEnd ℂ (R i j) * d).re -
          v * (-2 * (starRingEnd ℂ (R i j) * (R i a * R a j)).re) =
          2 * (starRingEnd ℂ (R i j) * ((v : ℂ) ^ 2 * R i a * R a a * S a j)).re := by
        simp only [d, mul_add, Complex.add_re, mul_neg, Complex.neg_re]
        have : (starRingEnd ℂ (R i j) * ((v : ℂ) * (R i a * R a j))).re =
            v * (starRingEnd ℂ (R i j) * (R i a * R a j)).re := by
          rw [show starRingEnd ℂ (R i j) * ((v : ℂ) * (R i a * R a j)) =
            (v : ℂ) * (starRingEnd ℂ (R i j) * (R i a * R a j)) by ring, Complex.re_ofReal_mul]
        rw [this]; ring
      have hre : |(starRingEnd ℂ (R i j) * ((v : ℂ) ^ 2 * R i a * R a a * S a j)).re| ≤
          P * (v ^ 2 * (if i = a then 2 else P) * 2 * (if a = j then 2 else P)) := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj]
        have h1 := hR i a
        have h3 := hS a j
        have hb1 : 0 ≤ (if i = a then (2 : ℝ) else P) := by split_ifs <;> linarith
        have hm : ‖(v : ℂ) ^ 2 * R i a * R a a * S a j‖ ≤
            v ^ 2 * (if i = a then 2 else P) * 2 * (if a = j then 2 else P) := by
          simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
          gcongr
        exact mul_le_mul hr hm (norm_nonneg _) hP0
      have hd0 : 0 ≤ ‖d‖ := norm_nonneg _
      calc |2 * (starRingEnd ℂ (R i j) * d).re + ‖d‖ ^ 2 -
            v * (-2 * (starRingEnd ℂ (R i j) * (R i a * R a j)).re)|
          = |2 * (starRingEnd ℂ (R i j) * ((v : ℂ) ^ 2 * R i a * R a a * S a j)).re +
              ‖d‖ ^ 2| := by rw [← hlin]; ring_nf
        _ ≤ 2 * (P * (v ^ 2 * (if i = a then 2 else P) * 2 * (if a = j then 2 else P))) +
            (2 * |v| * ((if i = a then 2 else P) * (if a = j then 2 else P))) ^ 2 := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg ‖d‖)]
            gcongr
        _ = 4 * v ^ 2 * P * ((if i = a then 2 else P) * (if a = j then 2 else P)) +
            4 * v ^ 2 * ((if i = a then 2 else P) ^ 2 * (if a = j then 2 else P) ^ 2) := by
            rw [mul_pow, mul_pow, sq_abs]; ring
    · have hP4 : P ^ 4 ≤ P ^ 3 := pow_le_pow_of_le_one hP0 hP1 (by norm_num)
      have hN : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
      have h1 : v ^ 2 * P ^ 4 ≤ v ^ 2 * P ^ 3 := mul_le_mul_of_nonneg_left hP4 (sq_nonneg _)
      nlinarith

/-! ### One law: the Taylor step (3.35)–(3.37) -/

/-- A continuous function of a bounded measurable random variable is integrable. -/
private lemma diagSwap_integrable_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {F : ℝ → ℝ} (hF : Continuous F) {a : α → ℝ} (ha : Measurable a)
    {R : ℝ} (hR : ∀ ω, |a ω| ≤ R) : Integrable (fun ω => F (a ω)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.of_bound (hF.measurable.comp ha).aestronglyMeasurable C
    (Eventually.of_forall fun ω => ?_)
  exact hC _ (abs_le.1 (hR ω))

/-- `E F(a) - E F(b)` for `b` the functional of `Q` and `a` that of `H = Q + v E^{aa}`, when the
linear term `E[F′(b) l v]` vanishes: on `Ω` the second-order Taylor remainder (3.35) and the error
`a - b - v l`; off `Ω` the bound `Φ (1 + |v|)` with `|v| ≤ T + v²/T`. -/
private lemma diagSwap_core {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {F : ℝ → ℝ} {CF : ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {a b l v : α → ℝ} (ha : Measurable a) (hb : Measurable b) (hl : Measurable l)
    (hv : Measurable v) (hv2 : Integrable (fun ω => v ω ^ 2) μ) {Kv : ℝ}
    (hKv : ∫ ω, v ω ^ 2 ∂μ ≤ Kv) {A : ℝ} (hA : 0 ≤ A) (haA : ∀ ω, |a ω| ≤ A)
    (hbA : ∀ ω, |b ω| ≤ A) (hlA : ∀ ω, |l ω| ≤ A)
    (hmean : ∫ ω, iteratedDeriv 1 F (b ω) * l ω * v ω ∂μ = 0)
    {Ω : Set α} {R₁ G D1 D2 : ℝ} (hG0 : 0 ≤ G) (hD2 : 0 ≤ D2)
    (hG : ∀ ζ, |ζ| ≤ R₁ → |iteratedDeriv 1 F ζ| ≤ G ∧ |iteratedDeriv 2 F ζ| ≤ G)
    (hgood : ∀ ω ∈ Ω, |a ω| ≤ R₁ ∧ |b ω| ≤ R₁ ∧ |a ω - b ω| ≤ D1 ∧
      |a ω - b ω - v ω * l ω| ≤ D2)
    {T : ℝ} (hT : 0 < T) :
    |∫ ω, F (a ω) ∂μ - ∫ ω, F (b ω) ∂μ| ≤
      G * (D1 ^ 2 / 2 + D2) +
        CF * (1 + A) ^ CF * (2 * A) * ((1 + T) * (μ Ωᶜ).toReal + Kv / T) := by
  have hCF : 0 ≤ CF := by
    have := hF 1 (by simp) 0
    simpa using (abs_nonneg _).trans this
  set K := CF * (1 + A) ^ CF with hK
  have hK0 : 0 ≤ K := mul_nonneg hCF (Real.rpow_nonneg (by linarith) _)
  have hF1 : ∀ ζ : ℝ, |ζ| ≤ A → |iteratedDeriv 1 F ζ| ≤ K := fun ζ hζ =>
    abs_iteratedDeriv_le_of_abs_le hF hζ 1 (by simp)
  have hFc : Continuous F := hF4.continuous
  have hF1c : Continuous (iteratedDeriv 1 F) := hF4.continuous_iteratedDeriv 1 (by norm_num)
  have hFa := diagSwap_integrable_comp (μ := μ) hFc ha haA
  have hFb := diagSwap_integrable_comp (μ := μ) hFc hb hbA
  have hvi : Integrable v μ := by
    refine Integrable.mono' (hv2.add (integrable_const 1)) hv.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    change ‖v ω‖ ≤ v ω ^ 2 + 1
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (v ω), sq_abs (v ω)]
  have hlin : Integrable (fun ω => iteratedDeriv 1 F (b ω) * l ω * v ω) μ := by
    refine Integrable.mono' (hvi.norm.const_mul (K * A))
      (((hF1c.measurable.comp hb).mul hl).mul hv).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 := hF1 (b ω) (hbA ω)
    have h2 := hlA ω
    have : |iteratedDeriv 1 F (b ω)| * |l ω| ≤ K * A :=
      mul_le_mul h1 h2 (abs_nonneg _) hK0
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  set Rf : α → ℝ := fun ω => F (a ω) - F (b ω) - iteratedDeriv 1 F (b ω) * l ω * v ω with hRf
  have hRfi : Integrable Rf μ := (hFa.sub hFb).sub hlin
  have hsplit : ∫ ω, F (a ω) ∂μ - ∫ ω, F (b ω) ∂μ = ∫ ω, Rf ω ∂μ := by
    have h1 : ∫ ω, Rf ω ∂μ = ∫ ω, (F (a ω) - F (b ω)) ∂μ -
        ∫ ω, iteratedDeriv 1 F (b ω) * l ω * v ω ∂μ := integral_sub (hFa.sub hFb) hlin
    rw [h1, hmean, sub_zero, integral_sub hFa hFb]
  set T' := toMeasurable μ Ωᶜ with hT'
  have hmeas : MeasurableSet T' := measurableSet_toMeasurable μ _
  set δ := G * (D1 ^ 2 / 2 + D2) with hδ
  have hδ0 : 0 ≤ δ := mul_nonneg hG0 (by positivity)
  set Φ := K * (2 * A) with hΦ
  have hΦ0 : 0 ≤ Φ := mul_nonneg hK0 (by linarith)
  have hpt : ∀ ω, |Rf ω| ≤ δ + Φ * ((1 + T) * T'.indicator 1 ω + v ω ^ 2 / T) := by
    intro ω
    have hvT : |v ω| ≤ T + v ω ^ 2 / T := by
      have h2 : (|v ω| - T) * T ≤ v ω ^ 2 := by
        nlinarith [sq_nonneg (|v ω| - T), sq_abs (v ω), abs_nonneg (v ω)]
      have := (le_div_iff₀ hT).2 h2
      linarith
    by_cases h : ω ∈ T'
    · simp only [Set.indicator_of_mem h, Pi.one_apply, mul_one]
      have hab : |F (a ω) - F (b ω)| ≤ K * (2 * A) := by
        have hmv := (show |F (a ω) - F (b ω)| ≤ K * |a ω - b ω| by
          have hd : Differentiable ℝ F := hF4.differentiable (by norm_num)
          have := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := Set.Icc (-A) A)
            (C := K) (x := b ω) (y := a ω) (fun x _ => hd.differentiableAt)
            (fun x hx => by
              rw [← iteratedDeriv_one]
              exact hF1 x (abs_le.2 hx)) (convex_Icc _ _) (abs_le.1 (hbA ω)) (abs_le.1 (haA ω))
          simpa [Real.norm_eq_abs] using this)
        have hd : |a ω - b ω| ≤ 2 * A := by
          have := abs_sub (a ω) (b ω)
          linarith [haA ω, hbA ω]
        exact hmv.trans (mul_le_mul_of_nonneg_left hd hK0)
      have hl3 : |iteratedDeriv 1 F (b ω) * l ω * v ω| ≤ K * A * |v ω| := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hF1 (b ω) (hbA ω)) (hlA ω) (abs_nonneg _) hK0) (abs_nonneg _)
      have hR : |Rf ω| ≤ K * (2 * A) + K * A * |v ω| := by
        simp only [hRf]
        exact (abs_sub _ _).trans (add_le_add hab hl3)
      have hKA : K * A * |v ω| ≤ Φ * (T + v ω ^ 2 / T) := by
        have : K * A ≤ Φ := by rw [hΦ]; nlinarith
        exact mul_le_mul this hvT (abs_nonneg _) hΦ0
      have : Φ * ((1 + T) + v ω ^ 2 / T) = Φ + Φ * (T + v ω ^ 2 / T) := by ring
      linarith
    · have hω : ω ∈ Ω := by
        by_contra hn
        exact h (subset_toMeasurable μ _ hn)
      simp only [Set.indicator_of_notMem h, mul_zero, zero_add]
      obtain ⟨h1, h2, h3, h4⟩ := hgood ω hω
      obtain ⟨ζ, hζ, hT2⟩ := taylor_second hF4 (b ω) (a ω)
      have hζR : |ζ| ≤ R₁ := by
        have a1 := abs_le.1 h1
        have a2 := abs_le.1 h2
        rcases Set.mem_uIcc.1 hζ with ⟨z1, z2⟩ | ⟨z1, z2⟩ <;>
          exact abs_le.2 ⟨by linarith, by linarith⟩
      have hRe : Rf ω = iteratedDeriv 2 F ζ * (a ω - b ω) ^ 2 / 2 +
          iteratedDeriv 1 F (b ω) * (a ω - b ω - v ω * l ω) := by
        simp only [hRf]; rw [hT2]; ring
      have hq : 0 ≤ Φ * (v ω ^ 2 / T) := mul_nonneg hΦ0 (div_nonneg (sq_nonneg _) hT.le)
      have hsq : (a ω - b ω) ^ 2 ≤ D1 ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h3 2
      have hmain : |Rf ω| ≤ δ := by
        rw [hRe, hδ]
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg (a ω - b ω))]
        have g2 := (hG ζ hζR).2
        have g1 := (hG (b ω) h2).1
        have e1 : |iteratedDeriv 2 F ζ| * (a ω - b ω) ^ 2 / 2 ≤ G * (D1 ^ 2 / 2) := by
          have := mul_le_mul g2 hsq (sq_nonneg _) hG0
          linarith
        have e2 : |iteratedDeriv 1 F (b ω)| * |a ω - b ω - v ω * l ω| ≤ G * D2 :=
          mul_le_mul g1 h4 (abs_nonneg _) hG0
        linarith
      linarith
  clear_value δ Φ
  have hind : Integrable (T'.indicator (1 : α → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hmeas
  have hbdi : Integrable (fun ω => δ + Φ * ((1 + T) * T'.indicator 1 ω + v ω ^ 2 / T)) μ :=
    (integrable_const δ).add (((hind.const_mul (1 + T)).add (hv2.div_const T)).const_mul Φ)
  rw [hsplit]
  calc |∫ ω, Rf ω ∂μ| = ‖∫ ω, Rf ω ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ ω, ‖Rf ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (δ + Φ * ((1 + T) * T'.indicator 1 ω + v ω ^ 2 / T)) ∂μ :=
        integral_mono hRfi.norm hbdi fun ω => by simpa [Real.norm_eq_abs] using hpt ω
    _ = δ + Φ * ((1 + T) * (μ Ωᶜ).toReal + (∫ ω, v ω ^ 2 ∂μ) / T) := by
        have i1 : Integrable (fun ω => (1 + T) * T'.indicator (1 : α → ℝ) ω) μ :=
          hind.const_mul (1 + T)
        have i2 : Integrable (fun ω => v ω ^ 2 / T) μ := hv2.div_const T
        have i3 : Integrable (fun ω => Φ * ((1 + T) * T'.indicator (1 : α → ℝ) ω +
            v ω ^ 2 / T)) μ := (i1.add i2).const_mul Φ
        rw [integral_add (integrable_const δ) i3, integral_const_mul, integral_add i1 i2,
          integral_const_mul, integral_div, integral_indicator_one hmeas, integral_const]
        simp [measureReal_def, hT', measure_toMeasurable]
    _ ≤ δ + Φ * ((1 + T) * (μ Ωᶜ).toReal + Kv / T) := by
        gcongr

/-! ### Continuity and deterministic sizes -/

private lemma diagSwap_continuous_off {N : ℕ} {η : ℝ} (hη : 0 < η) :
    Continuous (fun p : Entries N × ℝ =>
      diagSwapOff (resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ))) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
    by_cases h : i = j
    · simp only [h, ite_true]; exact continuous_const
    · simp only [h, ite_false]; exact (continuous_resolventC_symOfEntries_prod hη i j).norm.pow 2

private lemma diagSwap_continuous_lin {N : ℕ} (a : Fin N) {η : ℝ} (hη : 0 < η) :
    Continuous (fun p : Entries N × ℝ =>
      diagSwapLin a (resolventC (symOfEntries p.1) (⟨p.2, η⟩ : ℂ))) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
    by_cases h : i = j
    · simp only [h, ite_true]; exact continuous_const
    · simp only [h, ite_false]
      refine continuous_const.mul (Complex.continuous_re.comp ?_)
      exact ((Complex.continuous_conj.comp (continuous_resolventC_symOfEntries_prod hη i j)).mul
        ((continuous_resolventC_symOfEntries_prod hη i a).mul
          (continuous_resolventC_symOfEntries_prod hη a j)))

private lemma diagSwap_continuous_off_y {N : ℕ} {η : ℝ} (hη : 0 < η) (ω : Entries N) :
    Continuous fun y : ℝ => diagSwapOff (resolventC (symOfEntries ω) ⟨y, η⟩) := by
  have hc : Continuous (fun y : ℝ => (ω, y)) := continuous_const.prodMk continuous_id
  have h := (diagSwap_continuous_off (N := N) hη).comp hc
  exact h

private lemma diagSwap_continuous_lin_y {N : ℕ} (a : Fin N) {η : ℝ} (hη : 0 < η)
    (ω : Entries N) :
    Continuous fun y : ℝ => diagSwapLin a (resolventC (symOfEntries ω) ⟨y, η⟩) := by
  have hc : Continuous (fun y : ℝ => (ω, y)) := continuous_const.prodMk continuous_id
  have h := (diagSwap_continuous_lin a hη).comp hc
  exact h

private lemma diagSwap_continuous_zeroEntry {N : ℕ} (a : Fin N) :
    Continuous (zeroEntry (Sum.inl a) : Entries N → Entries N) := by
  change Continuous fun ω : Entries N => (Function.update ω.1 a 0, ω.2)
  exact (continuous_fst.update a continuous_const).prodMk continuous_snd

/-- `0 ≤ Σ_{i ≠ j} |G_ij|² ≤ N² η⁻²`. -/
private lemma diagSwap_off_bound {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ diagSwapOff (resolventC H z) ∧
      diagSwapOff (resolventC H z) ≤ (N : ℝ) ^ 2 * (1 / z.im) ^ 2 := by
  have hb := norm_resolventC_apply_le hH hz
  refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity,
    ?_⟩
  calc diagSwapOff (resolventC H z) ≤ ∑ _i : Fin N, ∑ _j : Fin N, (1 / z.im) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs
        · positivity
        · exact pow_le_pow_left₀ (norm_nonneg _) (hb i j) 2
    _ = (N : ℝ) ^ 2 * (1 / z.im) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `|Σ_{i ≠ j} -2 Re(conj(G_ij) G_ia G_aj)| ≤ 2 N² η⁻³`. -/
private lemma diagSwap_lin_bound {N : ℕ} (a : Fin N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    |diagSwapLin a (resolventC H z)| ≤ 2 * (N : ℝ) ^ 2 * (1 / z.im) ^ 3 := by
  have hb := norm_resolventC_apply_le hH hz
  have hη : 0 ≤ 1 / z.im := by positivity
  have hterm : ∀ i j, |(if i = j then (0 : ℝ) else -2 * (starRingEnd ℂ (resolventC H z i j) *
      (resolventC H z i a * resolventC H z a j)).re)| ≤ 2 * (1 / z.im) ^ 3 := by
    intro i j
    split_ifs
    · simp only [abs_zero]; positivity
    · rw [abs_mul, abs_neg, abs_two]
      refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
      rw [norm_mul, norm_mul, Complex.norm_conj, pow_three]
      exact mul_le_mul (hb i j) (mul_le_mul (hb i a) (hb a j) (norm_nonneg _) hη)
        (by positivity) hη
  calc |diagSwapLin a (resolventC H z)| ≤ ∑ i, ∑ j, |(if i = j then (0 : ℝ) else
        -2 * (starRingEnd ℂ (resolventC H z i j) *
          (resolventC H z i a * resolventC H z a j)).re)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, 2 * (1 / z.im) ^ 3 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = 2 * (N : ℝ) ^ 2 * (1 / z.im) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The bounds of the expansion (3.30) on the event (3.26) -/

/-- On `aprioriEvent N ε`, with the bound (3.27) for `R` and `|v| ≤ 1/2`, the bounds of
`diagSwap_off_sub_le` hold at every `y ∈ I_ε` for `S = G(H)`, `R = G(Q)` at `y + iη`,
`P = N^{-1/3+3ε}`. -/
private lemma diagSwap_point {N : ℕ} (a : Fin N) {ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hε' : ε < 1 / 10) {ω : Entries N} (hω : ω ∈ aprioriEvent N ε)
    (hRb : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    (hv : |entryVal (Sum.inl a) ω| ≤ 1 / 2)
    (hNP : 2 ≤ (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    (hNP2 : 4 ≤ (N : ℝ) * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2)
    {y : ℝ} (hy : |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) :
    |diagSwapOff (resolventC (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) -
        diagSwapOff (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω))
          ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)| ≤
      32 * |entryVal (Sum.inl a) ω| * (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 ∧
    |diagSwapOff (resolventC (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) -
        diagSwapOff (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω))
          ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) -
        entryVal (Sum.inl a) ω * diagSwapLin a (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω))
          ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)| ≤
      32 * entryVal (Sum.inl a) ω ^ 2 * (N : ℝ) ^ 2 *
        ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) with hη_def
  have hη : 0 < η := Real.rpow_pos_of_pos hn0 _
  set P : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hn0.le _
  have hP1 : P ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hP2 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hzη : (⟨y, η⟩ : ℂ).im = η := rfl
  have hz : 0 < (⟨y, η⟩ : ℂ).im := hη
  have hS : ∀ k l, ‖resolventC (symOfEntries ω) ⟨y, η⟩ k l‖ ≤ if k = l then 2 else P := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      simp only [ite_true]
      exact (aprioriEvent_bounds hN hε hε' hω).1 y hy k
    · have h := hω y hy k l
      simp only [hkl, ite_false, sub_zero] at h ⊢
      exact h.trans hP2
  have hR : ∀ k l, ‖resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨y, η⟩ k l‖ ≤
      if k = l then 2 else P := by
    intro k l
    have h := hRb y hy k l
    by_cases hkl : k = l
    · subst hkl
      simp only [ite_true] at h ⊢
      have hm := (norm_msc_eq_inv_and_lt_one (z := ⟨y, η⟩) hη).2
      have := norm_sub_norm_le (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨y, η⟩ k k)
        (msc ⟨y, η⟩)
      linarith
    · simp only [hkl, ite_false, sub_zero] at h ⊢
      exact h
  exact diagSwap_off_sub_le a (fun i j => diagSwap_expansion a ω hz i j) hR hS hv hP0 hP1 hNP hNP2

/-- `|η ∫_{E₁}^{E₂} g| ≤ η K |E₂ - E₁|` when `|g| ≤ K` on the interval. -/
private lemma diagSwap_eta_int_le {g : ℝ → ℝ} {η K : ℝ} (hη : 0 < η) {E₁ E₂ : ℝ}
    (hg : ∀ y ∈ Set.uIoc E₁ E₂, |g y| ≤ K) :
    |η * ∫ y in E₁..E₂, g y| ≤ K * (η * |E₂ - E₁|) := by
  rw [abs_mul, abs_of_pos hη]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E₁) (b := E₂) (f := g)
    (fun y hy => by simpa [Real.norm_eq_abs] using hg y hy)
  rw [Real.norm_eq_abs] at this
  nlinarith

/-- The expansion (3.30) for `y = offWard` ((3.33)) at `z = E + iη`, `E ∈ I_ε`, on the event:
the size `|y_S| ≤ N^{2ε}`, the increment `|y_S - y_R| ≤ 32 W B N² P³` and the error of the linear
term `≤ 32 W B² N² P³`, for any `W ≥ η²` and `|v| ≤ B ≤ 1/2`. -/
private lemma diagSwap_good_y {N : ℕ} (a : Fin N) {ε B W : ℝ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hε' : ε < 1 / 10) {ω : Entries N} (hω : ω ∈ aprioriEvent N ε)
    (hRb : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    (hvB : |entryVal (Sum.inl a) ω| ≤ B) (hB : B ≤ 1 / 2)
    (hNP : 2 ≤ (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    (hNP2 : 4 ≤ (N : ℝ) * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2)
    (hW : ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 ≤ W)
    {E : ℝ} (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) :
    |offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩| ≤ (N : ℝ) ^ (2 * ε) ∧
    |offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ -
        offWard (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩| ≤
      32 * W * B * (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 ∧
    |offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ -
        offWard (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ -
        entryVal (Sum.inl a) ω * (((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 *
          diagSwapLin a (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω))
            ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩))| ≤
      32 * W * B ^ 2 * (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) with hη_def
  set P : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) with hP
  set v := entryVal (Sum.inl a) ω with hv
  have hv12 : |v| ≤ 1 / 2 := hvB.trans hB
  obtain ⟨h1, h2⟩ := diagSwap_point a hN hε hε' hω hRb hv12 hNP hNP2 hE
  obtain ⟨-, hy, -⟩ := aprioriEvent_bounds hN hε hε' hω
  obtain ⟨hy0, hy1⟩ := hy E hE
  have hoff : ∀ H : Matrix (Fin N) (Fin N) ℝ,
      offWard H ⟨E, η⟩ = η ^ 2 * diagSwapOff (resolventC H ⟨E, η⟩) := fun H => rfl
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hvB
  have hX : 0 ≤ (N : ℝ) ^ 2 * P ^ 3 := by positivity
  have hW0 : 0 ≤ W := (sq_nonneg _).trans hW
  refine ⟨by rw [abs_of_nonneg hy0]; exact hy1, ?_, ?_⟩
  · rw [hoff, hoff, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg η)]
    calc η ^ 2 * |diagSwapOff (resolventC (symOfEntries ω) ⟨E, η⟩) -
          diagSwapOff (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩)|
        ≤ W * (32 * |v| * (N : ℝ) ^ 2 * P ^ 3) :=
          mul_le_mul hW h1 (abs_nonneg _) hW0
      _ ≤ W * (32 * B * (N : ℝ) ^ 2 * P ^ 3) := by gcongr
      _ = _ := by ring
  · have e : η ^ 2 * diagSwapOff (resolventC (symOfEntries ω) ⟨E, η⟩) -
        η ^ 2 * diagSwapOff (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩) -
        v * (η ^ 2 * diagSwapLin a (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩)) =
        η ^ 2 * (diagSwapOff (resolventC (symOfEntries ω) ⟨E, η⟩) -
          diagSwapOff (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩) -
          v * diagSwapLin a (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩)) := by
      ring
    rw [hoff, hoff, e, abs_mul, abs_of_nonneg (sq_nonneg η)]
    have hv2 : v ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hvB 2
    calc η ^ 2 * |diagSwapOff (resolventC (symOfEntries ω) ⟨E, η⟩) -
          diagSwapOff (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩) -
          v * diagSwapLin a (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩)|
        ≤ W * (32 * v ^ 2 * (N : ℝ) ^ 2 * P ^ 3) :=
          mul_le_mul hW h2 (abs_nonneg _) hW0
      _ ≤ W * (32 * B ^ 2 * (N : ℝ) ^ 2 * P ^ 3) := by gcongr
      _ = _ := by ring

/-- The same for `x = offWardInt` on `[E₁, E₂]`, `E₁, E₂ ∈ I_ε` ((3.19)), for any
`W ≥ η |E₂ - E₁|`; `v` leaves the `y`-integral. -/
private lemma diagSwap_good_x {N : ℕ} (a : Fin N) {ε B W : ℝ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hε' : ε < 1 / 10) {ω : Entries N} (hω : ω ∈ aprioriEvent N ε)
    (hRb : ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    (hvB : |entryVal (Sum.inl a) ω| ≤ B) (hB : B ≤ 1 / 2)
    (hNP : 2 ≤ (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε))
    (hNP2 : 4 ≤ (N : ℝ) * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2)
    {E₁ E₂ : ℝ} (h1 : |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (h2 : |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))
    (hW : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * |E₂ - E₁| ≤ W) :
    |offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂| ≤
      2 * (N : ℝ) ^ (4 * ε) ∧
    |offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ -
        offWardInt (symOfEntries (zeroEntry (Sum.inl a) ω)) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε))
          E₁ E₂| ≤
      32 * W * B * (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 ∧
    |offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂ -
        offWardInt (symOfEntries (zeroEntry (Sum.inl a) ω)) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε))
          E₁ E₂ -
        entryVal (Sum.inl a) ω * ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * ∫ y in E₁..E₂,
          diagSwapLin a (resolventC (symOfEntries (zeroEntry (Sum.inl a) ω))
            ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩))| ≤
      32 * W * B ^ 2 * (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) with hη_def
  have hη : 0 < η := Real.rpow_pos_of_pos hn0 _
  set P : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) with hP
  set v := entryVal (Sum.inl a) ω with hv
  set Q := zeroEntry (Sum.inl a) ω with hQ
  have hv12 : |v| ≤ 1 / 2 := hvB.trans hB
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hvB
  have hyI : ∀ y ∈ Set.uIoc E₁ E₂, |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    intro y hy
    have hy' := Set.uIoc_subset_uIcc hy
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 h2
    rcases Set.mem_uIcc.1 hy' with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
      exact abs_le.2 ⟨by linarith, by linarith⟩
  have hcS := diagSwap_continuous_off_y (N := N) hη ω
  have hcR := diagSwap_continuous_off_y (N := N) hη Q
  have hcL := diagSwap_continuous_lin_y a hη Q
  have hoff : ∀ H : Matrix (Fin N) (Fin N) ℝ,
      offWardInt H η E₁ E₂ = η * ∫ y in E₁..E₂, diagSwapOff (resolventC H ⟨y, η⟩) :=
    fun H => rfl
  have hX : 0 ≤ (N : ℝ) ^ 2 * P ^ 3 := by positivity
  refine ⟨(aprioriEvent_bounds hN hε hε' hω).2.2 E₁ E₂ h1 h2, ?_, ?_⟩
  · rw [hoff, hoff, ← mul_sub,
      ← intervalIntegral.integral_sub (hcS.intervalIntegrable _ _) (hcR.intervalIntegrable _ _)]
    refine (diagSwap_eta_int_le hη (K := 32 * B * (N : ℝ) ^ 2 * P ^ 3) fun y hy => ?_).trans ?_
    · refine (diagSwap_point a hN hε hε' hω hRb hv12 hNP hNP2 (hyI y hy)).1.trans ?_
      gcongr
    · calc 32 * B * (N : ℝ) ^ 2 * P ^ 3 * (η * |E₂ - E₁|) ≤ 32 * B * (N : ℝ) ^ 2 * P ^ 3 * W := by
            gcongr
        _ = _ := by ring
  · have e : η * (∫ y in E₁..E₂, diagSwapOff (resolventC (symOfEntries ω) ⟨y, η⟩)) -
        η * (∫ y in E₁..E₂, diagSwapOff (resolventC (symOfEntries Q) ⟨y, η⟩)) -
        v * (η * ∫ y in E₁..E₂, diagSwapLin a (resolventC (symOfEntries Q) ⟨y, η⟩)) =
        η * ∫ y in E₁..E₂, (diagSwapOff (resolventC (symOfEntries ω) ⟨y, η⟩) -
          diagSwapOff (resolventC (symOfEntries Q) ⟨y, η⟩) -
          v * diagSwapLin a (resolventC (symOfEntries Q) ⟨y, η⟩)) := by
      have i1 : IntervalIntegrable (fun y => diagSwapOff (resolventC (symOfEntries ω) ⟨y, η⟩) -
          diagSwapOff (resolventC (symOfEntries Q) ⟨y, η⟩)) MeasureTheory.volume E₁ E₂ :=
        (hcS.sub hcR).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun y => v * diagSwapLin a (resolventC (symOfEntries Q) ⟨y, η⟩))
          MeasureTheory.volume E₁ E₂ := (hcL.const_mul v).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub i1 i2,
        intervalIntegral.integral_sub (hcS.intervalIntegrable _ _) (hcR.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul]
      ring
    rw [hoff, hoff, e]
    have hv2 : v ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hvB 2
    refine (diagSwap_eta_int_le hη (K := 32 * B ^ 2 * (N : ℝ) ^ 2 * P ^ 3) fun y hy => ?_).trans ?_
    · refine (diagSwap_point a hN hε hε' hω hRb hv12 hNP hNP2 (hyI y hy)).2.trans ?_
      gcongr
    · calc 32 * B ^ 2 * (N : ℝ) ^ 2 * P ^ 3 * (η * |E₂ - E₁|) ≤
            32 * B ^ 2 * (N : ℝ) ^ 2 * P ^ 3 * W := by gcongr
        _ = _ := by ring

/-! ### One law: independence of `Q` and `v` -/

/-- The law of `v = h_aa` under `L.law` is `L.diag a`. -/
private lemma diagSwap_map_entryVal {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) (a : Fin N) :
    L.law.map (entryVal (Sum.inl a)) = L.diag a := by
  have : ∀ i, IsProbabilityMeasure (L.diag i) := hL.diag
  have : ∀ p, IsProbabilityMeasure (L.off p) := hL.off
  have : IsProbabilityMeasure (Measure.pi L.diag) := inferInstance
  have : IsProbabilityMeasure (Measure.pi L.off) := inferInstance
  exact ((measurePreserving_eval L.diag a).comp
    (measurePreserving_fst (μ := Measure.pi L.diag) (ν := Measure.pi L.off))).map_eq

private lemma diagSwap_measurable_entryVal {N : ℕ} (a : Fin N) :
    Measurable (entryVal (Sum.inl a) : Entries N → ℝ) := by
  change Measurable fun ω : Entries N => ω.1 a
  exact (measurable_pi_apply a).comp measurable_fst

/-- `diagSwap_core` for `ω ~ L.law`, `b = f(Q)`, `a = f(H)` and `l = Λ(Q)` with `Q` the entries
with `h_aa` set to `0`: the linear term vanishes by the independence of `Q` and `h_aa` and
`E h_aa = 0`, and `E h_aa² ≤ (1 + C0′)/N`. -/
private lemma diagSwap_law {N : ℕ} (a : Fin N) {L : EntryLaws N} {C0' : ℝ}
    (hL : L.IsGenWigner C0') {F : ℝ → ℝ} {CF : ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    {fa fl : Entries N → ℝ} (hfa : Continuous fa) (hfl : Continuous fl) {A : ℝ} (hA : 0 ≤ A)
    (hfaA : ∀ ω, |fa ω| ≤ A) (hflA : ∀ ω, |fl ω| ≤ A)
    {Ω : Set (Entries N)} {R₁ G D1 D2 : ℝ} (hG0 : 0 ≤ G) (hD2 : 0 ≤ D2)
    (hG : ∀ ζ, |ζ| ≤ R₁ → |iteratedDeriv 1 F ζ| ≤ G ∧ |iteratedDeriv 2 F ζ| ≤ G)
    (hgood : ∀ ω ∈ Ω, |fa ω| ≤ R₁ ∧ |fa (zeroEntry (Sum.inl a) ω)| ≤ R₁ ∧
      |fa ω - fa (zeroEntry (Sum.inl a) ω)| ≤ D1 ∧
      |fa ω - fa (zeroEntry (Sum.inl a) ω) -
        entryVal (Sum.inl a) ω * fl (zeroEntry (Sum.inl a) ω)| ≤ D2)
    {T : ℝ} (hT : 0 < T) :
    |∫ ω, F (fa ω) ∂L.law - ∫ ω, F (fa (zeroEntry (Sum.inl a) ω)) ∂L.law| ≤
      G * (D1 ^ 2 / 2 + D2) + CF * (1 + A) ^ CF * (2 * A) *
        ((1 + T) * (L.law Ωᶜ).toReal + (1 + C0') / N / T) := by
  have hP := isProbabilityMeasure_law hL.isProb
  set e : Fin N ⊕ OffDiag N := Sum.inl a with he
  have hz : Continuous (zeroEntry e) := diagSwap_continuous_zeroEntry a
  have hv := diagSwap_measurable_entryVal (N := N) a
  have hmap := diagSwap_map_entryVal hL.isProb a
  have hsq : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have hv2 : Integrable (fun ω => entryVal e ω ^ 2) L.law := by
    have h := (integrable_map_measure (μ := L.law) (f := entryVal e) (g := fun x : ℝ => x ^ 2)
      hsq.aestronglyMeasurable hv.aemeasurable).1 (by rw [hmap]; exact hL.sq_int_diag a)
    exact h
  have hKv : ∫ ω, entryVal e ω ^ 2 ∂L.law ≤ (1 + C0') / N := by
    have h1 : ∫ ω, entryVal e ω ^ 2 ∂L.law = ∫ x, x ^ 2 ∂(L.diag a) := by
      rw [← hmap, integral_map hv.aemeasurable hsq.aestronglyMeasurable]
    rw [h1]
    have h2 := hL.var_diag a
    have := (abs_le.1 h2).2
    rw [add_div, one_div]
    have e2 : C0' * (N : ℝ)⁻¹ = C0' / N := by rw [div_eq_mul_inv]
    linarith
  have hF1c : Continuous (iteratedDeriv 1 F) := hF4.continuous_iteratedDeriv 1 (by norm_num)
  have hmean : ∫ ω, iteratedDeriv 1 F (fa (zeroEntry e ω)) * fl (zeroEntry e ω) * entryVal e ω
      ∂L.law = 0 := by
    set f : Entries N → ℂ := fun ω => ((iteratedDeriv 1 F (fa ω) * fl ω : ℝ) : ℂ) with hf
    have hfc : Continuous f := Complex.continuous_ofReal.comp ((hF1c.comp hfa).mul hfl)
    obtain ⟨C, hC⟩ : ∃ C, ∀ ω, ‖f ω‖ ≤ C := by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := -A) (b := A)).exists_bound_of_continuousOn
        hF1c.continuousOn
      refine ⟨C * A, fun ω => ?_⟩
      simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have h1 := hC (fa ω) (abs_le.1 (hfaA ω))
      rw [Real.norm_eq_abs] at h1
      exact mul_le_mul h1 (hflA ω) (abs_nonneg _) ((abs_nonneg _).trans h1)
    have hfi : Integrable (fun ω => f (zeroEntry e ω)) L.law :=
      Integrable.of_bound (hfc.comp hz).aestronglyMeasurable C (Eventually.of_forall fun ω => hC _)
    have hk : Integrable (fun x : ℝ => x ^ 1) (L.entry e) := by
      have hd : L.entry e = L.diag a := rfl
      have := hL.isProb.diag a
      rw [hd]
      refine Integrable.mono' ((hL.sq_int_diag a).add (integrable_const 1))
        (measurable_id.pow_const 1).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      change ‖x ^ 1‖ ≤ x ^ 2 + 1
      rw [pow_one, Real.norm_eq_abs]
      nlinarith [abs_nonneg x, sq_abs x]
    have h := integral_mul_zeroEntry hL.isProb e f 1 hfc.measurable hfi hk
    have hm1 : L.entryMoment e 1 = 0 := by
      change ∫ x, (-x) ^ 1 ∂(L.diag a) = 0
      simp only [pow_one]
      rw [integral_neg, hL.mean_diag a, neg_zero]
    rw [hm1, Complex.ofReal_zero, mul_zero] at h
    have h' : ∫ ω, ((iteratedDeriv 1 F (fa (zeroEntry e ω)) * fl (zeroEntry e ω) *
        (-entryVal e ω) : ℝ) : ℂ) ∂L.law = 0 := by
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hf, pow_one]
      push_cast
      ring
    have h2 : ∫ ω, iteratedDeriv 1 F (fa (zeroEntry e ω)) * fl (zeroEntry e ω) *
        (-entryVal e ω) ∂L.law = 0 := by
      have := (integral_ofReal (𝕜 := ℂ) (μ := L.law) (f := fun ω =>
        iteratedDeriv 1 F (fa (zeroEntry e ω)) * fl (zeroEntry e ω) *
          (-entryVal e ω))).symm.trans h'
      exact Complex.ofReal_eq_zero.1 this
    have h'' : ∫ ω, -(iteratedDeriv 1 F (fa (zeroEntry e ω)) * fl (zeroEntry e ω) *
        (-entryVal e ω)) ∂L.law = 0 := by
      rw [integral_neg, h2, neg_zero]
    refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans h''
    ring
  have key := diagSwap_core (μ := L.law) hF4 hF (a := fa) (b := fun ω => fa (zeroEntry e ω))
    (l := fun ω => fl (zeroEntry e ω)) (v := entryVal e) hfa.measurable
    (hfa.comp hz).measurable (hfl.comp hz).measurable hv hv2 hKv hA hfaA
    (fun ω => hfaA _) (fun ω => hflA _) hmean hG0 hD2 hG hgood hT
  exact key

/-! ### Exponent bookkeeping -/

private lemma diagSwap_rpow_nat_mul {x : ℝ} (hx : 0 ≤ x) (ε : ℝ) (k : ℕ) :
    x ^ ((k : ℝ) * ε) = (x ^ ε) ^ k := by
  rw [mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

/-- `x^y ≥ 32` for `y ≥ 1/5`, and `x^y ≤ 1/32`, resp. `≤ 1/1024`, for `y ≤ -1/5`, resp.
`y ≤ -2/5`, once `x ≥ 2^25`. -/
private lemma diagSwap_pow_bounds {x : ℝ} (hx : 2 ^ 25 ≤ x) :
    (∀ y : ℝ, 1 / 5 ≤ y → 32 ≤ x ^ y) ∧ (∀ y : ℝ, y ≤ -(1 / 5) → x ^ y ≤ 1 / 32) ∧
      (∀ y : ℝ, y ≤ -(2 / 5) → x ^ y ≤ 1 / 1024) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h5 : 32 ≤ x ^ ((1 : ℝ) / 5) := by
    have h := Real.pow_rpow_inv_natCast (x := (32 : ℝ)) (n := 5) (by norm_num) (by norm_num)
    have e : ((32 : ℝ) ^ (5 : ℕ)) = 2 ^ 25 := by norm_num
    rw [e] at h
    calc (32 : ℝ) = ((2 : ℝ) ^ 25) ^ ((1 : ℝ) / 5) := by
          rw [← h]; norm_num
      _ ≤ x ^ ((1 : ℝ) / 5) := Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have hup : ∀ y : ℝ, 1 / 5 ≤ y → 32 ≤ x ^ y := fun y hy =>
    h5.trans (Real.rpow_le_rpow_of_exponent_le hx1 hy)
  have hdn : ∀ y : ℝ, y ≤ -(1 / 5) → x ^ y ≤ 1 / 32 := by
    intro y hy
    have h1 : x ^ y ≤ x ^ (-((1 : ℝ) / 5)) := Real.rpow_le_rpow_of_exponent_le hx1 hy
    rw [Real.rpow_neg hx0.le] at h1
    have h2 : (x ^ ((1 : ℝ) / 5))⁻¹ ≤ 1 / 32 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h5
      rw [one_div (32 : ℝ)]; exact this
    linarith
  refine ⟨hup, hdn, fun y hy => ?_⟩
  have h1 : x ^ y = (x ^ (y / 2)) ^ 2 := by
    rw [← diagSwap_rpow_nat_mul hx0.le]; congr 1; push_cast; ring
  have h2 := hdn (y / 2) (by linarith)
  have h3 : 0 ≤ x ^ (y / 2) := Real.rpow_nonneg hx0.le _
  rw [h1]
  nlinarith

/-- The parameter rows of the diagonal step for `x = N ≥ 2^25`, `x^ε ≥ 3`, `0 < ε < 1/100`,
`1/3 < φs ≤ 1/2`, with `η = x^{-2/3-ε}`, `P = x^{-1/3+3ε}`, `B = x^{ε-φs}`, `W = 2x^{-4/3}`:
`B ≤ 1/2`; `xP ≥ 2`; `xP² ≥ 4`; `η² ≤ W`; `η · 2x^{-2/3+ε} ≤ W`; `D₁ := 32 W B x² P³ ≤ 1`;
`2x^{4ε} + 1 ≤ x^{5ε}`; `η⁻¹ ≤ x`; `x^{-2/3+ε} ≤ 1`. -/
private lemma diagSwap_rows {x ε φs : ℝ} (hx : 2 ^ 25 ≤ x) (ht : 3 ≤ x ^ ε) (hε : 0 < ε)
    (hε' : ε < 1 / 100) (hφs : 1 / 3 < φs) :
    x ^ (ε - φs) ≤ 1 / 2 ∧ 2 ≤ x * x ^ (-(1 : ℝ) / 3 + 3 * ε) ∧
    4 ≤ x * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 2 ∧
    (x ^ (-(2 : ℝ) / 3 - ε)) ^ 2 ≤ 2 * x ^ (-(4 : ℝ) / 3) ∧
    x ^ (-(2 : ℝ) / 3 - ε) * (2 * x ^ (-(2 : ℝ) / 3 + ε)) ≤ 2 * x ^ (-(4 : ℝ) / 3) ∧
    32 * (2 * x ^ (-(4 : ℝ) / 3)) * x ^ (ε - φs) * x ^ 2 * (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 ≤ 1 ∧
    2 * x ^ (4 * ε) + 1 ≤ x ^ (5 * ε) ∧ 1 / x ^ (-(2 : ℝ) / 3 - ε) ≤ x ∧
    x ^ (-(2 : ℝ) / 3 + ε) ≤ 1 := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨hup, hdn, hdn2⟩ := diagSwap_pow_bounds hx
  have hmul : ∀ y z : ℝ, x ^ y * x ^ z = x ^ (y + z) := fun y z => (Real.rpow_add hx0 y z).symm
  have hsq : ∀ y : ℝ, (x ^ y) ^ 2 = x ^ (2 * y) := fun y => by
    rw [← diagSwap_rpow_nat_mul hx0.le]; norm_num
  have hcube : ∀ y : ℝ, (x ^ y) ^ 3 = x ^ (3 * y) := fun y => by
    rw [← diagSwap_rpow_nat_mul hx0.le]; norm_num
  have hx2 : x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_two x).symm
  have hone : ∀ y : ℝ, x * x ^ y = x ^ (1 + y) := fun y => by
    rw [Real.rpow_add hx0, Real.rpow_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hdn _ (by linarith)).trans (by norm_num)
  · rw [hone]; exact le_trans (by norm_num) (hup _ (by linarith))
  · rw [hsq, hone]; exact le_trans (by norm_num) (hup _ (by linarith))
  · rw [hsq]
    have : x ^ (2 * (-(2 : ℝ) / 3 - ε)) ≤ x ^ (-(4 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h0 : 0 ≤ x ^ (-(4 : ℝ) / 3) := Real.rpow_nonneg hx0.le _
    linarith
  · have : x ^ (-(2 : ℝ) / 3 - ε) * x ^ (-(2 : ℝ) / 3 + ε) = x ^ (-(4 : ℝ) / 3) := by
      rw [hmul]; congr 1; ring
    nlinarith
  · have e : 32 * (2 * x ^ (-(4 : ℝ) / 3)) * x ^ (ε - φs) * x ^ 2 *
        (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 = 64 * x ^ (-(1 : ℝ) / 3 + 10 * ε - φs) := by
      rw [hcube, hx2]
      have : x ^ (-(4 : ℝ) / 3) * x ^ (ε - φs) * x ^ (2 : ℝ) * x ^ (3 * (-(1 : ℝ) / 3 + 3 * ε)) =
          x ^ (-(1 : ℝ) / 3 + 10 * ε - φs) := by
        rw [hmul, hmul, hmul]; congr 1; ring
      rw [← this]; ring
    rw [e]
    have := hdn2 (-(1 : ℝ) / 3 + 10 * ε - φs) (by linarith)
    linarith
  · have h4 : x ^ (4 * ε) = (x ^ ε) ^ 4 := by
      rw [← diagSwap_rpow_nat_mul hx0.le]; norm_num
    have h5 : x ^ (5 * ε) = (x ^ ε) ^ 5 := by
      rw [← diagSwap_rpow_nat_mul hx0.le]; norm_num
    rw [h4, h5]
    have h1 : 1 ≤ (x ^ ε) ^ 4 := one_le_pow₀ (by linarith)
    have : (x ^ ε) ^ 5 = x ^ ε * (x ^ ε) ^ 4 := by ring
    nlinarith
  · rw [one_div, ← Real.rpow_neg hx0.le]
    calc x ^ (-(-(2 : ℝ) / 3 - ε)) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  · exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)

/-- The final count of the diagonal step: with `G = x^{(5CF+1)ε}` and the `D₁, D₂` of
`diagSwap_rows`, `G (D₁²/2 + D₂) + x^{-2}/2 ≤ x^{-1/3+(5CF+20)ε-2φs}/2`. -/
private lemma diagSwap_final {x ε φs CF : ℝ} (hx : 2 ^ 25 ≤ x) (ht : 3 ≤ x ^ ε) (hε : 0 < ε)
    (hε' : ε < 1 / 100) (hφs' : φs ≤ 1 / 2) (hCF : 0 ≤ CF) :
    x ^ ((5 * CF + 1) * ε) *
        ((32 * (2 * x ^ (-(4 : ℝ) / 3)) * x ^ (ε - φs) * x ^ 2 *
            (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3) ^ 2 / 2 +
          32 * (2 * x ^ (-(4 : ℝ) / 3)) * (x ^ (ε - φs)) ^ 2 * x ^ 2 *
            (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3) + x ^ (-2 : ℝ) / 2 ≤
      x ^ (-(1 : ℝ) / 3 + (5 * CF + 20) * ε - 2 * φs) / 2 := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨-, hdn, -⟩ := diagSwap_pow_bounds hx
  have hmul : ∀ y z : ℝ, x ^ y * x ^ z = x ^ (y + z) := fun y z => (Real.rpow_add hx0 y z).symm
  have hsq : ∀ y : ℝ, (x ^ y) ^ 2 = x ^ (2 * y) := fun y => by
    rw [← diagSwap_rpow_nat_mul hx0.le]; norm_num
  have hcube : ∀ y : ℝ, (x ^ y) ^ 3 = x ^ (3 * y) := fun y => by
    rw [← diagSwap_rpow_nat_mul hx0.le]; norm_num
  have hx2 : x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_two x).symm
  set X := x ^ (-(1 : ℝ) / 3 + (5 * CF + 12) * ε - 2 * φs) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hx0.le _
  have eD1 : 32 * (2 * x ^ (-(4 : ℝ) / 3)) * x ^ (ε - φs) * x ^ 2 *
      (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 = 64 * x ^ (-(1 : ℝ) / 3 + 10 * ε - φs) := by
    rw [hcube, hx2]
    have : x ^ (-(4 : ℝ) / 3) * x ^ (ε - φs) * x ^ (2 : ℝ) * x ^ (3 * (-(1 : ℝ) / 3 + 3 * ε)) =
        x ^ (-(1 : ℝ) / 3 + 10 * ε - φs) := by
      rw [hmul, hmul, hmul]; congr 1; ring
    rw [← this]; ring
  have eD2 : 32 * (2 * x ^ (-(4 : ℝ) / 3)) * (x ^ (ε - φs)) ^ 2 * x ^ 2 *
      (x ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 = 64 * x ^ (-(1 : ℝ) / 3 + 11 * ε - 2 * φs) := by
    rw [hcube, hsq, hx2]
    have : x ^ (-(4 : ℝ) / 3) * x ^ (2 * (ε - φs)) * x ^ (2 : ℝ) *
        x ^ (3 * (-(1 : ℝ) / 3 + 3 * ε)) = x ^ (-(1 : ℝ) / 3 + 11 * ε - 2 * φs) := by
      rw [hmul, hmul, hmul]; congr 1; ring
    rw [← this]; ring
  rw [eD1, eD2]
  have e1 : x ^ ((5 * CF + 1) * ε) * ((64 * x ^ (-(1 : ℝ) / 3 + 10 * ε - φs)) ^ 2 / 2) =
      2048 * (x ^ (-(1 : ℝ) / 3 + 9 * ε) * X) := by
    rw [mul_pow, hsq, hX, hmul]
    have : x ^ ((5 * CF + 1) * ε) * x ^ (2 * (-(1 : ℝ) / 3 + 10 * ε - φs)) =
        x ^ (-(1 : ℝ) / 3 + 9 * ε + (-(1 : ℝ) / 3 + (5 * CF + 12) * ε - 2 * φs)) := by
      rw [hmul]; congr 1; ring
    rw [← this]; ring
  have e2 : x ^ ((5 * CF + 1) * ε) * (64 * x ^ (-(1 : ℝ) / 3 + 11 * ε - 2 * φs)) = 64 * X := by
    rw [hX, mul_left_comm, hmul]; congr 2; ring
  have e3 : x ^ (-(1 : ℝ) / 3 + (5 * CF + 20) * ε - 2 * φs) = (x ^ ε) ^ 8 * X := by
    rw [← diagSwap_rpow_nat_mul hx0.le, hX, hmul]; congr 1; push_cast; ring
  have h9 : x ^ (-(1 : ℝ) / 3 + 9 * ε) ≤ 1 / 32 := hdn _ (by linarith)
  have hm2 : x ^ (-2 : ℝ) ≤ X := Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  have h8 : 6561 ≤ (x ^ ε) ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num) ht 8
    norm_num at this ⊢; linarith
  rw [mul_add, e1, e2, e3]
  have : x ^ (-(1 : ℝ) / 3 + 9 * ε) * X ≤ 1 / 32 * X := mul_le_mul_of_nonneg_right h9 hX0
  nlinarith

/-- `φ` beats every power of `N`: `N^M e^{-c φ} ≤ 1` for large `N`. -/
private lemma diagSwap_rpow_mul_exp_le (c M : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ M * Real.exp (-c * phi N) ≤ 1 := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  filter_upwards [eventually_ge_atTop 3, hL.eventually_ge_atTop ((|M| + 1) / c),
    hu.eventually_ge_atTop 2] with N hN3 hL1 hu2
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    exact Real.log_pos (by linarith)
  have hphi : L ^ 2 ≤ phi N := by
    rw [phi_eq_exp hN3]
    have h2 : L ^ 2 = Real.exp (2 * Real.log L) := by
      rw [show (2 : ℝ) * Real.log L = Real.log L + Real.log L by ring, Real.exp_add,
        Real.exp_log hL0]
      ring
    rw [h2]
    exact Real.exp_le_exp.2 (by nlinarith)
  rw [Real.rpow_def_of_pos hN0, ← Real.exp_add, ← hLdef]
  refine Real.exp_le_one_iff.2 ?_
  have h1 : (|M| + 1) ≤ c * L := by
    have := (div_le_iff₀ hc).1 hL1
    linarith
  have h2 : L * M ≤ L * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) hL0.le
  nlinarith [abs_nonneg M]

/-- Off the event: `Φ ((1 + T) p + K_v/T) ≤ N^{-2}/2` for `Φ = CF (1 + A)^CF (2A)`, `A = 4N⁵`,
`T = N^{D+3}`, `D = 5CF + 5` and `K_v = (1 + C0′)/N`, once `p ≤ N^{-(2D+6)}` and
`N ≥ 8 K₁ (1 + C0′)` with `K₁ = 8 CF 5^CF`. -/
private lemma diagSwap_off_part {N : ℕ} {CF C0' p : ℝ} (hN : 1 ≤ N) (hCF : 0 ≤ CF)
    (hC0 : 0 ≤ C0') (hp0 : 0 ≤ p) (hp : p ≤ (N : ℝ) ^ (-(2 * (5 * CF + 5) + 6)))
    (hK : 8 * (8 * CF * 5 ^ CF) * (1 + C0') ≤ N) :
    CF * (1 + 4 * (N : ℝ) ^ 5) ^ CF * (2 * (4 * (N : ℝ) ^ 5)) *
        ((1 + (N : ℝ) ^ (5 * CF + 5 + 3)) * p + (1 + C0') / N / (N : ℝ) ^ (5 * CF + 5 + 3)) ≤
      (N : ℝ) ^ (-2 : ℝ) / 2 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  set n : ℝ := (N : ℝ) with hn
  set D : ℝ := 5 * CF + 5 with hD
  set K₁ : ℝ := 8 * CF * 5 ^ CF with hK₁
  have hK0 : 0 ≤ K₁ := by positivity
  have hmul : ∀ y z : ℝ, n ^ y * n ^ z = n ^ (y + z) := fun y z => (Real.rpow_add hn0 y z).symm
  have h5 : n ^ 5 = n ^ (5 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have hn5 : 1 ≤ n ^ 5 := one_le_pow₀ hn1
  have hΦ : CF * (1 + 4 * n ^ 5) ^ CF * (2 * (4 * n ^ 5)) ≤ K₁ * n ^ D := by
    have h1 : (1 + 4 * n ^ 5) ^ CF ≤ (5 * n ^ 5) ^ CF :=
      Real.rpow_le_rpow (by positivity) (by linarith) hCF
    have h2 : (5 * n ^ 5) ^ CF = 5 ^ CF * n ^ (5 * CF) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), h5, ← Real.rpow_mul hn0.le]
    have h3 : n ^ D = n ^ (5 * CF) * n ^ 5 := by
      rw [h5, hmul]
    calc CF * (1 + 4 * n ^ 5) ^ CF * (2 * (4 * n ^ 5))
        ≤ CF * (5 ^ CF * n ^ (5 * CF)) * (2 * (4 * n ^ 5)) := by
          rw [← h2]; gcongr
      _ = K₁ * n ^ D := by rw [h3, hK₁]; ring
  have hT1 : 1 ≤ n ^ (D + 3) := Real.one_le_rpow hn1 (by positivity)
  have hT0 : 0 < n ^ (D + 3) := by linarith
  have hpart1 : (1 + n ^ (D + 3)) * p ≤ 2 * n ^ (-(D + 3)) := by
    have hp' : p ≤ n ^ (-(2 * D + 6)) := hp
    calc (1 + n ^ (D + 3)) * p ≤ (2 * n ^ (D + 3)) * n ^ (-(2 * D + 6)) :=
          mul_le_mul (by linarith) hp' hp0 (by positivity)
      _ = 2 * n ^ (-(D + 3)) := by rw [mul_assoc, hmul]; congr 2; ring
  have hpart2 : (1 + C0') / n / n ^ (D + 3) = (1 + C0') * n ^ (-(D + 4)) := by
    rw [div_div, Real.rpow_neg hn0.le, ← div_eq_mul_inv]
    congr 1
    rw [show D + 4 = 1 + (D + 3) by ring, Real.rpow_add hn0 1 (D + 3), Real.rpow_one]
  have hm3 : n ^ D * n ^ (-(D + 3)) = n ^ (-3 : ℝ) := by rw [hmul]; congr 1; ring
  have hm4 : n ^ D * n ^ (-(D + 4)) = n ^ (-3 : ℝ) * n ^ (-1 : ℝ) := by
    rw [hmul, hmul]; congr 1; ring
  have hm2 : n ^ (-2 : ℝ) = n * n ^ (-3 : ℝ) := by
    rw [show (-2 : ℝ) = 1 + -3 by norm_num, Real.rpow_add hn0, Real.rpow_one]
  have hinv : n ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have h30 : 0 ≤ n ^ (-3 : ℝ) := Real.rpow_nonneg hn0.le _
  have hinv0 : 0 ≤ n ^ (-1 : ℝ) := Real.rpow_nonneg hn0.le _
  have hS0 : 0 ≤ (1 + n ^ (D + 3)) * p + (1 + C0') / n / n ^ (D + 3) := by positivity
  calc CF * (1 + 4 * n ^ 5) ^ CF * (2 * (4 * n ^ 5)) *
        ((1 + n ^ (D + 3)) * p + (1 + C0') / n / n ^ (D + 3))
      ≤ K₁ * n ^ D * (2 * n ^ (-(D + 3)) + (1 + C0') * n ^ (-(D + 4))) := by
        rw [← hpart2]
        exact mul_le_mul hΦ (by linarith) hS0 (by positivity)
    _ = K₁ * (2 * n ^ (-3 : ℝ) + (1 + C0') * (n ^ (-3 : ℝ) * n ^ (-1 : ℝ))) := by
        rw [← hm4, ← hm3]; ring
    _ ≤ K₁ * (2 * n ^ (-3 : ℝ) + (1 + C0') * n ^ (-3 : ℝ)) := by
        gcongr
        nlinarith
    _ ≤ n ^ (-2 : ℝ) / 2 := by
        rw [hm2]
        have : K₁ * (2 * n ^ (-3 : ℝ) + (1 + C0') * n ^ (-3 : ℝ)) =
            (K₁ * (2 + (1 + C0'))) * n ^ (-3 : ℝ) := by ring
        rw [this]
        have hle : K₁ * (2 + (1 + C0')) ≤ n / 2 := by nlinarith
        nlinarith

/-! ### Assembly -/

/-- Deterministic sizes of the two functionals and of their linear coefficients, for every real
symmetric `H`: at most `4N⁵` once `η⁻¹ ≤ N` and `η |E₂ - E₁| ≤ 2`. -/
private lemma diagSwap_det {N : ℕ} (a : Fin N) (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    (hηN : 1 / η ≤ N) {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (E E₁ E₂ : ℝ)
    (hW : η * |E₂ - E₁| ≤ 2) :
    |offWard H ⟨E, η⟩| ≤ 4 * (N : ℝ) ^ 5 ∧
    |η ^ 2 * diagSwapLin a (resolventC H ⟨E, η⟩)| ≤ 4 * (N : ℝ) ^ 5 ∧
    |offWardInt H η E₁ E₂| ≤ 4 * (N : ℝ) ^ 5 ∧
    |η * ∫ y in E₁..E₂, diagSwapLin a (resolventC H ⟨y, η⟩)| ≤ 4 * (N : ℝ) ^ 5 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi0 : 0 ≤ 1 / η := by positivity
  have hηη : η * (1 / η) = 1 := by field_simp
  have hz : 0 < (⟨E, η⟩ : ℂ).im := hη
  have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hn1 (by norm_num)
  have hN3 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hn1 (by norm_num)
  have hN4 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hn1 (by norm_num)
  have hi2 : (1 / η) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hi0 hηN 2
  have hi3 : (1 / η) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hi0 hηN 3
  have hW0 : 0 ≤ η * |E₂ - E₁| := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨h0, h1⟩ := diagSwap_off_bound hH hz
    have e : offWard H ⟨E, η⟩ = η ^ 2 * diagSwapOff (resolventC H ⟨E, η⟩) := rfl
    rw [e, abs_of_nonneg (mul_nonneg (sq_nonneg _) h0)]
    calc η ^ 2 * diagSwapOff (resolventC H ⟨E, η⟩) ≤ η ^ 2 * ((N : ℝ) ^ 2 * (1 / η) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (N : ℝ) ^ 2 * (η * (1 / η)) ^ 2 := by ring
      _ ≤ 4 * (N : ℝ) ^ 5 := by rw [hηη]; nlinarith
  · have h1 := diagSwap_lin_bound a hH hz
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc η ^ 2 * |diagSwapLin a (resolventC H ⟨E, η⟩)| ≤
          η ^ 2 * (2 * (N : ℝ) ^ 2 * (1 / η) ^ 3) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = 2 * (N : ℝ) ^ 2 * (η * (1 / η)) ^ 2 * (1 / η) := by ring
      _ ≤ 2 * (N : ℝ) ^ 2 * 1 * N := by
          rw [hηη, one_pow]; gcongr
      _ ≤ 4 * (N : ℝ) ^ 5 := by nlinarith
  · have e : offWardInt H η E₁ E₂ = η * ∫ y in E₁..E₂, diagSwapOff (resolventC H ⟨y, η⟩) := rfl
    rw [e]
    refine (diagSwap_eta_int_le hη (K := (N : ℝ) ^ 2 * (1 / η) ^ 2) fun y _ => ?_).trans ?_
    · obtain ⟨h0, h1⟩ := diagSwap_off_bound hH (show 0 < (⟨y, η⟩ : ℂ).im from hη)
      rw [abs_of_nonneg h0]; exact h1
    · calc (N : ℝ) ^ 2 * (1 / η) ^ 2 * (η * |E₂ - E₁|) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 2 * 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hi2 (by positivity)) hW hW0 (by positivity)
        _ ≤ 4 * (N : ℝ) ^ 5 := by nlinarith
  · refine (diagSwap_eta_int_le hη (K := 2 * (N : ℝ) ^ 2 * (1 / η) ^ 3) fun y _ =>
      diagSwap_lin_bound a hH (show 0 < (⟨y, η⟩ : ℂ).im from hη)).trans ?_
    calc 2 * (N : ℝ) ^ 2 * (1 / η) ^ 3 * (η * |E₂ - E₁|) ≤ 2 * (N : ℝ) ^ 2 * (N : ℝ) ^ 3 * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hi3 (by positivity)) hW hW0 (by positivity)
      _ = 4 * (N : ℝ) ^ 5 := by ring

/-- `E F(f(H))` under `H_γ` and under `H_{γ-1}`, `γ = lexPos N (a, a)`, through the common value
`E F(f(Q))`: if each law moves `E F(f)` by at most `δ` when `h_aa` is set to `0`, the two laws
differ by at most `2δ`. -/
private lemma diagSwap_two {N : ℕ} (a : Fin N) {Lv : EntryLaws N} (hv : Lv.IsProb)
    {F : ℝ → ℝ} (hFc : Continuous F) {fa : Entries N → ℝ} (hfa : Continuous fa) {δ : ℝ}
    (h1 : |∫ ω, F (fa ω) ∂(interp (lexPos N) (lexPos N (Sum.inl a)) Lv (goeLaws N)).law -
      ∫ ω, F (fa (zeroEntry (Sum.inl a) ω))
        ∂(interp (lexPos N) (lexPos N (Sum.inl a)) Lv (goeLaws N)).law| ≤ δ)
    (h0 : |∫ ω, F (fa ω) ∂(interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law -
      ∫ ω, F (fa (zeroEntry (Sum.inl a) ω))
        ∂(interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law| ≤ δ) :
    |∫ ω, F (fa ω) ∂(interp (lexPos N) (lexPos N (Sum.inl a)) Lv (goeLaws N)).law -
      ∫ ω, F (fa ω) ∂(interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law| ≤
      δ + δ := by
  have hm : Measurable fun ω : Entries N => ((F (fa ω) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp (hFc.comp hfa)).measurable
  have h := integral_zeroEntry_interp hv (goeLaws_isGenWigner N).isProb (Sum.inl a) _ hm
  have e1 := integral_ofReal (𝕜 := ℂ)
    (μ := (interp (lexPos N) (lexPos N (Sum.inl a)) Lv (goeLaws N)).law)
    (f := fun ω => F (fa (zeroEntry (Sum.inl a) ω)))
  have e2 := integral_ofReal (𝕜 := ℂ)
    (μ := (interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law)
    (f := fun ω => F (fa (zeroEntry (Sum.inl a) ω)))
  have h' := Complex.ofReal_injective (e1.symm.trans (h.trans e2))
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h'
  rw [h'] at h1
  calc _ ≤ |∫ ω, F (fa ω) ∂(interp (lexPos N) (lexPos N (Sum.inl a)) Lv (goeLaws N)).law -
        ∫ ω, F (fa (zeroEntry (Sum.inl a) ω))
          ∂(interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law| +
      |∫ ω, F (fa (zeroEntry (Sum.inl a) ω))
          ∂(interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law -
        ∫ ω, F (fa ω) ∂(interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law| :=
        abs_sub_le _ _ _
    _ ≤ δ + δ := by rw [abs_sub_comm] at h0; exact add_le_add h1 h0

/-- One law of the class: `|E F(f(H)) - E F(f(Q))| ≤ N^{-1/3+(5CF+20)ε-2φs}/2` for a functional
`f` of size `≤ 4N⁵` with linear coefficient `l`, given the bounds of `diagSwap_good_y` or
`diagSwap_good_x` on `Ω` and `P(Ωᶜ) ≤ N^{-(10CF+16)}`. -/
private lemma diagSwap_perLaw {N : ℕ} (a : Fin N) {ε φs CF C0 : ℝ} {L : EntryLaws N}
    (hL : L.IsGenWigner (max C0 1)) (hN : 1 ≤ N) (hx : (2 : ℝ) ^ 25 ≤ N) (ht : 3 ≤ (N : ℝ) ^ ε)
    (hε : 0 < ε) (hε' : ε < 1 / 100) (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) (hCF : 0 ≤ CF)
    {F : ℝ → ℝ} (hF4 : ContDiff ℝ 4 F)
    (hF : ∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF)
    (hG : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (5 * ε) →
      ∀ n ∈ Finset.Icc 1 4, |iteratedDeriv n F ζ| ≤ (N : ℝ) ^ ((5 * CF + 1) * ε))
    {Ω : Set (Entries N)} (hp : (L.law Ωᶜ).toReal ≤ (N : ℝ) ^ (-(2 * (5 * CF + 5) + 6)))
    (hK : 8 * (8 * CF * 5 ^ CF) * (1 + max C0 1) ≤ N)
    {fa fl : Entries N → ℝ} (hfa : Continuous fa) (hfl : Continuous fl)
    (hfaA : ∀ ω, |fa ω| ≤ 4 * (N : ℝ) ^ 5) (hflA : ∀ ω, |fl ω| ≤ 4 * (N : ℝ) ^ 5)
    (hgood : ∀ ω ∈ Ω, |fa ω| ≤ 2 * (N : ℝ) ^ (4 * ε) ∧
      |fa ω - fa (zeroEntry (Sum.inl a) ω)| ≤
        32 * (2 * (N : ℝ) ^ (-(4 : ℝ) / 3)) * (N : ℝ) ^ (ε - φs) * (N : ℝ) ^ 2 *
          ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 ∧
      |fa ω - fa (zeroEntry (Sum.inl a) ω) -
          entryVal (Sum.inl a) ω * fl (zeroEntry (Sum.inl a) ω)| ≤
        32 * (2 * (N : ℝ) ^ (-(4 : ℝ) / 3)) * ((N : ℝ) ^ (ε - φs)) ^ 2 * (N : ℝ) ^ 2 *
          ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3) :
    |∫ ω, F (fa ω) ∂L.law - ∫ ω, F (fa (zeroEntry (Sum.inl a) ω)) ∂L.law| ≤
      (N : ℝ) ^ (-(1 : ℝ) / 3 + (5 * CF + 20) * ε - 2 * φs) / 2 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  obtain ⟨-, -, -, -, -, hD1, h45, -, -⟩ := diagSwap_rows hx ht hε hε' hφs
  set D1 := 32 * (2 * (N : ℝ) ^ (-(4 : ℝ) / 3)) * (N : ℝ) ^ (ε - φs) * (N : ℝ) ^ 2 *
    ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 with hD1def
  set D2 := 32 * (2 * (N : ℝ) ^ (-(4 : ℝ) / 3)) * ((N : ℝ) ^ (ε - φs)) ^ 2 * (N : ℝ) ^ 2 *
    ((N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)) ^ 3 with hD2def
  have hD2 : 0 ≤ D2 := by positivity
  have h4 : 0 ≤ (N : ℝ) ^ (4 * ε) := Real.rpow_nonneg hn0.le _
  have hgood' : ∀ ω ∈ Ω, |fa ω| ≤ (N : ℝ) ^ (5 * ε) ∧
      |fa (zeroEntry (Sum.inl a) ω)| ≤ (N : ℝ) ^ (5 * ε) ∧
      |fa ω - fa (zeroEntry (Sum.inl a) ω)| ≤ D1 ∧
      |fa ω - fa (zeroEntry (Sum.inl a) ω) -
        entryVal (Sum.inl a) ω * fl (zeroEntry (Sum.inl a) ω)| ≤ D2 := by
    intro ω hω
    obtain ⟨g1, g2, g3⟩ := hgood ω hω
    refine ⟨by linarith, ?_, g2, g3⟩
    have := abs_sub_abs_le_abs_sub (fa ω) (fa (zeroEntry (Sum.inl a) ω))
    have := abs_sub_comm (fa ω) (fa (zeroEntry (Sum.inl a) ω))
    have := abs_sub_abs_le_abs_sub (fa (zeroEntry (Sum.inl a) ω)) (fa ω)
    linarith
  have hG' : ∀ ζ : ℝ, |ζ| ≤ (N : ℝ) ^ (5 * ε) → |iteratedDeriv 1 F ζ| ≤
      (N : ℝ) ^ ((5 * CF + 1) * ε) ∧ |iteratedDeriv 2 F ζ| ≤ (N : ℝ) ^ ((5 * CF + 1) * ε) :=
    fun ζ hζ => ⟨hG ζ hζ 1 (by simp), hG ζ hζ 2 (by simp)⟩
  have hT : 0 < (N : ℝ) ^ (5 * CF + 5 + 3) := Real.rpow_pos_of_pos hn0 _
  have key := diagSwap_law a hL hF4 hF hfa hfl (by positivity) hfaA hflA
    (Real.rpow_nonneg hn0.le _) hD2 hG' hgood' hT
  have hoff := diagSwap_off_part (C0' := max C0 1) hN hCF (le_max_of_le_right zero_le_one)
    ENNReal.toReal_nonneg hp hK
  have hfin := diagSwap_final hx ht hε hε' hφs' hCF
  calc _ ≤ _ := key
    _ ≤ _ := by
      rw [← hD1def, ← hD2def] at hfin
      linarith

/-! ### (3.29)–(3.38) for a diagonal entry -/

/-- (3.29)–(3.38) for a diagonal entry `e = (a, a)`: one replacement `H_{γ-1} → H_γ`,
`γ = lexPos N e`, between a law of Lemma 3.5 and the GOE, for both functionals of the Claim, with
error `N^{-1/3+Cε} q⁻²`, `q = N^{φs}`; the second moments on the diagonal need not match. -/
theorem swap_comparison_diag_largeQ {CF C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∃ ε₀ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
      ∀ Lv : EntryLaws N, LargeQClass C0 φs N Lv → ∀ a : Fin N,
      ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
        (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
        (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
              ∂(interp (lexPos N) (lexPos N (Sum.inl a)) Lv (goeLaws N)).law -
            ∫ ω, F (offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
              ∂(interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law| ≤
            (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε - 2 * φs)) ∧
        (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
          |∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)
              ∂(interp (lexPos N) (lexPos N (Sum.inl a)) Lv (goeLaws N)).law -
            ∫ ω, F (offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂)
              ∂(interp (lexPos N) (lexPos N (Sum.inl a) - 1) Lv (goeLaws N)).law| ≤
            (N : ℝ) ^ (-(1 : ℝ) / 3 + C * ε - 2 * φs)) := by
  refine ⟨1 / 100, by norm_num, 5 * |CF| + 20, by positivity, fun ε hε hε' => ?_⟩
  by_cases hCF : 0 ≤ CF
  swap
  · refine ⟨0, fun N _ Lv _ a F _ hF => ?_⟩
    exfalso
    have h1 := hF 1 (by simp) 0
    exact hCF (by simpa using (abs_nonneg _).trans h1)
  rw [abs_of_nonneg hCF]
  have hε10 : ε < 1 / 10 := by linarith
  obtain ⟨c, hc, Cb, hCb, N1, hHP⟩ := (apriori_largeQInterp_event hC0 hφs hφs' ε hε hε10).inter
    (entryVal_le_largeQInterp hC0 hφs hφs' ε hε hε10)
  obtain ⟨N2, hN2⟩ := norm_resolventC_zeroEntry_sub_le hφs hφs' ε hε hε10
  obtain ⟨N3, hN3⟩ := abs_iteratedDeriv_le_rpow_eps (CF := CF) (a := 5) (by norm_num) hε
  obtain ⟨N4, hN4⟩ := eventually_atTop.1 <|
    (eventually_ge_atTop (2 ^ 25)).and <|
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3).and <|
    (eventually_ge_atTop ⌈8 * (8 * CF * 5 ^ CF) * (1 + max C0 1)⌉₊).and <|
    diagSwap_rpow_mul_exp_le c (2 * (5 * CF + 5) + 6 + Cb) hc
  refine ⟨max N1 (max N2 (max N3 N4)), fun N hN Lv hLv a F hF4 hF => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN3 : N3 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNN4 : N4 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  obtain ⟨hN25, ht, hNK, hexp⟩ := hN4 N hNN4
  replace ht : 3 ≤ (N : ℝ) ^ ε := ht
  have hx : (2 : ℝ) ^ 25 ≤ N := by exact_mod_cast hN25
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN25
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hn0 : (0 : ℝ) < N := by linarith
  have hK : 8 * (8 * CF * 5 ^ CF) * (1 + max C0 1) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  obtain ⟨hB, hNP, hNP2, hW1, hW2, -, -, hηN, hwin⟩ := diagSwap_rows hx ht hε hε' hφs
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) with hη_def
  have hη : 0 < η := Real.rpow_pos_of_pos hn0 _
  set e : Fin N ⊕ OffDiag N := Sum.inl a with he
  set Ω : Set (Entries N) := aprioriEvent N ε ∩
    {ω | ∀ e : Fin N ⊕ OffDiag N, |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs)} with hΩ
  have hG := fun ζ hζ => hN3 N hNN3 F hF ζ hζ
  -- the two laws `H_γ`, `H_{γ-1}`
  have hp : ∀ γ : ℕ, ((interp (lexPos N) γ Lv (goeLaws N)).law Ωᶜ).toReal ≤
      (N : ℝ) ^ (-(2 * (5 * CF + 5) + 6)) := by
    intro γ
    have h := hHP N hNN1 (interp (lexPos N) γ Lv (goeLaws N)) ⟨Lv, γ, hLv, rfl⟩
    have h' := ENNReal.toReal_le_of_le_ofReal (by positivity) h
    refine h'.trans ?_
    rw [Real.rpow_one] at *
    have hC : (N : ℝ) ^ Cb = (N : ℝ) ^ (Cb : ℝ) := (Real.rpow_natCast _ _).symm
    have e2 : (N : ℝ) ^ (2 * (5 * CF + 5) + 6 + (Cb : ℝ)) =
        (N : ℝ) ^ (2 * (5 * CF + 5) + 6) * (N : ℝ) ^ (Cb : ℝ) := Real.rpow_add hn0 _ _
    rw [e2] at hexp
    have hpos : 0 < (N : ℝ) ^ (2 * (5 * CF + 5) + 6) := Real.rpow_pos_of_pos hn0 _
    rw [Real.rpow_neg hn0.le, hC, ← one_div, le_div_iff₀ hpos]
    calc (N : ℝ) ^ (Cb : ℝ) * Real.exp (-c * phi N) * (N : ℝ) ^ (2 * (5 * CF + 5) + 6) =
        (N : ℝ) ^ (2 * (5 * CF + 5) + 6) * (N : ℝ) ^ (Cb : ℝ) * Real.exp (-c * phi N) := by ring
      _ ≤ 1 := hexp
  have hwL : ∀ γ : ℕ, (interp (lexPos N) γ Lv (goeLaws N)).IsGenWigner (max C0 1) := fun γ =>
    interp_isGenWigner hLv.1 (goeLaws_isGenWigner N)
  -- the event: (3.26), `|v| ≤ N^ε q⁻¹`, and then (3.27)
  have hRb : ∀ ω ∈ Ω, ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩ k l -
          (if k = l then msc ⟨E, η⟩ else 0)‖ ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) :=
    fun ω hω => hN2 N hNN2 ω (Sum.inl a) hω.1 (hω.2 _)
  have hW0 : 2 * (N : ℝ) ^ (-(4 : ℝ) / 3) ≤ 2 := by
    have := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num : (-(4 : ℝ) / 3) ≤ 0)
    linarith
  have hlen : ∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → η * |E₂ - E₁| ≤ 2 * (N : ℝ) ^ (-(4 : ℝ) / 3) := by
    intro E₁ E₂ h1 h2
    have hΔ : |E₂ - E₁| ≤ 2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
      have a1 := abs_le.1 h1
      have a2 := abs_le.1 h2
      exact abs_le.2 ⟨by linarith, by linarith⟩
    exact (mul_le_mul_of_nonneg_left hΔ hη.le).trans hW2
  have hFc : Continuous F := hF4.continuous
  have hcont : ∀ y : ℝ, Continuous (fun ω : Entries N => (ω, y)) := fun y =>
    continuous_id.prodMk continuous_const
  refine ⟨fun E hE => ?_, fun E₁ E₂ h1 h2 => ?_⟩
  · -- `y = offWard` at `E + iη`
    have hfa : Continuous fun ω : Entries N => offWard (symOfEntries ω) ⟨E, η⟩ := by
      have h := (diagSwap_continuous_off (N := N) hη).comp (hcont E)
      have h2 := h.const_mul (η ^ 2)
      exact h2
    have hfl : Continuous fun ω : Entries N =>
        η ^ 2 * diagSwapLin a (resolventC (symOfEntries ω) ⟨E, η⟩) := by
      have h := (diagSwap_continuous_lin a hη).comp (hcont E)
      have h2 := h.const_mul (η ^ 2)
      exact h2
    have hdet := fun ω : Entries N => diagSwap_det a hN1 hη hηN (symOfEntries_isHermitian ω) E E E
      (by simp)
    have hgood : ∀ ω ∈ Ω, _ := fun ω hω =>
      diagSwap_good_y a hN1 hε hε10 hω.1 (hRb ω hω) (hω.2 _) hB hNP hNP2 hW1 hE
    have per : ∀ γ : ℕ, |∫ ω, F (offWard (symOfEntries ω) ⟨E, η⟩)
          ∂(interp (lexPos N) γ Lv (goeLaws N)).law -
        ∫ ω, F (offWard (symOfEntries (zeroEntry (Sum.inl a) ω)) ⟨E, η⟩)
          ∂(interp (lexPos N) γ Lv (goeLaws N)).law| ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + (5 * CF + 20) * ε - 2 * φs) / 2 := fun γ =>
      diagSwap_perLaw a (hwL γ) hN1 hx ht hε hε' hφs hφs' hCF hF4 hF hG (hp γ) hK hfa hfl
        (fun ω => (hdet ω).1) (fun ω => (hdet ω).2.1) fun ω hω => by
          obtain ⟨g1, g2, g3⟩ := hgood ω hω
          refine ⟨?_, g2, g3⟩
          have : (N : ℝ) ^ (2 * ε) ≤ 2 * (N : ℝ) ^ (4 * ε) := by
            have := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : 2 * ε ≤ 4 * ε)
            have := Real.rpow_nonneg hn0.le (4 * ε)
            linarith
          exact g1.trans this
    have h2 := diagSwap_two a hLv.1.isProb hFc hfa (per _) (per _)
    linarith
  · -- `x = offWardInt` on `[E₁, E₂]`
    have hfa : Continuous fun ω : Entries N => offWardInt (symOfEntries ω) η E₁ E₂ := by
      have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume)
        (f := fun (ω : Entries N) (y : ℝ) => diagSwapOff (resolventC (symOfEntries ω) ⟨y, η⟩))
        (diagSwap_continuous_off hη) E₁ E₂
      have h2 := h.const_mul η
      exact h2
    have hfl : Continuous fun ω : Entries N =>
        η * ∫ y in E₁..E₂, diagSwapLin a (resolventC (symOfEntries ω) ⟨y, η⟩) := by
      have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := MeasureTheory.volume)
        (f := fun (ω : Entries N) (y : ℝ) => diagSwapLin a (resolventC (symOfEntries ω) ⟨y, η⟩))
        (diagSwap_continuous_lin a hη) E₁ E₂
      have h2 := h.const_mul η
      exact h2
    have hW := hlen E₁ E₂ h1 h2
    have hdet := fun ω : Entries N => diagSwap_det a hN1 hη hηN (symOfEntries_isHermitian ω) E₁ E₁
      E₂ (hW.trans hW0)
    have per : ∀ γ : ℕ, |∫ ω, F (offWardInt (symOfEntries ω) η E₁ E₂)
          ∂(interp (lexPos N) γ Lv (goeLaws N)).law -
        ∫ ω, F (offWardInt (symOfEntries (zeroEntry (Sum.inl a) ω)) η E₁ E₂)
          ∂(interp (lexPos N) γ Lv (goeLaws N)).law| ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + (5 * CF + 20) * ε - 2 * φs) / 2 := fun γ =>
      diagSwap_perLaw a (hwL γ) hN1 hx ht hε hε' hφs hφs' hCF hF4 hF hG (hp γ) hK hfa hfl
        (fun ω => (hdet ω).2.2.1) (fun ω => (hdet ω).2.2.2) fun ω hω =>
          diagSwap_good_x a hN1 hε hε10 hω.1 (hRb ω hω) (hω.2 _) hB hNP hNP2 h1 h2 hW
    have h2 := diagSwap_two a hLv.1.isProb hFc hfa (per _) (per _)
    linarith

/-! ### A nondegenerate instance of the hypotheses -/

-- The entry law of Lemma 3.5 at `N = 1024` with diagonal values `±1/16, 0, 0` (variance `2/N`)
-- and off-diagonal values `±1/32` (variance `1/N`), in `LargeQClass 1 (2/5) 1024`.
open private lawA lawA_isGenWigner lawA_supp from WEdgeNS.EdgeUniv.LargeQClass

/-- Every hypothesis of `swap_comparison_diag_largeQ` holds at one point: `N = 1024`, `C0 = 1`,
`φs = 2/5`, `ε = 1/15` (the window `I_ε` is `|E - 2| ≤ 1/64`), `Lv` the law above, the diagonal
entry `a = 4` with `γ = lexPos N (a, a) = 4091` (under `H_γ` the entry `(4, 4)` has the law of
`Lv`, under `H_{γ-1}` the Gaussian law, and rows `0`–`3` have both entry types),
`F = K(·/π)` for the edge cutoff `K`, `E = 2` and `E₁ = 2 - 1/100 < E₂ = 2 + 1/100`; the same law
also gives `H_5000`. -/
example : ∃ CF : ℝ, 0 < CF ∧ (0 : ℝ) ≤ 1 ∧ (1 / 3 : ℝ) < 2 / 5 ∧ (2 / 5 : ℝ) ≤ 1 / 2 ∧
    (0 : ℝ) < 1 / 15 ∧ (1 / 15 : ℝ) < 1 / 10 ∧
    LargeQClass 1 (2 / 5) 1024 lawA ∧
    (∃ Lv γ, LargeQClass 1 (2 / 5) 1024 Lv ∧
      interp (lexPos 1024) 5000 lawA (goeLaws 1024) = interp (lexPos 1024) γ Lv (goeLaws 1024)) ∧
    lexPos 1024 (Sum.inl (4 : Fin 1024)) = 4091 ∧
    (interp (lexPos 1024) (lexPos 1024 (Sum.inl (4 : Fin 1024))) lawA (goeLaws 1024)).diag 4 =
      lawA.diag 4 ∧
    (interp (lexPos 1024) (lexPos 1024 (Sum.inl (4 : Fin 1024)) - 1) lawA (goeLaws 1024)).diag 4 =
      (goeLaws 1024).diag 4 ∧
    ContDiff ℝ 4 (fun x => edgeCutoff (x / Real.pi)) ∧
    (∀ n ∈ Finset.Icc 1 4, ∀ x : ℝ,
      |iteratedDeriv n (fun x => edgeCutoff (x / Real.pi)) x| ≤ CF * (1 + |x|) ^ CF) ∧
    |(2 - 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    |(2 + 1 / 100 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) ∧
    (2 - 1 / 100 : ℝ) < 2 + 1 / 100 ∧
    |(2 : ℝ) - 2| ≤ ((1024 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 15) := by
  obtain ⟨CF, hCF, h⟩ := edgeCutoff_deriv_le
  have hpos : lexPos 1024 (Sum.inl (4 : Fin 1024)) = 4091 := rfl
  refine ⟨CF, hCF, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨lawA_isGenWigner, lawA_supp⟩, ⟨lawA, 5000, ⟨lawA_isGenWigner, lawA_supp⟩, rfl⟩, hpos, ?_, ?_,
    (edgeCutoff_props.1 4).comp (contDiff_id.div_const _), h, ?_, ?_, by norm_num, ?_⟩
  · simp only [interp, le_refl, ite_true]
  · simp only [interp, hpos, show ¬ (4091 ≤ 4091 - 1) by decide, ite_false]
  all_goals
    rw [rpow_1024_window]; norm_num [abs_of_nonneg, abs_of_nonpos]

#print axioms swap_comparison_diag_largeQ

end WEdgeNS
