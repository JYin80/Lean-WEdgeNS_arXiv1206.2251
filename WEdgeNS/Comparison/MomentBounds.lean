import WEdgeNS.Comparison.Classes
import WEdgeNS.Comparison.Monomial

/-!
# Moments of matched entries and coefficient bounds
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private integrable_pow_of_tail lawV lawW lawVW_matchedPair rpow16_quarter
  from WEdgeNS.Comparison.Classes

/-- For an even order `m ≤ k`: `|∫ (-x)^k| ≤ (q⁻¹)^{k-m} ∫ x^m` on the support `|x| ≤ q⁻¹`. -/
private lemma mb_abs_moment_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {q : ℝ}
    (h : μ {x | q⁻¹ < |x|} = 0) (m k : ℕ) (hm : Even m) (hk : m ≤ k) :
    |∫ x, (-x) ^ k ∂μ| ≤ q⁻¹ ^ (k - m) * ∫ x, x ^ m ∂μ := by
  have h1 : ∀ᵐ x ∂μ, ¬ (q⁻¹ < |x|) := by
    rw [ae_iff]; simpa using h
  have hi : Integrable (fun x : ℝ => x ^ m) μ := integrable_pow_of_tail h m
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_ae ?_ (hi.const_mul _) ?_
  · have : Integrable (fun x : ℝ => x ^ k) μ := integrable_pow_of_tail h k
    simpa [norm_neg] using this.norm
  · filter_upwards [h1] with x hx
    have hx' : |x| ≤ q⁻¹ := not_lt.mp hx
    have e : ‖(-x) ^ k‖ = |x| ^ (k - m) * |x| ^ m := by
      rw [norm_pow, norm_neg, Real.norm_eq_abs, ← pow_add, Nat.sub_add_cancel hk]
    change ‖(-x) ^ k‖ ≤ q⁻¹ ^ (k - m) * x ^ m
    rw [e, ← hm.pow_abs x]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) hx' _) (by positivity)

/-- The moments `k ≤ matchedOrder e` agree (Lemma 5.1); `k = 0` included. -/
theorem MatchedPair.entryMoment_eq {N : ℕ} {C1 q : ℝ} {Lv Lw : EntryLaws N}
    (h : MatchedPair C1 q Lv Lw) (e : Fin N ⊕ OffDiag N) (k : ℕ) (hk : k ≤ matchedOrder e) :
    Lv.entryMoment e k = Lw.entryMoment e k := by
  have hv := h.isProb_v.diag; have hv' := h.isProb_v.off
  have hw := h.isProb_w.diag; have hw' := h.isProb_w.off
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rcases e with i | p <;> simp [EntryLaws.entryMoment, EntryLaws.entry]
  · have key : ∀ (μ : Measure ℝ), ∫ x, (-x) ^ k ∂μ = (-1) ^ k * ∫ x, x ^ k ∂μ := fun μ => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => neg_pow x k)
    rcases e with i | p
    · have := h.match_diag i k (Finset.mem_Icc.mpr ⟨hk0, hk⟩)
      simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inl, key, this]
    · have := h.match_off p k (Finset.mem_Icc.mpr ⟨hk0, hk⟩)
      simp only [EntryLaws.entryMoment, EntryLaws.entry, Sum.elim_inr, key, this]

/-- (6.78) with the constant `C1` kept: off the diagonal,
`|E h^k| ≤ C1 log N N^{-2} q^{-(k-4)}` for `k ≥ 4`, at every `H_γ`. -/
theorem MatchedPair.abs_entryMoment_off_le {N : ℕ} {C1 q : ℝ} {Lv Lw : EntryLaws N}
    (h : MatchedPair C1 q Lv Lw) (hq : 0 < q) (γ : ℕ) (p : OffDiag N) (k : ℕ) (hk : 4 ≤ k) :
    |(EntryLaws.interp (lexPos N) γ Lv Lw).entryMoment (Sum.inr p) k| ≤
      C1 * Real.log N / (N : ℝ) ^ 2 * q⁻¹ ^ (k - 4) := by
  have hv' := h.isProb_v.off
  have hw' := h.isProb_w.off
  have hq' : 0 ≤ q⁻¹ ^ (k - 4) := by positivity
  have hv4 := h.fourth_off_le p
  have hw4 : ∫ x, x ^ 4 ∂(Lw.off p) ≤ C1 * Real.log N / (N : ℝ) ^ 2 :=
    (h.match_off p 4 (by simp)).trans_le hv4
  unfold EntryLaws.entryMoment EntryLaws.entry EntryLaws.interp
  dsimp only [Sum.elim_inr]
  split_ifs
  · calc _ ≤ q⁻¹ ^ (k - 4) * ∫ x, x ^ 4 ∂(Lv.off p) :=
          mb_abs_moment_le (h.supp_v.2 p) 4 k (by decide) hk
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hv4 hq'
  · calc _ ≤ q⁻¹ ^ (k - 4) * ∫ x, x ^ 4 ∂(Lw.off p) :=
          mb_abs_moment_le (h.supp_w.2 p) 4 k (by decide) hk
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw4 hq'

/-- The diagonal analogue: `|E h_aa^k| ≤ C1 N⁻¹ q^{-(k-2)}` for `k ≥ 2`. -/
theorem MatchedPair.abs_entryMoment_diag_le {N : ℕ} {C1 q : ℝ} {Lv Lw : EntryLaws N}
    (h : MatchedPair C1 q Lv Lw) (hq : 0 < q) (γ : ℕ) (i : Fin N) (k : ℕ) (hk : 2 ≤ k) :
    |(EntryLaws.interp (lexPos N) γ Lv Lw).entryMoment (Sum.inl i) k| ≤ C1 / N * q⁻¹ ^ (k - 2) := by
  have hv := h.isProb_v.diag
  have hw := h.isProb_w.diag
  have hq' : 0 ≤ q⁻¹ ^ (k - 2) := by positivity
  have hv2 := h.var_diag_le i
  have hw2 : ∫ x, x ^ 2 ∂(Lw.diag i) ≤ C1 / N :=
    (h.match_diag i 2 (by simp)).trans_le hv2
  unfold EntryLaws.entryMoment EntryLaws.entry EntryLaws.interp
  dsimp only [Sum.elim_inl]
  split_ifs
  · calc _ ≤ q⁻¹ ^ (k - 2) * ∫ x, x ^ 2 ∂(Lv.diag i) :=
          mb_abs_moment_le (h.supp_v.1 i) 2 k (by decide) hk
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hv2 hq'
  · calc _ ≤ q⁻¹ ^ (k - 2) * ∫ x, x ^ 2 ∂(Lw.diag i) :=
          mb_abs_moment_le (h.supp_w.1 i) 2 k (by decide) hk
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw2 hq'

/-- `ξ = ⌈2ζ/φq⌉` of (6.46). -/
def xiOf (ζ φq : ℝ) : ℕ := ⌈2 * ζ / φq⌉₊

/-- Coefficient bound of (6.22) (`N^{-2-kφq/10}` off the diagonal) and of its diagonal analogue
(`N^{-1-kφq/4}`), for `k = |α|`. -/
def coeffBound (N : ℕ) (φq : ℝ) : Fin N ⊕ OffDiag N → ℕ → ℝ
  | Sum.inl _, k => (N : ℝ) ^ (-1 - (k : ℝ) * φq / 4)
  | Sum.inr _, k => (N : ℝ) ^ (-2 - (k : ℝ) * φq / 10)

/-- Index vectors `α ∈ ℕ^s` with `m0 < |α| ≤ ξ`. -/
def highIdx (s m0 ξ : ℕ) : Finset (Fin s → ℕ) :=
  (Finset.Icc (m0 + 1) ξ).biUnion fun c => Finset.Nat.antidiagonalTuple s c

/-! ## Nondegenerate instances at `N = 16`, `C1 = 2`, `q = 16^{1/4} = 2` -/

private lemma q16_pos : (0 : ℝ) < ((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
  simp only [Nat.cast_ofNat, rpow16_quarter]; norm_num

/-- An off-diagonal pair of `Fin 16`. -/
private def pair01 : OffDiag 16 := ⟨(0, 1), by decide⟩

/-- The fourth off-diagonal moments of `lawV` and `lawW` agree. -/
example : lawV.entryMoment (Sum.inr pair01) 4 = lawW.entryMoment (Sum.inr pair01) 4 :=
  lawVW_matchedPair.entryMoment_eq _ 4 (by simp [matchedOrder])

/-- The second diagonal moments of `lawV` and `lawW` agree, and `k = 0` is included. -/
example : lawV.entryMoment (Sum.inl (0 : Fin 16)) 2 = lawW.entryMoment (Sum.inl (0 : Fin 16)) 2 :=
  lawVW_matchedPair.entryMoment_eq _ 2 (by simp [matchedOrder])

example : lawV.entryMoment (Sum.inr pair01) 0 = lawW.entryMoment (Sum.inr pair01) 0 :=
  lawVW_matchedPair.entryMoment_eq _ 0 (by simp [matchedOrder])

/-- (6.78) at the interpolation `H_5` of `lawV` and `lawW`, sixth moment. -/
example : |(EntryLaws.interp (lexPos 16) 5 lawV lawW).entryMoment (Sum.inr pair01) 6| ≤
    2 * Real.log (16 : ℕ) / ((16 : ℕ) : ℝ) ^ 2 * (((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4))⁻¹ ^ (6 - 4) :=
  lawVW_matchedPair.abs_entryMoment_off_le q16_pos 5 pair01 6 (by norm_num)

/-- The diagonal analogue at `H_5`, fourth moment. -/
example : |(EntryLaws.interp (lexPos 16) 5 lawV lawW).entryMoment (Sum.inl (0 : Fin 16)) 4| ≤
    2 / ((16 : ℕ) : ℝ) * (((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4))⁻¹ ^ (4 - 2) :=
  lawVW_matchedPair.abs_entryMoment_diag_le q16_pos 5 0 4 (by norm_num)

example : xiOf 1 (1 / 4) = 8 := by
  unfold xiOf
  rw [show 2 * (1 : ℝ) / (1 / 4) = ((8 : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]

example : coeffBound 16 (1 / 4) (Sum.inr pair01) 5 = (16 : ℝ) ^ (-2 - (5 : ℝ) * (1 / 4) / 10) := by
  simp [coeffBound]

example : (highIdx 2 4 6).card = 13 := by decide

example : (highIdx 2 2 4).card = 9 := by decide

#print axioms MatchedPair.entryMoment_eq
#print axioms MatchedPair.abs_entryMoment_off_le
#print axioms MatchedPair.abs_entryMoment_diag_le
#print axioms xiOf
#print axioms coeffBound
#print axioms highIdx

end WEdgeNS
