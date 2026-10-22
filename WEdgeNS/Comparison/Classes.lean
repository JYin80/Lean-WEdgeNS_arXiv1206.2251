import WEdgeNS.Moments.Matching
import WEdgeNS.Model.Ensembles
import WEdgeNS.Model.TestLaws

/-!
# Classes of entry laws for the small-support comparison
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

namespace EntryLaws

variable {N : ℕ}

/-- `Lw` is a moment match of `Lv` as produced by Lemma 5.1: probability laws, almost surely
bounded by `(√N / ((2C1+4) C1 log N))⁻¹`, off-diagonal moments `1–4` and diagonal moments `1–2`
equal to those of `Lv`. -/
def IsMomentMatch (Lv Lw : EntryLaws N) (C1 : ℝ) : Prop :=
  Lw.IsProb ∧ Lw.BoundedSupportAS (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) ∧
    (∀ p, ∀ k ∈ Finset.Icc 1 4, ∫ x, x ^ k ∂(Lw.off p) = ∫ x, x ^ k ∂(Lv.off p)) ∧
    (∀ i, ∀ k ∈ Finset.Icc 1 2, ∫ x, x ^ k ∂(Lw.diag i) = ∫ x, x ^ k ∂(Lv.diag i))

/-- Lemma 5.1 in the `IsMomentMatch` form. -/
theorem exists_isMomentMatch (hN : 3 ≤ N) {C1 : ℝ} {L : EntryLaws N} (hL : L.MomentCond C1) :
    ∃ L', L.IsMomentMatch L' C1 :=
  exists_momentMatched hN hL

/-- A measure that gives no mass to `{x | q⁻¹ < |x|}` has integrable monomials. -/
private lemma integrable_pow_of_tail {μ : Measure ℝ} [IsFiniteMeasure μ] {q : ℝ}
    (h : μ {x | q⁻¹ < |x|} = 0) (k : ℕ) : Integrable (fun x : ℝ => x ^ k) μ := by
  refine Integrable.of_bound (continuous_pow k).aestronglyMeasurable (|q⁻¹| ^ k) ?_
  have h1 : ∀ᵐ x ∂μ, ¬ (q⁻¹ < |x|) := by
    rw [ae_iff]; simpa using h
  filter_upwards [h1] with x hx
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg x) ((not_lt.mp hx).trans (le_abs_self _)) k

/-- Almost surely bounded probability laws have all polynomial moments. -/
theorem BoundedSupportAS.integrable_pow {L : EntryLaws N} {q : ℝ} (h : L.BoundedSupportAS q)
    (hL : L.IsProb) (k : ℕ) :
    (∀ i, Integrable (fun x : ℝ => x ^ k) (L.diag i)) ∧
      ∀ p, Integrable (fun x : ℝ => x ^ k) (L.off p) := by
  have := hL.diag; have := hL.off
  exact ⟨fun i => integrable_pow_of_tail (h.1 i) k, fun p => integrable_pow_of_tail (h.2 p) k⟩

end EntryLaws

/-- The class of Theorem 3.6 with the almost-sure support condition: the moment conditions with
`C1` and `|h_ij| ≤ N^{-φs}` almost surely. -/
def SmallQClass (C1 φs : ℝ) (N : ℕ) (L : EntryLaws N) : Prop :=
  L.MomentCond C1 ∧ L.BoundedSupportAS ((N : ℝ) ^ φs)

/-- A pair of entry laws as in Lemma 5.1, both almost surely bounded by `q⁻¹`: `Lv` has mean zero,
off-diagonal variance `N⁻¹`, diagonal variance at most `C1/N` and off-diagonal fourth moment at most
`C1 log N / N²`; `Lw` matches the off-diagonal moments `1–4` and the diagonal moments `1–2`. -/
structure MatchedPair {N : ℕ} (C1 q : ℝ) (Lv Lw : EntryLaws N) : Prop where
  isProb_v : Lv.IsProb
  isProb_w : Lw.IsProb
  supp_v : Lv.BoundedSupportAS q
  supp_w : Lw.BoundedSupportAS q
  mean_diag : ∀ i, ∫ x, x ∂(Lv.diag i) = 0
  mean_off : ∀ p, ∫ x, x ∂(Lv.off p) = 0
  var_diag_le : ∀ i, ∫ x, x ^ 2 ∂(Lv.diag i) ≤ C1 / N
  var_off : ∀ p, ∫ x, x ^ 2 ∂(Lv.off p) = (N : ℝ)⁻¹
  fourth_off_le : ∀ p, ∫ x, x ^ 4 ∂(Lv.off p) ≤ C1 * Real.log N / (N : ℝ) ^ 2
  match_off : ∀ p, ∀ k ∈ Finset.Icc 1 4, ∫ x, x ^ k ∂(Lw.off p) = ∫ x, x ^ k ∂(Lv.off p)
  match_diag : ∀ i, ∀ k ∈ Finset.Icc 1 2, ∫ x, x ^ k ∂(Lw.diag i) = ∫ x, x ^ k ∂(Lv.diag i)

/-- The interpolations `H_γ` (3.21) of matched pairs with support `q ≥ N^{φq}`. -/
def PairInterpClass (C1 φq : ℝ) (N : ℕ) (L : EntryLaws N) : Prop :=
  ∃ (Lv Lw : EntryLaws N) (q : ℝ) (γ : ℕ), MatchedPair C1 q Lv Lw ∧ (N : ℝ) ^ φq ≤ q ∧
    L = interp (lexPos N) γ Lv Lw

/-- The interpolations `H_γ` between a law of Theorem 3.6 and its Lemma 5.1 match. -/
def SmallQInterpClass (C1 φs : ℝ) (N : ℕ) (L : EntryLaws N) : Prop :=
  ∃ (Lv Lw : EntryLaws N) (γ : ℕ), SmallQClass C1 φs N Lv ∧ Lv.IsMomentMatch Lw C1 ∧
    L = interp (lexPos N) γ Lv Lw

/-- `H_{γ₀}` against `H̃` is again a matched pair (used for (6.82)). -/
theorem MatchedPair.interp {N : ℕ} {C1 q : ℝ} {Lv Lw : EntryLaws N}
    (h : MatchedPair C1 q Lv Lw) (γ : ℕ) : MatchedPair C1 q (interp (lexPos N) γ Lv Lw) Lw := by
  have hd : ∀ i, (EntryLaws.interp (lexPos N) γ Lv Lw).diag i = Lv.diag i ∨
      (EntryLaws.interp (lexPos N) γ Lv Lw).diag i = Lw.diag i := fun i => by
    unfold EntryLaws.interp; dsimp only; split_ifs <;> simp
  have ho : ∀ p, (EntryLaws.interp (lexPos N) γ Lv Lw).off p = Lv.off p ∨
      (EntryLaws.interp (lexPos N) γ Lv Lw).off p = Lw.off p := fun p => by
    unfold EntryLaws.interp; dsimp only; split_ifs <;> simp
  have m1d : ∀ i, ∫ x, x ∂(Lw.diag i) = ∫ x, x ∂(Lv.diag i) := fun i => by
    simpa using h.match_diag i 1 (by simp)
  have m1o : ∀ p, ∫ x, x ∂(Lw.off p) = ∫ x, x ∂(Lv.off p) := fun p => by
    simpa using h.match_off p 1 (by simp)
  have m2d : ∀ i, ∫ x, x ^ 2 ∂(Lw.diag i) = ∫ x, x ^ 2 ∂(Lv.diag i) := fun i =>
    h.match_diag i 2 (by simp)
  have m2o : ∀ p, ∫ x, x ^ 2 ∂(Lw.off p) = ∫ x, x ^ 2 ∂(Lv.off p) := fun p =>
    h.match_off p 2 (by simp)
  have m4o : ∀ p, ∫ x, x ^ 4 ∂(Lw.off p) = ∫ x, x ^ 4 ∂(Lv.off p) := fun p =>
    h.match_off p 4 (by simp)
  refine ⟨⟨fun i => ?_, fun p => ?_⟩, h.isProb_w, ⟨fun i => ?_, fun p => ?_⟩, h.supp_w,
    fun i => ?_, fun p => ?_, fun i => ?_, fun p => ?_, fun p => ?_, fun p k hk => ?_,
    fun i k hk => ?_⟩
  · rcases hd i with e | e <;> rw [e]
    exacts [h.isProb_v.diag i, h.isProb_w.diag i]
  · rcases ho p with e | e <;> rw [e]
    exacts [h.isProb_v.off p, h.isProb_w.off p]
  · rcases hd i with e | e <;> rw [e]
    exacts [h.supp_v.1 i, h.supp_w.1 i]
  · rcases ho p with e | e <;> rw [e]
    exacts [h.supp_v.2 p, h.supp_w.2 p]
  · rcases hd i with e | e <;> rw [e]
    exacts [h.mean_diag i, (m1d i).trans (h.mean_diag i)]
  · rcases ho p with e | e <;> rw [e]
    exacts [h.mean_off p, (m1o p).trans (h.mean_off p)]
  · rcases hd i with e | e <;> rw [e]
    exacts [h.var_diag_le i, (m2d i).trans_le (h.var_diag_le i)]
  · rcases ho p with e | e <;> rw [e]
    exacts [h.var_off p, (m2o p).trans (h.var_off p)]
  · rcases ho p with e | e <;> rw [e]
    exacts [h.fourth_off_le p, (m4o p).trans_le (h.fourth_off_le p)]
  · rcases ho p with e | e <;> rw [e]
    exact h.match_off p k hk
  · rcases hd i with e | e <;> rw [e]
    exact h.match_diag i k hk

/-- Shrinking the support: a law that is almost surely bounded by `r⁻¹` is almost surely bounded
by `q⁻¹` whenever `0 < q ≤ r`. -/
private lemma tail_zero_mono {μ : Measure ℝ} {q r : ℝ} (hq : 0 < q) (hqr : q ≤ r)
    (h : μ {x | r⁻¹ < |x|} = 0) : μ {x | q⁻¹ < |x|} = 0 :=
  measure_mono_null (fun _ hx => lt_of_le_of_lt (inv_anti₀ hq hqr) hx) h

/-- A law with nonzero second moment that is almost surely bounded by `q⁻¹` has `q > 0`. -/
private lemma pos_of_tail_zero {μ : Measure ℝ} {q : ℝ} (h : μ {x | q⁻¹ < |x|} = 0)
    (hv : ∫ x, x ^ 2 ∂μ ≠ 0) : 0 < q := by
  by_contra hq
  have hq' : q⁻¹ ≤ 0 := inv_nonpos.mpr (not_lt.mp hq)
  have h0 : ∀ᵐ x ∂μ, x = 0 := by
    have : μ {x : ℝ | 0 < |x|} = 0 := measure_mono_null (fun _ hx => lt_of_le_of_lt hq' hx) h
    rw [ae_iff]; simpa using this
  apply hv
  rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by filter_upwards [h0] with x hx; simp [hx])]
  simp

/-- The support parameter of Lemma 5.1 is positive for a Lemma 5.1 match of a law with the moment
conditions of Theorem 3.6. -/
private lemma tilde_pos {N : ℕ} (hN : 3 ≤ N) {C1 : ℝ} {Lv Lw : EntryLaws N}
    (hv : Lv.MomentCond C1) (hw : Lv.IsMomentMatch Lw C1) :
    0 < Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N) := by
  let p : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  refine pos_of_tail_zero (hw.2.1.2 p) ?_
  rw [hw.2.2.1 p 2 (by simp), hv.var_off p]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))

/-- `N^{1/4} ≤ √N / (K log N)` for `K > 0` and `N ≥ (8K)^8`. -/
private lemma rpow_quarter_le_tilde {N : ℕ} (hN : 3 ≤ N) {K : ℝ} (hK : 0 < K)
    (hNK : (8 * K) ^ 8 ≤ (N : ℝ)) :
    (N : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt N / (K * Real.log N) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set a : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have h4 : (N : ℝ) ^ ((1 : ℝ) / 4) = a ^ 2 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have h2 : Real.sqrt N = a ^ 4 := by
    rw [Real.sqrt_eq_rpow, ha, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hlog_le : Real.log N ≤ 8 * a := by
    have := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 1 / 8 by norm_num)
    calc Real.log N ≤ (N : ℝ) ^ ((1 : ℝ) / 8) / (1 / 8) := this
      _ = 8 * a := by rw [← ha]; ring
  have hKa : 8 * K ≤ a := by
    have h1 : ((8 * K) ^ 8) ^ (((8 : ℕ) : ℝ)⁻¹) ≤ (N : ℝ) ^ (((8 : ℕ) : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) hNK (by positivity)
    rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at h1
    simpa [ha, one_div] using h1
  rw [h4, h2, le_div_iff₀ (by positivity)]
  calc a ^ 2 * (K * Real.log N) ≤ a ^ 2 * (K * (8 * a)) := by gcongr
    _ = a ^ 3 * (8 * K) := by ring
    _ ≤ a ^ 3 * a := by gcongr
    _ = a ^ 4 := by ring

/-- A law of Theorem 3.6 and its match form a matched pair with
`q = min(N^{φs}, √N/((2C1+4)C1 log N))`. -/
theorem MatchedPair.of_smallQ {N : ℕ} {C1 φs : ℝ} (hN : 3 ≤ N) {Lv Lw : EntryLaws N}
    (hv : SmallQClass C1 φs N Lv) (hw : Lv.IsMomentMatch Lw C1) :
    MatchedPair C1 (min ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N))) Lv Lw := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hq0 : 0 < min ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) :=
    lt_min (Real.rpow_pos_of_pos hN0 _) (tilde_pos hN hv.1 hw)
  exact ⟨hv.1.isProb, hw.1,
    ⟨fun i => tail_zero_mono hq0 (min_le_left _ _) (hv.2.1 i),
      fun p => tail_zero_mono hq0 (min_le_left _ _) (hv.2.2 p)⟩,
    ⟨fun i => tail_zero_mono hq0 (min_le_right _ _) (hw.2.1.1 i),
      fun p => tail_zero_mono hq0 (min_le_right _ _) (hw.2.1.2 p)⟩,
    hv.1.mean_diag, hv.1.mean_off, hv.1.var_diag_le, hv.1.var_off, hv.1.fourth_off_le,
    hw.2.2.1, hw.2.2.2⟩

/-- `SmallQInterpClass ⊆ PairInterpClass` with `φq = min(φs, 1/4)`, for `N ≥ N0(C1)`. -/
theorem smallQInterp_pairInterp {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, SmallQInterpClass C1 φs N L →
      PairInterpClass C1 (min φs (1 / 4)) N L := by
  -- the argument holds for every `φs`; the hypothesis `0 < φs` is not needed
  have _ := hφs
  refine ⟨max 3 ⌈(8 * ((2 * C1 + 4) * C1)) ^ 8⌉₊, fun N hN L hL => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hNc : (8 * ((2 * C1 + 4) * C1)) ^ 8 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  obtain ⟨Lv, Lw, γ, hv, hw, rfl⟩ := hL
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hK : 0 < (2 * C1 + 4) * C1 := by
    have h1 : 0 < (2 * C1 + 4) * C1 * Real.log N :=
      (div_pos_iff_of_pos_left (Real.sqrt_pos.mpr hN0)).1 (tilde_pos hN3 hv.1 hw)
    exact (mul_pos_iff_of_pos_right hlog).1 h1
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  refine ⟨Lv, Lw, _, γ, MatchedPair.of_smallQ hN3 hv hw, le_min ?_ ?_, rfl⟩
  · exact Real.rpow_le_rpow_of_exponent_le h1N (min_le_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le h1N (min_le_right _ _)).trans
      (rpow_quarter_le_tilde hN3 hK hNc)

/-- A matched pair is a pair of generalized Wigner laws (Definition 2.1). -/
theorem MatchedPair.isGenWigner {N : ℕ} {C1 q : ℝ} {Lv Lw : EntryLaws N}
    (h : MatchedPair C1 q Lv Lw) : Lv.IsGenWigner (max C1 1) ∧ Lw.IsGenWigner (max C1 1) := by
  have hN0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hM1 : C1 ≤ max C1 1 := le_max_left _ _
  have hM2 : 1 ≤ max C1 1 := le_max_right _ _
  have hvd : ∀ i, |∫ x, x ^ 2 ∂(Lv.diag i) - (N : ℝ)⁻¹| ≤ max C1 1 * (N : ℝ)⁻¹ := fun i => by
    have h0 : 0 ≤ ∫ x, x ^ 2 ∂(Lv.diag i) := integral_nonneg (fun x => sq_nonneg x)
    have h1 := h.var_diag_le i
    rw [div_eq_mul_inv] at h1
    rw [abs_le]
    constructor <;> nlinarith
  have iv := h.supp_v.integrable_pow h.isProb_v 2
  have iw := h.supp_w.integrable_pow h.isProb_w 2
  exact ⟨⟨h.isProb_v, iv.1, iv.2, h.mean_diag, h.mean_off, h.var_off, hvd⟩,
    ⟨h.isProb_w, iw.1, iw.2,
      fun i => by
        have := h.match_diag i 1 (by simp)
        simp only [pow_one] at this
        rw [this]; exact h.mean_diag i,
      fun p => by
        have := h.match_off p 1 (by simp)
        simp only [pow_one] at this
        rw [this]; exact h.mean_off p,
      fun p => (h.match_off p 2 (by simp)).trans (h.var_off p),
      fun i => by rw [h.match_diag i 2 (by simp)]; exact hvd i⟩⟩

/-! ## Nondegenerate instances at `N = 16` -/

/-- Off-diagonal law of `H^v` at `N = 16` (scale `h`): `±1/2` w.p. `1/10` each, `±1/8` w.p. `2/5`
each. -/
private noncomputable def offV : List ℝ := [1/2, -1/2, 1/8, 1/8, 1/8, 1/8, -1/8, -1/8, -1/8, -1/8]
/-- Off-diagonal law of `H̃`: `0` w.p. `9/16`, `±1/4` w.p. `1/8` each, `±1/2` w.p. `3/32` each. -/
private noncomputable def offW : List ℝ :=
  List.replicate 18 0 ++ List.replicate 4 (1/4) ++ List.replicate 4 (-1/4) ++
  List.replicate 3 (1/2) ++ List.replicate 3 (-1/2)
private noncomputable def diagV : List ℝ := [1/4, -1/4]
private noncomputable def diagW : List ℝ := [0, 0, 0, 0, 0, 0, 1/2, -1/2]

private noncomputable def lawV : EntryLaws 16 := ⟨fun _ => unifList diagV, fun _ => unifList offV⟩
private noncomputable def lawW : EntryLaws 16 := ⟨fun _ => unifList diagW, fun _ => unifList offW⟩

private lemma rpow16_quarter : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
  rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num

private lemma rpow16_neg_three_halves : (16 : ℝ) ^ (-(3 : ℝ) / 2) = 1 / 64 := by
  rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  rw [show (4 : ℝ) * (-(3 : ℝ) / 2) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
    Real.rpow_natCast]
  norm_num

private lemma log16_ge : (13 : ℝ) / 8 ≤ Real.log 16 := by
  have := Real.log_two_gt_d9
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith

private lemma lawV_isProb : lawV.IsProb :=
  ⟨fun _ => unifList_prob _ (by simp [diagV]), fun _ => unifList_prob _ (by simp [offV])⟩

private lemma lawW_isProb : lawW.IsProb :=
  ⟨fun _ => unifList_prob _ (by simp [diagW]), fun _ => unifList_prob _ (by simp [offW])⟩

/-- `H^v` at `N = 16` satisfies the moment conditions of Theorem 3.6 with `C1 = 2`. -/
private lemma lawV_momentCond : lawV.MomentCond 2 := by
  refine ⟨lawV_isProb, fun _ => integrable_unifList _ (by simp [diagV]) _,
    fun _ => integrable_unifList _ (by simp [offV]) _, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · simp only [lawV]; rw [integral_unifList]; norm_num [diagV]
  · simp only [lawV]; rw [integral_unifList]; norm_num [offV]
  · simp only [lawV]; rw [integral_unifList]; norm_num [diagV]
  · simp only [lawV]; rw [integral_unifList]; norm_num [offV]
  · simp only [lawV]; rw [integral_unifList]
    simp only [Nat.cast_ofNat, rpow16_neg_three_halves]; norm_num [offV, abs_of_pos]
  · simp only [lawV]; rw [integral_unifList]
    simp only [Nat.cast_ofNat]
    have := log16_ge
    rw [le_div_iff₀ (by norm_num)]
    norm_num [offV]; linarith

/-- `|h| ≤ 16^{-1/4} = 1/2` almost surely for `H^v` and `H̃`. -/
private lemma lawV_supp : lawV.BoundedSupportAS (((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) := by
  simp only [Nat.cast_ofNat, rpow16_quarter]
  refine ⟨fun _ => unifList_tail _ _ ?_, fun _ => unifList_tail _ _ ?_⟩
  · intro a ha
    simp only [diagV, one_div, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> norm_num [abs_of_pos]
  · intro a ha
    simp only [offV, one_div, List.mem_cons, List.not_mem_nil, or_false, or_self,
      or_self_left] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> norm_num [abs_of_pos]

private lemma lawW_supp : lawW.BoundedSupportAS (((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) := by
  simp only [Nat.cast_ofNat, rpow16_quarter]
  refine ⟨fun _ => unifList_tail _ _ ?_, fun _ => unifList_tail _ _ ?_⟩
  · intro a ha
    simp only [diagW, one_div, List.mem_cons, List.not_mem_nil, or_false, or_self_left] at ha
    rcases ha with rfl | rfl | rfl <;> norm_num [abs_of_pos]
  · intro a ha
    simp only [offW, List.reduceReplicate, one_div, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, or_self, or_self_left] at ha
    rcases ha with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      norm_num [abs_of_pos]


private lemma unifList_tail_le (l : List ℝ) (q b : ℝ) (hb : b ≤ q⁻¹) (h : ∀ a ∈ l, |a| ≤ b) :
    unifList l {x | q⁻¹ < |x|} = 0 :=
  unifList_tail l q fun a ha => (h a ha).trans hb

private lemma offW_abs (a : ℝ) (ha : a ∈ offW) : |a| ≤ 1 / 2 := by
  simp only [offW, List.reduceReplicate, one_div, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, or_self, or_self_left] at ha
  rcases ha with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num [abs_of_pos]

private lemma diagW_abs (a : ℝ) (ha : a ∈ diagW) : |a| ≤ 1 / 2 := by
  simp only [diagW, one_div, List.mem_cons, List.not_mem_nil, or_false, or_self_left] at ha
  rcases ha with rfl | rfl | rfl <;> norm_num [abs_of_pos]

/-- A law of Theorem 3.6 with the almost-sure support condition at a nondegenerate point:
`N = 16`, `C1 = 2`, `φs = 1/4`; the off-diagonal entries take the extreme values
`±N^{-1/4} = ±1/2` with probability `1/5`. -/
example : SmallQClass 2 (1 / 4) 16 lawV := ⟨lawV_momentCond, lawV_supp⟩

/-- A matched pair with different laws: `H̃` has an atom at `0` of mass `9/16`
off the diagonal and `3/4` on it, while `H^v` has none; moments `1–4` (off) and `1–2` (diagonal)
agree. -/
private lemma lawVW_matchedPair : MatchedPair 2 (((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) lawV lawW := by
  refine ⟨lawV_isProb, lawW_isProb, lawV_supp, lawW_supp, lawV_momentCond.mean_diag,
    lawV_momentCond.mean_off, lawV_momentCond.var_diag_le, lawV_momentCond.var_off,
    lawV_momentCond.fourth_off_le, ?_, ?_⟩
  · intro p k hk
    simp only [Finset.mem_Icc] at hk
    simp only [lawV, lawW]; rw [integral_unifList, integral_unifList]
    obtain ⟨hk1, hk4⟩ := hk
    interval_cases k <;> norm_num [offV, offW]
  · intro i k hk
    simp only [Finset.mem_Icc] at hk
    simp only [lawV, lawW]; rw [integral_unifList, integral_unifList]
    obtain ⟨hk1, hk2⟩ := hk
    interval_cases k <;> norm_num [diagV, diagW]

example : MatchedPair 2 (((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) lawV lawW := lawVW_matchedPair

/-- `lawW` is a Lemma 5.1 match of `lawV`: `q̃⁻¹ = 4 log 16 ≥ 1/2`. -/
private lemma lawVW_isMomentMatch : lawV.IsMomentMatch lawW 2 := by
  have hs : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have hl := log16_ge
  have hq : (1 : ℝ) / 2 ≤
      (Real.sqrt ((16 : ℕ) : ℝ) / ((2 * 2 + 4) * 2 * Real.log ((16 : ℕ) : ℝ)))⁻¹ := by
    simp only [Nat.cast_ofNat, hs]
    rw [inv_div, le_div_iff₀ (by norm_num)]; nlinarith
  refine ⟨lawW_isProb, ⟨fun _ => unifList_tail_le _ _ _ hq diagW_abs,
    fun _ => unifList_tail_le _ _ _ hq offW_abs⟩, lawVW_matchedPair.match_off,
    lawVW_matchedPair.match_diag⟩

example : lawV.IsMomentMatch lawW 2 := lawVW_isMomentMatch

/-- The interpolation `H_5` (entries with `lexPos ≤ 5` from `H^v`, the others from `H̃`)
lies in both interpolation classes. -/
example : PairInterpClass 2 (1 / 4) 16 (interp (lexPos 16) 5 lawV lawW) :=
  ⟨lawV, lawW, _, 5, lawVW_matchedPair, le_refl _, rfl⟩

example : SmallQInterpClass 2 (1 / 4) 16 (interp (lexPos 16) 5 lawV lawW) :=
  ⟨lawV, lawW, 5, ⟨lawV_momentCond, lawV_supp⟩, lawVW_isMomentMatch, rfl⟩

example : ∃ L', lawV.IsMomentMatch L' 2 := exists_isMomentMatch (by norm_num) lawV_momentCond

example : Integrable (fun x : ℝ => x ^ 4) (lawV.off ⟨(0, 1), by decide⟩) :=
  (lawV_supp.integrable_pow lawV_isProb 4).2 _

example : MatchedPair 2 (((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) (interp (lexPos 16) 5 lawV lawW) lawW :=
  lawVW_matchedPair.interp 5

example : MatchedPair 2 (min (((16 : ℕ) : ℝ) ^ ((1 : ℝ) / 4))
    (Real.sqrt ((16 : ℕ) : ℝ) / ((2 * 2 + 4) * 2 * Real.log ((16 : ℕ) : ℝ)))) lawV lawW :=
  MatchedPair.of_smallQ (by norm_num) ⟨lawV_momentCond, lawV_supp⟩ lawVW_isMomentMatch

example : lawV.IsGenWigner (max 2 1) ∧ lawW.IsGenWigner (max 2 1) :=
  lawVW_matchedPair.isGenWigner

example : ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, SmallQInterpClass 2 (1 / 4) N L →
    PairInterpClass 2 (min (1 / 4) (1 / 4)) N L :=
  smallQInterp_pairInterp (by norm_num)

#print axioms EntryLaws.exists_isMomentMatch
#print axioms EntryLaws.BoundedSupportAS.integrable_pow
#print axioms MatchedPair.interp
#print axioms MatchedPair.of_smallQ
#print axioms smallQInterp_pairInterp
#print axioms MatchedPair.isGenWigner

end WEdgeNS
