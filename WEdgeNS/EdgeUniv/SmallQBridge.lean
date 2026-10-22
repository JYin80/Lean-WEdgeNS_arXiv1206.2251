import WEdgeNS.Comparison.RigiditySmallQ
import WEdgeNS.EdgeUniv.LargeQInputs
import WEdgeNS.EdgeUniv.InputsComparison

/-!
# The edge event for the pairs of Theorem 3.7
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The pairs of Theorem 3.7: a law of Theorem 3.6 (almost-sure support) and a Lemma 5.1 match. -/
def SmallQPair (C1 φs : ℝ) (N : ℕ) (Lv Lw : EntryLaws N) : Prop :=
  SmallQClass C1 φs N Lv ∧ Lv.IsMomentMatch Lw C1

/-- For `D > 0` and large `N`, `D log N ≤ N^{1/10}`. -/
private lemma sqb_log_le_rpow (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, D * Real.log N ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := by
  have hev : ∀ᶠ N : ℕ in atTop, 20 * |D| ≤ (N : ℝ) ^ ((1 : ℝ) / 20) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hlog : Real.log N ≤ (N : ℝ) ^ ((1 : ℝ) / 20) / (1 / 20) :=
    Real.log_le_rpow_div hN0 (by norm_num)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hp : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hN0 _
  have h10 : (N : ℝ) ^ ((1 : ℝ) / 10) = (N : ℝ) ^ ((1 : ℝ) / 20) * (N : ℝ) ^ ((1 : ℝ) / 20) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  rw [h10]
  have h1 : Real.log N ≤ 20 * (N : ℝ) ^ ((1 : ℝ) / 20) := by
    have : (N : ℝ) ^ ((1 : ℝ) / 20) / (1 / 20) = 20 * (N : ℝ) ^ ((1 : ℝ) / 20) := by ring
    linarith
  calc D * Real.log N ≤ |D| * Real.log N := mul_le_mul_of_nonneg_right (le_abs_self D) hlog0
    _ ≤ |D| * (20 * (N : ℝ) ^ ((1 : ℝ) / 20)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg D)
    _ = (20 * |D|) * (N : ℝ) ^ ((1 : ℝ) / 20) := by ring
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 20) * (N : ℝ) ^ ((1 : ℝ) / 20) :=
        mul_le_mul_of_nonneg_right hN hp

/-- The support of a Lemma 5.1 match is inside the support `N^{-2/5}` from some `N` on:
`q̃⁻¹ ≤ (N^{2/5})⁻¹` for `q̃ = √N/((2C1+4)C1 log N)`. -/
private lemma sqb_inv_support_le (C1 : ℝ) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N))⁻¹ ≤ ((N : ℝ) ^ ((2 : ℝ) / 5))⁻¹ := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    ((sqb_log_le_rpow ((2 * C1 + 4) * C1)).and (eventually_ge_atTop 2))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hlog, hN2⟩ := hN0 N hN
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < (N : ℝ) ^ ((2 : ℝ) / 5) := Real.rpow_pos_of_pos hNpos _
  set D := (2 * C1 + 4) * C1 with hD
  by_cases hD0 : D ≤ 0
  · have h1 : D * Real.log N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD0 hlogpos.le
    have h2 : Real.sqrt N / (D * Real.log N) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) h1
    exact (inv_nonpos.2 h2).trans (inv_nonneg.2 hpos.le)
  · have hDl : 0 < D * Real.log N := mul_pos (not_le.mp hD0) hlogpos
    refine inv_anti₀ hpos ?_
    rw [le_div_iff₀ hDl]
    have hsq : Real.sqrt N = (N : ℝ) ^ ((2 : ℝ) / 5) * (N : ℝ) ^ ((1 : ℝ) / 10) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]; norm_num
    rw [hsq]
    exact mul_le_mul_of_nonneg_left hlog hpos.le

/-- The match `H̃` of a law of Theorem 3.6 is in the class of Lemma 3.5 with
`C0 = max C1 1` and `φs = 2/5`, from `N0(C1)` on (`q̃ = √N/((2C1+4)C1 log N) ≥ N^{2/5}`). -/
theorem SmallQPair.largeQClass {C1 φs : ℝ} :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ Lv Lw : EntryLaws N, SmallQPair C1 φs N Lv Lw →
      LargeQClass (max C1 1) (2 / 5) N Lw := by
  obtain ⟨N1, hN1⟩ := sqb_inv_support_le C1
  refine ⟨max N1 2, fun N hN Lv Lw hp => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  obtain ⟨⟨hmc, -⟩, hprob, hsupp, hoff, hdiag⟩ := hp
  have hint := hsupp.integrable_pow hprob 2
  have hm1 : ∀ i, ∫ x, x ^ 1 ∂(Lw.diag i) = ∫ x, x ^ 1 ∂(Lv.diag i) :=
    fun i => hdiag i 1 (by simp)
  have hm2 : ∀ i, ∫ x, x ^ 2 ∂(Lw.diag i) = ∫ x, x ^ 2 ∂(Lv.diag i) :=
    fun i => hdiag i 2 (by simp)
  refine ⟨⟨hprob, hint.1, hint.2, fun i => ?_, fun p => ?_, fun p => ?_, fun i => ?_⟩, ?_⟩
  · have := hm1 i
    simp only [pow_one] at this
    rw [this]; exact hmc.mean_diag i
  · have := hoff p 1 (by simp)
    simp only [pow_one] at this
    rw [this]; exact hmc.mean_off p
  · rw [hoff p 2 (by simp)]; exact hmc.var_off p
  · rw [hm2 i]
    have h0 : 0 ≤ ∫ x, x ^ 2 ∂(Lv.diag i) := integral_nonneg fun x => sq_nonneg x
    have h1 := hmc.var_diag_le i
    have hC : C1 / N ≤ max C1 1 * (N : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 hNpos.le)
    have hC' : (N : ℝ)⁻¹ ≤ max C1 1 * (N : ℝ)⁻¹ := by
      calc (N : ℝ)⁻¹ = 1 * (N : ℝ)⁻¹ := (one_mul _).symm
        _ ≤ max C1 1 * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.2 hNpos.le)
    have hinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hNpos.le
    rw [abs_le]
    constructor <;> nlinarith
  · have hle := hN1 N hN1'
    have hsub : {x : ℝ | ((N : ℝ) ^ ((2 : ℝ) / 5))⁻¹ < |x|} ⊆
        {x : ℝ | (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N))⁻¹ < |x|} :=
      fun x hx => lt_of_le_of_lt hle hx
    exact ⟨fun i => measure_mono_null hsub (hsupp.1 i),
      fun p => measure_mono_null hsub (hsupp.2 p)⟩

/-- Both laws of a pair are probability laws. -/
theorem SmallQPair.isProb {C1 φs : ℝ} {N : ℕ} {Lv Lw : EntryLaws N}
    (h : SmallQPair C1 φs N Lv Lw) : Lv.IsProb ∧ Lw.IsProb :=
  ⟨h.1.1.isProb, h.2.1⟩

/-- A larger exponent `C` only enlarges `φ^C`, since `φ ≥ 1` from `N = 3` on. -/
private lemma sqb_phi_rpow_mono {N : ℕ} (hN : 3 ≤ N) {a b : ℝ} (hab : a ≤ b) :
    phi N ^ a ≤ phi N ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by rw [phi_eq_exp hN]; exact Real.one_le_exp (sq_nonneg _)) hab

/-- The event of Lemma 5.6 for the first law of the pairs of Theorem 3.7, for every `C ≥ C0`
((5.17), (5.24), (5.25), (5.26)). -/
theorem edgeInput_smallQPair_v {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ C0 > (0 : ℝ), ∀ C ≥ C0, HighProbOn 1 (fun N L => ∃ Lw, SmallQPair C1 φs N L Lw)
      (fun N _ => edgeInputEvent N C) := by
  obtain ⟨Cn, hCn, hn⟩ := abs_eigenvalues_le_smallQ (C1 := C1) hφs
  obtain ⟨Cs, hCs, hs⟩ := stieltjes_local_smallQ (C1 := C1) hφs
  obtain ⟨Ce, hCe, he⟩ := edge_inputs_smallQ (C1 := C1) hφs
  refine ⟨max Cs Ce, lt_max_of_lt_left hCs, fun C hC => ?_⟩
  have hCs' : Cs ≤ C := le_trans (le_max_left _ _) hC
  have hCe' : Ce ≤ C := le_trans (le_max_right _ _) hC
  refine HighProbOn.mono_eventually ((hn.inter hs).inter (he C hCe'))
    (fun N L ⟨Lw, hp⟩ => hp.1) ?_
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((phi_rpow_le_rpow Cn (c := 1 / 3) (by norm_num)).and (eventually_ge_atTop 3))
  refine ⟨N1, fun N hN L _ ω hω => ?_⟩
  obtain ⟨hφn, hN3⟩ := hN1 N hN
  obtain ⟨⟨hω1, hω2⟩, hω3, hω4⟩ := hω
  have hNpos : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hN1r : (1 : ℝ) ≤ N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  refine ⟨fun α => ?_, fun z hz _ => ?_, hω3, hω4⟩
  · have h1 := hω1 α
    have h2 : phi N ^ Cn * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 := by
      calc phi N ^ Cn * (N : ℝ) ^ (-(2 : ℝ) / 3)
          ≤ (N : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right hφn (Real.rpow_nonneg hNpos.le _)
        _ = (N : ℝ) ^ (-(1 : ℝ) / 3) := by
            rw [← Real.rpow_add hNpos]; norm_num
        _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by norm_num)
    linarith
  · obtain ⟨hre, hlow, hup⟩ := hz
    have hlow' : phi N ^ Cs / N < z.im :=
      lt_of_le_of_lt (div_le_div_of_nonneg_right (sqb_phi_rpow_mono hN3 hCs') hNpos.le) hlow
    have him : 0 < z.im :=
      lt_trans (div_pos (Real.rpow_pos_of_pos (by
        rw [phi_eq_exp hN3]; exact Real.exp_pos _) _) hNpos) hlow
    have hNim : 0 < (N : ℝ) * z.im := mul_pos hNpos him
    exact (hω2 z ⟨hre, hlow', hup⟩).trans
      (div_le_div_of_nonneg_right (sqb_phi_rpow_mono hN3 hCs') hNim.le)

/-- The event of Lemma 5.6 for the matched law of the pairs of Theorem 3.7, for every `C ≥ C0`. -/
theorem edgeInput_smallQPair_w {C1 φs : ℝ} :
    ∃ C0 > (0 : ℝ), ∀ C ≥ C0, HighProbOn 1 (fun N L => ∃ Lv, SmallQPair C1 φs N Lv L)
      (fun N _ => edgeInputEvent N C) := by
  obtain ⟨C₀, hC₀, h⟩ := edgeInput_largeQ (C0 := max C1 1) (φs := 2 / 5)
    (le_max_of_le_right zero_le_one) (by norm_num) (by norm_num)
  obtain ⟨Nb, hb⟩ := SmallQPair.largeQClass (C1 := C1) (φs := φs)
  refine ⟨C₀, hC₀, fun C hC => ?_⟩
  obtain ⟨c, hc, C', hC', N0, hN0⟩ := h C hC
  refine ⟨c, hc, C', hC', max N0 Nb, fun N hN L hL => ?_⟩
  obtain ⟨Lv, hp⟩ := hL
  exact hN0 N (le_of_max_le_left hN) L (hb N (le_of_max_le_right hN) Lv L hp)

/-! ### Compiled checks -/

/-- The inputs `hprob`, `hv`, `hw` of Lemma 5.6 for the pairs of Theorem 3.7. -/
example {C1 φs : ℝ} (hφs : 0 < φs) (hcomp : GreenCompHyp (SmallQPair C1 φs) φs) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ Lv Lw : EntryLaws N, SmallQPair C1 φs N Lv Lw →
      ∀ s : ℝ, edgeCdfL Lw (s - (N : ℝ) ^ (-δ)) - (N : ℝ) ^ (-δ) ≤ edgeCdfL Lv s ∧
        edgeCdfL Lv s ≤ edgeCdfL Lw (s + (N : ℝ) ^ (-δ)) + (N : ℝ) ^ (-δ) :=
  edge_universality_of_inputs hφs (fun _ _ _ h => SmallQPair.isProb h)
    (edgeInput_smallQPair_v hφs) edgeInput_smallQPair_w hcomp

open private lawV lawW lawV_momentCond lawV_supp lawVW_isMomentMatch
  from WEdgeNS.Comparison.Classes

/-! Entry laws of the check at `N = 16`: `H^v` has off-diagonal values `±1/2` with probability
`1/10` each, `±1/8` with probability `2/5` each, and diagonal values `±1/4`; `H̃` has off-diagonal
values `0` with probability `9/16`, `±1/4` with probability `1/8` each, `±1/2` with probability
`3/32` each, and diagonal values `0` with probability `3/4`, `±1/2` with probability `1/8` each. -/

/-- A pair of Theorem 3.7 at a nondegenerate point: `N = 16`, `C1 = 2`, `φs = 1/4`; `H̃` has an
atom at `0`, `H^v` has none; the off-diagonal moments `1–4` and the diagonal moments `1–2` agree. -/
example : SmallQPair 2 (1 / 4) 16 lawV lawW := ⟨⟨lawV_momentCond, lawV_supp⟩, lawVW_isMomentMatch⟩

#print axioms SmallQPair.largeQClass
#print axioms SmallQPair.isProb
#print axioms edgeInput_smallQPair_v
#print axioms edgeInput_smallQPair_w

end WEdgeNS
