import WEdgeNS.EdgeUniv.LargeQClass
import WEdgeNS.LocalLaw.Interface
import WEdgeNS.Comparison.Telescope
import WEdgeNS.Model.HighProbCalc

/-!
# The a priori bound on the resolvent along the interpolation to the GOE
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- `y = η² Σ_{i ≠ j} |G_ij|²` of (3.20), (3.33). -/
def offWard {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  z.im ^ 2 * ∑ i, ∑ j, if i = j then 0 else ‖resolventC H z i j‖ ^ 2

/-- `x = η ∫_{E₁}^{E₂} Σ_{i ≠ j} |G_ij(y + iη)|² dy` ([16] (6.56); off-diagonal part of [26]
(6.31)). -/
def offWardInt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (η E₁ E₂ : ℝ) : ℝ :=
  η * ∫ y in E₁..E₂, ∑ i, ∑ j, if i = j then 0 else ‖resolventC H ⟨y, η⟩ i j‖ ^ 2

/-- The diagonal part removed in (3.20) is `η² Σ_i |G_ii|²`. -/
theorem ward_sub_offWard {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    z.im ^ 2 * ∑ i, ∑ j, ‖resolventC H z i j‖ ^ 2 - offWard H z =
      z.im ^ 2 * ∑ i, ‖resolventC H z i i‖ ^ 2 := by
  unfold offWard
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  simp [sub_ite]

-- The upper GOE entry laws are `N(0, 1/N)`.
open private goeLaws_off from WEdgeNS.Model.Transfer

/-! ### Exponent bookkeeping -/

/-- `(x^a)² = x^(2a)`. -/
private lemma apriori_sq_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num [mul_comm]

/-! ### The size of the error of (3.3) on `I_ε` -/

/-- `Im m_sc ≤ C √(κ + η)` on `|E| ≤ 5`, `0 < η ≤ 10`: the two regimes of Lemma 2.6 combined. -/
private lemma apriori_im_msc : ∃ Cm : ℝ, 1 ≤ Cm ∧ ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
    (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im) := by
  obtain ⟨Cm, hCm, h⟩ := msc_bounds
  refine ⟨Cm, hCm, fun z hre him h10 => ?_⟩
  obtain ⟨-, -, h3, h4⟩ := h z hre him h10
  by_cases hk : kappa z.re ≤ z.im
  · exact (h4 (Or.inl hk)).2
  by_cases he : |z.re| ≤ 2
  · exact (h4 (Or.inr he)).2
  have hk' := not_le.mp hk
  have he' := not_le.mp he
  refine (h3 hk'.le he'.le).2.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
  have hκ : 0 ≤ kappa z.re := abs_nonneg _
  have ht : 0 < Real.sqrt (kappa z.re + z.im) := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_iff₀ ht, Real.mul_self_sqrt (by linarith)]
  linarith

/-- For `E ∈ I_ε` and `η = N^{-2/3-ε}`: the point `E + iη` lies in `S(C)` and the right side of
(3.3) at `q = N^φp` is at most `N^{-1/3+2ε}`, as soon as `φ^C ≤ N^{ε/2}` and
`2 + 2 C_m ≤ N^{ε/2}`. -/
private lemma apriori_domain_err {N : ℕ} {ε C φp Cm : ℝ} (hN : 2 ≤ N) (hε : 0 < ε)
    (hε' : ε < 1 / 10) (hφp : 1 / 3 ≤ φp) (hCm : 1 ≤ Cm)
    (him : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
      (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im))
    (hC : phi N ^ C ≤ (N : ℝ) ^ (ε / 2)) (hK : 2 + 2 * Cm ≤ (N : ℝ) ^ (ε / 2)) {E : ℝ}
    (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) :
    (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ) ∈ specDomain N C ∧
      entryErr N C ((N : ℝ) ^ φp) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) := by
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hn0 : (0 : ℝ) < N := by linarith
  have hη0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hr1 : (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1.le (by linarith)
  have hηr : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
  have hA0 : 0 < (N : ℝ) ^ (-(1 : ℝ) / 3 + ε) := Real.rpow_pos_of_pos hn0 _
  have hrA : (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) ≤ ((N : ℝ) ^ (-(1 : ℝ) / 3 + ε)) ^ 2 := by
    rw [apriori_sq_rpow hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
  have hNη : 1 / ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) = (N : ℝ) ^ (-(1 : ℝ) / 3 + ε) := by
    have h1 : (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) = (N : ℝ) ^ (1 / 3 - ε) := by
      have h := Real.rpow_add hn0 1 (-(2 : ℝ) / 3 - ε)
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    rw [h1, one_div, ← Real.rpow_neg hn0.le]
    congr 1
    ring
  obtain ⟨hE1, hE2⟩ := abs_le.1 hE
  have hE0 : 0 < E := by linarith
  have hre : |E| ≤ 5 := by rw [abs_of_pos hE0]; linarith
  have hκ : kappa E ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
    rw [kappa, abs_of_pos hE0]
    exact hE
  have hη1 : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) ≤ 10 := by linarith
  refine ⟨⟨hre, ?_, hη1⟩, ?_⟩
  · change phi N ^ C / N < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)
    calc phi N ^ C / N ≤ (N : ℝ) ^ (ε / 2) / N := by gcongr
      _ = (N : ℝ) ^ (ε / 2 - 1) := (Real.rpow_sub_one hn0.ne' _).symm
      _ < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_lt_rpow_of_exponent_lt hn1 (by linarith)
  · have hsq : Real.sqrt (kappa E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ≤
        2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + ε) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith
    have hIm : (msc (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ)).im ≤
        Cm * (2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + ε)) :=
      (him ⟨E, _⟩ hre hη0 hη1).trans (mul_le_mul_of_nonneg_left hsq (by linarith))
    have hq : 1 / (N : ℝ) ^ φp ≤ (N : ℝ) ^ (-(1 : ℝ) / 3 + ε) := by
      rw [one_div, ← Real.rpow_neg hn0.le]
      exact Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
    have hroot : Real.sqrt ((msc (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ)).im /
        ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - ε))) ≤
        2 * Cm * (N : ℝ) ^ (-(1 : ℝ) / 3 + ε) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [div_eq_mul_one_div, hNη]
      calc (msc (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ)).im *
            (N : ℝ) ^ (-(1 : ℝ) / 3 + ε)
          ≤ Cm * (2 * (N : ℝ) ^ (-(1 : ℝ) / 3 + ε)) * (N : ℝ) ^ (-(1 : ℝ) / 3 + ε) :=
            mul_le_mul_of_nonneg_right hIm hA0.le
        _ ≤ (2 * Cm * (N : ℝ) ^ (-(1 : ℝ) / 3 + ε)) ^ 2 := by
            have : 0 ≤ ((N : ℝ) ^ (-(1 : ℝ) / 3 + ε)) ^ 2 := sq_nonneg _
            nlinarith
    have hparen : 1 / (N : ℝ) ^ φp +
        Real.sqrt ((msc (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ)).im /
          ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - ε))) +
        1 / ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ≤
        (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-(1 : ℝ) / 3 + ε) := by
      rw [hNη]
      nlinarith
    have hpos : 0 ≤ 1 / (N : ℝ) ^ φp +
        Real.sqrt ((msc (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ)).im /
          ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - ε))) +
        1 / ((N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) := by positivity
    calc entryErr N C ((N : ℝ) ^ φp) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩
        ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-(1 : ℝ) / 3 + ε)) :=
          mul_le_mul hC hparen hpos (Real.rpow_nonneg hn0.le _)
      _ = (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
          congr 1
          ring

/-! ### The support parameter of the interpolated laws -/

/-- The GOE entry laws have the support parameter `N^φp` (`φp < 1/2`) with one constant `c > 0`,
for every lower bound `Q ≤ N^φp` and all large `N`. -/
private lemma apriori_goe_support {φp : ℝ} (h0 : 0 < φp) (h1 : φp < 1 / 2) :
    ∃ c > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ Q : ℝ,
      Q ≤ (N : ℝ) ^ φp → (goeLaws N).SupportParam Q c ((N : ℝ) ^ φp) := by
  obtain ⟨cb, hcb, Nb, hb⟩ := goeLaws_boundedSupport h0 h1
  obtain ⟨ct, hct, Nt, ht⟩ := gaussianReal_tailVar h0 h1
  refine ⟨min cb ct, lt_min hcb hct, max Nb (max Nt 1), fun N hN Q hQ => ⟨hQ, ?_, ?_⟩⟩
  · have hNb : Nb ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hmono : Real.exp (-(N : ℝ) ^ cb) ≤ Real.exp (-(N : ℝ) ^ (min cb ct)) :=
      Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)))
    exact ⟨fun i => ((hb N hNb).1 i).trans (ENNReal.ofReal_le_ofReal hmono),
      fun p => ((hb N hNb).2 p).trans (ENNReal.ofReal_le_ofReal hmono)⟩
  · intro p
    have hNt : Nt ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hmono : Real.exp (-(N : ℝ) ^ ct) ≤ Real.exp (-(N : ℝ) ^ (min cb ct)) :=
      Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)))
    rw [goeLaws_off]
    refine (ht N hNt _ ?_).trans hmono
    have hNpos : (0 : ℝ) < N := by linarith
    push_cast
    rw [mul_one, div_eq_mul_inv]
    have : 0 ≤ (N : ℝ)⁻¹ := by positivity
    linarith

/-- A law of `LargeQClass C0 φs` has the support parameter `N^φp` for `φp ≤ φs`. -/
private lemma apriori_class_support {C0 φs φp : ℝ} {N : ℕ} {Lv : EntryLaws N} (hN : 1 ≤ N)
    (hφ : φp ≤ φs) (hv : LargeQClass C0 φs N Lv) (Q c : ℝ) (hQ : Q ≤ (N : ℝ) ^ φp) :
    Lv.SupportParam Q c ((N : ℝ) ^ φp) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hle : ((N : ℝ) ^ φs)⁻¹ ≤ ((N : ℝ) ^ φp)⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hN1 hφ)
  have hbs : Lv.BoundedSupportAS ((N : ℝ) ^ φp) :=
    ⟨fun i => measure_mono_null (fun x hx => lt_of_le_of_lt hle hx) (hv.2.1 i),
      fun p => measure_mono_null (fun x hx => lt_of_le_of_lt hle hx) (hv.2.2 p)⟩
  exact ⟨hQ, hbs.boundedSupport c, hbs.tailVarOff c⟩

/-! ### (3.26) for every `H_γ` -/

/-- (3.26) for every `H_γ` between a law of Lemma 3.5 and the GOE, simultaneously for
all `γ ≤ N(N+1)/2`, `E ∈ I_ε` and entries: `|G_kl - δ_kl m_sc| ≤ N^{-1/3+2ε}`. -/
theorem apriori_largeQInterp {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → HighProbOn 1
      (fun N L => ∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N))
      (fun N _ => {ω | ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
        ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
            (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
          (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)}) := by
  intro ε hε hε'
  have _ := hC0
  have hφp1 : 1 / 3 < (1 / 3 + φs) / 2 := by linarith
  have hφp2 : (1 / 3 + φs) / 2 < φs := by linarith
  have hφp3 : (1 / 3 + φs) / 2 < 1 / 2 := by linarith
  obtain ⟨c, hc, Ng, hg⟩ := apriori_goe_support (φp := (1 / 3 + φs) / 2) (by linarith) hφp3
  obtain ⟨Cl, hCl, hll⟩ := localLaw (ζ := 1) (C0 := max C0 1) (c := c) one_pos
    (le_max_of_le_right zero_le_one) hc
  obtain ⟨Cm, hCm, him⟩ := apriori_im_msc
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 <|
    (eventually_ge_atTop 2).and <|
    (phi_rpow_le_rpow Cl (half_pos hε)).and <|
    (phi_rpow_le_rpow Cl (by linarith : (0 : ℝ) < (1 / 3 + φs) / 2)).and <|
    ((tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (2 + 2 * Cm)
  refine HighProbOn.mono_eventually hll (fun N L hL => ?_)
    ⟨max N1 Ng, fun N hN L hL ω hω => ?_⟩
  · obtain ⟨Lv, γ, hv, rfl⟩ := hL
    exact interp_isGenWigner hv.1 (goeLaws_isGenWigner N)
  · obtain ⟨Lv, γ, hv, rfl⟩ := hL
    obtain ⟨hN2, hC1, hC2, hK⟩ := hN1 N (le_trans (le_max_left _ _) hN)
    replace hK : 2 + 2 * Cm ≤ (N : ℝ) ^ (ε / 2) := hK
    have hNg : Ng ≤ N := le_trans (le_max_right _ _) hN
    have hSP := interp_supportParam (Φ := lexPos N) (γ := γ)
      (apriori_class_support (by omega) hφp2.le hv _ c hC2)
      (hg N hNg _ hC2)
    intro E hE k l
    obtain ⟨hz, herr⟩ := apriori_domain_err (φp := (1 / 3 + φs) / 2) hN2 hε hε' hφp1.le hCm
      him hC1 hK hE
    exact ((hω _ hSP _ hz).2 k l).trans herr

/-- The event of (3.26) at `η = N^{-2/3-ε}`: `|G_kl(E + iη) - δ_kl m_sc(E + iη)| ≤ N^{-1/3+2ε}` for
all `E ∈ I_ε` and all `k, l` ([16] (6.55)). -/
def aprioriEvent (N : ℕ) (ε : ℝ) : Set (Entries N) :=
  {ω | ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
    ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
        (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
      (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)}

/-- (3.26) in terms of `aprioriEvent`. -/
theorem apriori_largeQInterp_event {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → HighProbOn 1
      (fun N L => ∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N))
      (fun N _ => aprioriEvent N ε) :=
  apriori_largeQInterp hC0 hφs hφs'

/-- (3.26) uniformly in `y` between `E₁, E₂ ∈ I_ε`, the form used for (3.19) ([16] (6.55) with
`y ∈ [E₁, E₂]`). -/
theorem apriori_largeQInterp_uIcc {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → HighProbOn 1
      (fun N L => ∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N))
      (fun N _ => {ω | ∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ y ∈ Set.uIcc E₁ E₂, ∀ k l,
          ‖resolventC (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
              (if k = l then msc ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
            (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)}) := by
  intro ε hε hε'
  refine HighProbOn.mono (apriori_largeQInterp hC0 hφs hφs' ε hε hε') fun N _ ω hω => ?_
  intro E₁ E₂ h1 h2 y hy k l
  refine hω y ?_ k l
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  rcases Set.mem_uIcc.1 hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ### Deterministic consequences of (3.26) -/

/-- On `aprioriEvent N ε` the off-diagonal double sum at a point of `I_ε` is at most
`N² (N^{-1/3+2ε})²`. -/
private lemma apriori_offSum_le {N : ℕ} {ε : ℝ} {ω : Entries N} (hω : ω ∈ aprioriEvent N ε)
    {E : ℝ} (hE : |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) :
    ∑ i, ∑ j, (if i = j then 0 else
        ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) ≤
      (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2 := by
  have hterm : ∀ i j : Fin N, (if i = j then 0 else
      ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) ≤
        ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]; positivity
    · simp only [hij, ↓reduceIte]
      have h := hω E hE i j
      simp only [hij, ↓reduceIte, sub_zero] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
  calc ∑ i, ∑ j, (if i = j then 0 else
        ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2)
      ≤ ∑ _i : Fin N, ∑ _j : Fin N, ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Deterministic consequences of (3.26) on `aprioriEvent N ε`, used for (3.19), (3.34) and [16]
(6.61): `|G_kk| ≤ 2`; `0 ≤ y_S ≤ N^{2ε}` ((3.33)); `|x_S| ≤ 2N^{4ε}` ([16] (6.56)). -/
theorem aprioriEvent_bounds {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10)
    {ω : Entries N} (hω : ω ∈ aprioriEvent N ε) :
    (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k,
      ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k k‖ ≤ 2) ∧
    (∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      0 ≤ offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ ∧
      offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ ≤ (N : ℝ) ^ (2 * ε)) ∧
    (∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
      |offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) E₁ E₂| ≤
        2 * (N : ℝ) ^ (4 * ε)) := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hη0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  refine ⟨fun E hE k => ?_, fun E hE => ?_, fun E₁ E₂ h1 h2 => ?_⟩
  · have h := hω E hE k k
    simp only [↓reduceIte] at h
    have hm := (norm_msc_eq_inv_and_lt_one
      (z := ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) hη0).2
    calc ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k k‖
        ≤ ‖msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩‖ +
          ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k k -
            msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩‖ := by
          have := norm_add_le (msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
            (resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k k -
              msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩)
          rwa [add_sub_cancel] at this
      _ ≤ 2 := by linarith
  · refine ⟨mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg
      fun j _ => ?_), ?_⟩
    · split_ifs <;> positivity
    · calc offWard (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩
          ≤ ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε)) ^ 2 *
              ((N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2) :=
            mul_le_mul_of_nonneg_left (apriori_offSum_le hω hE) (sq_nonneg _)
        _ = (N : ℝ) ^ (2 * ε) := by
            rw [apriori_sq_rpow hn0.le, apriori_sq_rpow hn0.le,
              show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) from (Real.rpow_two _).symm,
              ← Real.rpow_add hn0, ← Real.rpow_add hn0]
            congr 1
            ring
  · have hint : ‖∫ y in E₁..E₂, ∑ i, ∑ j, (if i = j then 0 else
        ‖resolventC (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2)‖ ≤
        ((N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2) * |E₂ - E₁| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      have hy' := Set.uIoc_subset_uIcc hy
      have a1 := abs_le.1 h1
      have a2 := abs_le.1 h2
      have hyI : |y - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
        rcases Set.mem_uIcc.1 hy' with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
          exact abs_le.2 ⟨by linarith, by linarith⟩
      have hnn : 0 ≤ ∑ i, ∑ j, (if i = j then 0 else
          ‖resolventC (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact apriori_offSum_le hω hyI
    have hlen : |E₂ - E₁| ≤ 2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) := by
      have a1 := abs_le.1 h1
      have a2 := abs_le.1 h2
      exact abs_le.2 ⟨by linarith, by linarith⟩
    unfold offWardInt
    rw [abs_mul, abs_of_pos hη0, ← Real.norm_eq_abs]
    have hB : 0 ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2 := by positivity
    calc (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) * ‖∫ y in E₁..E₂, ∑ i, ∑ j, (if i = j then 0 else
          ‖resolventC (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ^ 2)‖
        ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) *
            (((N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2) *
              (2 * (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))) :=
          mul_le_mul_of_nonneg_left (hint.trans (mul_le_mul_of_nonneg_left hlen hB)) hη0.le
      _ = 2 * (N : ℝ) ^ (4 * ε) := by
          have e : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) *
              (((N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2) *
                (N : ℝ) ^ (-(2 : ℝ) / 3 + ε)) = (N : ℝ) ^ (4 * ε) := by
            rw [apriori_sq_rpow hn0.le,
              show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) from (Real.rpow_two _).symm,
              ← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
            congr 1
            ring
          calc _ = 2 * ((N : ℝ) ^ (-(2 : ℝ) / 3 - ε) *
              (((N : ℝ) ^ 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε)) ^ 2) *
                (N : ℝ) ^ (-(2 : ℝ) / 3 + ε))) := by ring
            _ = _ := by rw [e]

/-! ### Checks -/

/-- For the GOE (`γ = 0` and the Rademacher laws as `Lv`) at `(C0, φs) = (1, 2/5)`, the event
`aprioriEvent N ε` is nonempty for all large `N`: its complement has probability at most
`ε_N → 0`, while the whole space has probability `1`. -/
private lemma apriori_nonempty {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) :
    ∀ᶠ N : ℕ in atTop, (aprioriEvent N ε).Nonempty := by
  obtain ⟨e, he, hev⟩ := (apriori_largeQInterp_event (C0 := 1) (φs := 2 / 5) zero_le_one
    (by norm_num) (by norm_num) ε hε hε').tendstoOneOn one_pos
  filter_upwards [hev, he.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 32] with
    N hN heN h32
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have := EntryLaws.isProbabilityMeasure_law (goeLaws_isGenWigner N).isProb
  have h1 := hN (goeLaws N) ⟨radLaws N, 0, ⟨radLaws_isGenWigner (by omega),
    radLaws_boundedSupportAS h32⟩, (interp_lexPos_zero _ _).symm⟩
  rw [hne, Set.compl_empty, measure_univ] at h1
  exact absurd (h1.trans_lt (ENNReal.ofReal_lt_one.mpr heN)) (lt_irrefl _)

/-- The hypotheses of `aprioriEvent_bounds` hold together at `ε = 1/20`: for all large `N` there is
an `ω` in `aprioriEvent N (1/20)` (from the GOE, `γ = 0`, and the Rademacher laws), and the three
bounds hold for it at the centre `E = 2` of `I_ε` and on the window `[2 - N^{-2/3+1/20},
2 + N^{-2/3+1/20}]`, whose endpoints differ. -/
example : ∀ᶠ N : ℕ in atTop, ∃ ω : Entries N, ω ∈ aprioriEvent N (1 / 20) ∧
    (∀ k, ‖resolventC (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ k k‖ ≤ 2) ∧
    (0 ≤ offWard (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ ∧
      offWard (symOfEntries ω) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ ≤
        (N : ℝ) ^ (2 * (1 / 20 : ℝ))) ∧
    |offWardInt (symOfEntries ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20))
        (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20)) (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20))| ≤
      2 * (N : ℝ) ^ (4 * (1 / 20 : ℝ)) := by
  filter_upwards [apriori_nonempty (ε := 1 / 20) (by norm_num) (by norm_num),
    eventually_ge_atTop 1] with N ⟨ω, hω⟩ hN
  obtain ⟨b1, b2, b3⟩ := aprioriEvent_bounds hN (ε := 1 / 20) (by norm_num) (by norm_num) hω
  have hr : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := by positivity
  have h0 : |(2 : ℝ) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := by
    rw [sub_self, abs_zero]; exact hr
  refine ⟨ω, hω, b1 2 h0, b2 2 h0, b3 _ _ ?_ ?_⟩
  · exact abs_le.2 ⟨by linarith, by linarith⟩
  · exact abs_le.2 ⟨by linarith, by linarith⟩

#print axioms ward_sub_offWard
#print axioms apriori_largeQInterp
#print axioms apriori_largeQInterp_event
#print axioms apriori_largeQInterp_uIcc
#print axioms aprioriEvent_bounds

end WEdgeNS
