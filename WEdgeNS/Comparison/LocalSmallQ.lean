import WEdgeNS.Comparison.MomentCompare
import WEdgeNS.Model.HighProbCalc

/-!
# The averaged local law for small support
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private swap_measurable_resS from WEdgeNS.Comparison.Swap
open private rpow_quarter_le_tilde tilde_pos from WEdgeNS.Comparison.Classes
open private weak_norm_msc_sub_le weak_norm_stieltjesM_sub_le from WEdgeNS.LocalLaw.Weak
open private expansion_matchedPair_radLaws from WEdgeNS.Comparison.Expansion
open private sc_one_le_phi from WEdgeNS.LocalLaw.SelfConsistent
open private lawV lawW lawV_momentCond lawV_supp lawVW_isMomentMatch
  from WEdgeNS.Comparison.Classes

/-! ### Elementary bounds -/

private lemma lsq_natCast_pos {N : ℕ} (hN : 3 ≤ N) : (0 : ℝ) < N :=
  Nat.cast_pos.2 (by omega)

/-- `S(C') ⊆ S(C)` for `C ≤ C'` once `φ ≥ 1`. -/
private lemma lsq_specDomain_mono {N : ℕ} {C C' : ℝ} (hN : 3 ≤ N) (h : C ≤ C') :
    specDomain N C' ⊆ specDomain N C := by
  intro z hz
  refine ⟨hz.1, lt_of_le_of_lt ?_ hz.2.1, hz.2.2⟩
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (sc_one_le_phi hN) h) (lsq_natCast_pos hN).le

/-- On `S(C)` with `C ≥ 0`: `N Im z > 1`. -/
private lemma lsq_one_lt_mul_im {N : ℕ} {C : ℝ} (hN : 3 ≤ N) (hC : 0 ≤ C) {z : ℂ}
    (hz : z ∈ specDomain N C) : 1 < N * z.im := by
  have hNr := lsq_natCast_pos hN
  have h1 : 1 ≤ phi N ^ C := Real.one_le_rpow (sc_one_le_phi hN) hC
  have := hz.2.1
  rw [div_lt_iff₀ hNr] at this
  linarith

/-- `‖m(z)‖ ≤ 1 / Im z`. -/
private lemma lsq_norm_stieltjesM_le {N : ℕ} (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) : ‖stieltjesM H z‖ ≤ 1 / z.im := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have e : stieltjesM H z = (N : ℂ)⁻¹ * ∑ i, resolventC H z i i := by
    unfold stieltjesM
    rw [Matrix.trace]
    simp only [Matrix.diag]
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ i, resolventC H z i i‖ ≤ (N : ℝ)⁻¹ * (N * (1 / z.im)) := by
        gcongr
        refine (norm_sum_le _ _).trans ?_
        calc ∑ i, ‖resolventC H z i i‖ ≤ ∑ _i : Fin N, 1 / z.im :=
              Finset.sum_le_sum fun i _ => norm_resolventC_apply_le hH hz i i
          _ = N * (1 / z.im) := by simp
    _ = 1 / z.im := by field_simp

/-- `m(z)` is measurable in the entries. -/
private lemma lsq_measurable_stieltjesM {N : ℕ} (z : ℂ) :
    Measurable (fun ω : Entries N => stieltjesM (symOfEntries ω) z) := by
  have e : (fun ω : Entries N => stieltjesM (symOfEntries ω) z) =
      fun ω => (N : ℂ)⁻¹ * ∑ i, resS z ω i i := by
    funext ω
    unfold stieltjesM resS
    rw [Matrix.trace]
    simp only [Matrix.diag]
  rw [e]
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  exact (swap_measurable_resS z).eval_matrix (i := i) (j := i)

/-- `|m - m_sc| ≤ N + 1` on `S(C)`, `C ≥ 0`. -/
private lemma lsq_norm_sub_le {N : ℕ} {C : ℝ} (hN : 3 ≤ N) (hC : 0 ≤ C) {z : ℂ}
    (hz : z ∈ specDomain N C) (ω : Entries N) :
    ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ N + 1 := by
  have h1 := lsq_one_lt_mul_im hN hC hz
  have hNr := lsq_natCast_pos hN
  have hzim : 0 < z.im := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have h2 := lsq_norm_stieltjesM_le (by omega) (symOfEntries_isHermitian ω) hzim
  have h3 := (norm_msc_eq_inv_and_lt_one hzim).2
  have h4 : 1 / z.im < N := by
    rw [div_lt_iff₀ hzim]; linarith
  exact (norm_sub_le _ _).trans (by linarith)

/-! ### The errors (3.2)-(3.3) at the support of the match -/

private lemma lsq_sq_add3 (x y w : ℝ) : (x + y + w) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + w ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - w), sq_nonneg (y - w)]

/-- At `q = √N / (K log N)` the errors (3.2)-(3.3) on `S(C)` are at most
`φ^{2 C_l + 3} / (N Im z)` (the entry error squared), once `φ ≥ 3 (10 K² + 2)`. -/
private lemma lsq_err_bound {N : ℕ} {Cl C K : ℝ} (hN : 16 ≤ N) (hCl : 0 ≤ Cl) (hC : 0 ≤ C)
    (hK : 0 < K) (hϕ : 3 * (10 * K ^ 2 + 2) ≤ phi N) {z : ℂ} (hz : z ∈ specDomain N C) :
    0 ≤ entryErr N Cl (Real.sqrt N / (K * Real.log N)) z ∧
    0 ≤ avgErr N Cl (Real.sqrt N / (K * Real.log N)) z ∧
    entryErr N Cl (Real.sqrt N / (K * Real.log N)) z ^ 2 ≤
      phi N ^ (2 * Cl + 3) / (N * z.im) ∧
    avgErr N Cl (Real.sqrt N / (K * Real.log N)) z ≤ phi N ^ (2 * Cl + 3) / (N * z.im) := by
  have hN3 : 3 ≤ N := by omega
  have hNr := lsq_natCast_pos hN3
  have ht1 := lsq_one_lt_mul_im hN3 hC hz
  have hη : 0 < z.im := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hη10 : z.im ≤ 10 := hz.2.2
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLϕ : Real.log N ≤ phi N := log_le_phi hN
  have hϕ1 := sc_one_le_phi hN3
  have hϕ0 : 0 < phi N := by linarith
  have hmsc1 : (msc z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_msc_eq_inv_and_lt_one hη).2.le
  have hmsc0 : 0 ≤ (msc z).im := (im_msc_pos hη).le
  set t : ℝ := (N : ℝ) * z.im with ht
  have ht0 : 0 < t := by linarith
  set ϕ : ℝ := phi N with hϕdef
  set a : ℝ := K * Real.log N with ha
  have ha0 : 0 < a := mul_pos hK hL
  have haϕ : a ^ 2 ≤ K ^ 2 * ϕ ^ 2 := by
    rw [ha, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hLϕ 2) (sq_nonneg K)
  set q : ℝ := Real.sqrt N / a with hq
  have hq0 : 0 < q := div_pos (Real.sqrt_pos.2 hNr) ha0
  have hq2 : q ^ 2 = N / a ^ 2 := by rw [hq, div_pow, Real.sq_sqrt hNr.le]
  have hu2 : 1 / q ^ 2 = a ^ 2 / N := by rw [hq2]; field_simp
  have hu2' : 1 / q ^ 2 ≤ 10 * a ^ 2 / t := by
    rw [hu2, div_le_div_iff₀ hNr ht0, ht]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg a) hNr.le) (sub_nonneg.2 hη10)]
  -- the sharp `q`-term of (3.2)
  have hmin : min (1 / (q ^ 2 * Real.sqrt (kappa z.re + z.im))) (1 / q) ≤ 4 * a ^ 2 / t := by
    refine (min_le_left _ _).trans ?_
    have hs0 : 0 < Real.sqrt z.im := Real.sqrt_pos.2 hη
    have hκ : 0 ≤ kappa z.re := abs_nonneg _
    have hsκ : Real.sqrt z.im ≤ Real.sqrt (kappa z.re + z.im) :=
      Real.sqrt_le_sqrt (by linarith)
    have hs4 : Real.sqrt z.im ≤ 4 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    have hss : Real.sqrt z.im ^ 2 = z.im := Real.sq_sqrt hη.le
    have hqs : 0 < q ^ 2 * Real.sqrt z.im := by positivity
    refine (one_div_le_one_div_of_le hqs (mul_le_mul_of_nonneg_left hsκ (sq_nonneg q))).trans ?_
    rw [div_le_div_iff₀ hqs ht0, one_mul, hq2, ht]
    have h1 : 4 * a ^ 2 * (N / a ^ 2 * Real.sqrt z.im) = 4 * N * Real.sqrt z.im := by
      field_simp
    have h2 : (N : ℝ) * z.im = N * Real.sqrt z.im ^ 2 := by rw [hss]
    rw [h1, h2]
    nlinarith [mul_nonneg (mul_nonneg hNr.le hs0.le) (sub_nonneg.2 hs4)]
  have hΛ : ϕ ^ (2 * Cl) * (3 * (10 * a ^ 2 + 2)) / t ≤ ϕ ^ (2 * Cl + 3) / t := by
    refine div_le_div_of_nonneg_right ?_ ht0.le
    have h3 : ϕ ^ (2 * Cl + 3) = ϕ ^ (2 * Cl) * ϕ ^ 3 := by
      rw [Real.rpow_add hϕ0]; norm_cast
    rw [h3]
    have hp0 : 0 ≤ ϕ ^ (2 * Cl) := Real.rpow_nonneg hϕ0.le _
    refine mul_le_mul_of_nonneg_left ?_ hp0
    have : 3 * (10 * a ^ 2 + 2) ≤ 3 * (10 * K ^ 2 + 2) * ϕ ^ 2 := by
      nlinarith [sq_nonneg K, sq_nonneg ϕ, mul_nonneg (sq_nonneg K) (sq_nonneg ϕ)]
    calc 3 * (10 * a ^ 2 + 2) ≤ 3 * (10 * K ^ 2 + 2) * ϕ ^ 2 := this
      _ ≤ ϕ * ϕ ^ 2 := mul_le_mul_of_nonneg_right hϕ (sq_nonneg ϕ)
      _ = ϕ ^ 3 := by ring
  have hCl1 : ϕ ^ Cl ≤ ϕ ^ (2 * Cl) := Real.rpow_le_rpow_of_exponent_le hϕ1 (by linarith)
  have hp0 : 0 ≤ ϕ ^ (2 * Cl) := Real.rpow_nonneg hϕ0.le _
  have hp2 : ϕ ^ (2 * Cl) = ϕ ^ Cl * ϕ ^ Cl := by
    rw [two_mul, Real.rpow_add hϕ0]
  have hpCl0 : 0 ≤ ϕ ^ Cl := Real.rpow_nonneg hϕ0.le _
  have hXnn : 0 ≤ entryErr N Cl q z := by
    unfold entryErr
    exact mul_nonneg hpCl0 (by positivity)
  have hYnn : 0 ≤ avgErr N Cl q z := by
    unfold avgErr
    refine mul_nonneg hpCl0 (add_nonneg (le_min (by positivity) (by positivity)) (by positivity))
  refine ⟨hXnn, hYnn, ?_, ?_⟩
  · -- the entry error
    unfold entryErr
    set β : ℝ := 1 / q with hβ
    set γ : ℝ := Real.sqrt ((msc z).im / t) with hγ
    set δ' : ℝ := 1 / t with hδ'
    have hβ2 : β ^ 2 ≤ 10 * a ^ 2 / t := by rw [hβ, div_pow, one_pow]; exact hu2'
    have hγ2 : γ ^ 2 ≤ 1 / t := by
      rw [hγ, Real.sq_sqrt (by positivity)]
      exact div_le_div_of_nonneg_right hmsc1 ht0.le
    have hδ2 : δ' ^ 2 ≤ 1 / t := by
      rw [hδ', div_pow, one_pow]
      exact one_div_le_one_div_of_le ht0 (le_self_pow₀ ht1.le two_ne_zero)
    have hβ0 : 0 ≤ β := by positivity
    have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
    have hδ0 : 0 ≤ δ' := by positivity
    have h3 : (β + γ + δ') ^ 2 ≤ 3 * (β ^ 2 + γ ^ 2 + δ' ^ 2) := lsq_sq_add3 β γ δ'
    calc (ϕ ^ Cl * (β + γ + δ')) ^ 2 = ϕ ^ (2 * Cl) * (β + γ + δ') ^ 2 := by
          rw [mul_pow, hp2]; ring
      _ ≤ ϕ ^ (2 * Cl) * (3 * (10 * a ^ 2 / t + 1 / t + 1 / t)) := by
          refine mul_le_mul_of_nonneg_left (h3.trans ?_) hp0
          linarith
      _ = ϕ ^ (2 * Cl) * (3 * (10 * a ^ 2 + 2)) / t := by ring
      _ ≤ _ := hΛ
  · -- the averaged error
    unfold avgErr
    calc ϕ ^ Cl * (min (1 / (q ^ 2 * Real.sqrt (kappa z.re + z.im))) (1 / q) + 1 / t)
        ≤ ϕ ^ (2 * Cl) * (4 * a ^ 2 / t + 1 / t) := by
          refine mul_le_mul hCl1 (add_le_add hmin le_rfl) (by positivity) hp0
      _ ≤ ϕ ^ (2 * Cl) * ((3 * (10 * a ^ 2 + 2)) / t) := by
          refine mul_le_mul_of_nonneg_left ?_ hp0
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg a]) ht0.le
      _ = ϕ ^ (2 * Cl) * (3 * (10 * a ^ 2 + 2)) / t := by ring
      _ ≤ _ := hΛ

/-! ### Markov's inequality for a moment comparison -/

/-- Markov's inequality at level `2T` for `f ≥ 0` bounded by `B`, when the `p`-th moment of `f`
under `μ` exceeds that under `ν` by at most `R`, and `f ≤ Y` outside a `ν`-set of mass `δ`. -/
private lemma lsq_markov {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ ω, f ω ≤ B) {p : ℕ} {Y T R δ : ℝ}
    (hY : 0 ≤ Y) (hT : 0 < T) (hδ : 0 ≤ δ)
    (hmom : ∫ ω, f ω ^ p ∂μ ≤ ∫ ω, f ω ^ p ∂ν + R)
    (hbad : ν {ω | Y < f ω} ≤ ENNReal.ofReal δ) :
    μ {ω | 2 * T ≤ f ω} ≤ ENNReal.ofReal ((Y ^ p + B ^ p * δ + R) / (2 * T) ^ p) := by
  have hint : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → Integrable (fun ω => f ω ^ p) ρ := by
    intro ρ _
    refine Integrable.of_bound ((hf.pow_const p).aestronglyMeasurable) (B ^ p)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf0 ω) p)]
    exact pow_le_pow_left₀ (hf0 ω) (hB ω) p
  have hS : MeasurableSet {ω | Y < f ω} := measurableSet_lt measurable_const hf
  -- the `p`-th moment under `ν`
  have hν : ∫ ω, f ω ^ p ∂ν ≤ Y ^ p + B ^ p * δ := by
    have hpt : ∀ ω, f ω ^ p ≤ Y ^ p + {ω | Y < f ω}.indicator (fun _ => B ^ p) ω := by
      intro ω
      by_cases h : Y < f ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | Y < f ω} from h)]
        have := pow_le_pow_left₀ (hf0 ω) (hB ω) p
        have : 0 ≤ Y ^ p := pow_nonneg hY p
        linarith
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | Y < f ω} from h)]
        simpa using pow_le_pow_left₀ (hf0 ω) (not_lt.1 h) p
    have hi : Integrable ({ω | Y < f ω}.indicator (fun _ => B ^ p)) ν :=
      (integrable_const (B ^ p)).indicator hS
    calc ∫ ω, f ω ^ p ∂ν
        ≤ ∫ ω, (Y ^ p + {ω | Y < f ω}.indicator (fun _ => B ^ p) ω) ∂ν :=
          integral_mono (hint ν inferInstance) ((integrable_const _).add hi) hpt
      _ = Y ^ p + ν.real {ω | Y < f ω} * B ^ p := by
          rw [integral_add (integrable_const _) hi, integral_const, integral_indicator_const _ hS]
          simp
      _ ≤ Y ^ p + B ^ p * δ := by
          have h1 : ν.real {ω | Y < f ω} ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ hbad
          have h2 : 0 ≤ B ^ p := pow_nonneg hB0 p
          nlinarith
  -- Markov
  have h2T : 0 ≤ 2 * T := by positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun ω => f ω ^ p)
    (Eventually.of_forall fun ω => pow_nonneg (hf0 ω) p) (hint μ inferInstance) ((2 * T) ^ p)
  have hsub : {ω | 2 * T ≤ f ω} ⊆ {ω | (2 * T) ^ p ≤ f ω ^ p} :=
    fun ω hω => pow_le_pow_left₀ h2T hω p
  have hμ : μ.real {ω | 2 * T ≤ f ω} ≤ (Y ^ p + B ^ p * δ + R) / (2 * T) ^ p := by
    rw [le_div_iff₀ (by positivity)]
    have h3 : μ.real {ω | 2 * T ≤ f ω} ≤ μ.real {ω | (2 * T) ^ p ≤ f ω ^ p} :=
      measureReal_mono hsub
    have h4 : 0 ≤ (2 * T) ^ p := by positivity
    calc μ.real {ω | 2 * T ≤ f ω} * (2 * T) ^ p
        ≤ μ.real {ω | (2 * T) ^ p ≤ f ω ^ p} * (2 * T) ^ p :=
          mul_le_mul_of_nonneg_right h3 h4
      _ = (2 * T) ^ p * μ.real {ω | (2 * T) ^ p ≤ f ω ^ p} := mul_comm _ _
      _ ≤ _ := hmk
      _ ≤ _ := by linarith
  calc μ {ω | 2 * T ≤ f ω} = ENNReal.ofReal (μ.real {ω | 2 * T ≤ f ω}) :=
        (ofReal_measureReal).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hμ

/-! ### The final arithmetic of the Markov bound -/

/-- `(N+1)^p · N^{C'} e^{-c φ³} ≤ (10 N)^{-p}` for `p ≤ φ`, `log N ≤ φ` and `φ` large. -/
private lemma lsq_tiny {N : ℕ} {ϕ cl Cl' : ℝ} {p : ℕ} (hN : 12 ≤ N) (hlog : Real.log N ≤ ϕ)
    (hϕ1 : 1 ≤ ϕ) (hp : (p : ℝ) ≤ ϕ) (hcl : 0 < cl) (hCl' : 0 ≤ Cl') (hϕc : (3 + Cl') / cl ≤ ϕ) :
    ((N : ℝ) + 1) ^ p * ((N : ℝ) ^ Cl' * Real.exp (-cl * ϕ ^ (3 : ℝ))) ≤
      (1 / (10 * (N : ℝ))) ^ p := by
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have h1 : ((N : ℝ) + 1) * (10 * N) ≤ (N : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hNr (sq_nonneg (N : ℝ))]
  have hcube : (N : ℝ) ^ 3 = Real.exp (3 * Real.log N) := by
    rw [show (3 : ℝ) * Real.log N = ((3 : ℕ) : ℝ) * Real.log N by norm_num, Real.exp_nat_mul,
      Real.exp_log hN0]
  have hpow3 : ϕ ^ (3 : ℝ) = ϕ ^ 3 := by
    rw [← Real.rpow_natCast]; norm_num
  have hrp : (N : ℝ) ^ Cl' = Real.exp (Cl' * Real.log N) := by
    rw [Real.rpow_def_of_pos hN0, mul_comm]
  have hcϕ : 3 + Cl' ≤ cl * ϕ := by
    rw [div_le_iff₀ hcl] at hϕc; linarith
  have hexp : 3 * (p * Real.log N) + Cl' * Real.log N + -cl * ϕ ^ 3 ≤ 0 := by
    have e1 : (p : ℝ) * Real.log N ≤ ϕ * ϕ := mul_le_mul hp hlog hlogN (by linarith)
    have e2 : Cl' * Real.log N ≤ Cl' * ϕ := mul_le_mul_of_nonneg_left hlog hCl'
    have e3 : (3 + Cl') * ϕ ^ 2 ≤ cl * ϕ * ϕ ^ 2 :=
      mul_le_mul_of_nonneg_right hcϕ (sq_nonneg ϕ)
    have e4 : Cl' * ϕ ≤ Cl' * ϕ ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hCl'
    nlinarith
  have key : ((N : ℝ) + 1) ^ p * ((N : ℝ) ^ Cl' * Real.exp (-cl * ϕ ^ (3 : ℝ))) *
      (10 * (N : ℝ)) ^ p ≤ 1 := by
    have e : ((N : ℝ) + 1) ^ p * ((N : ℝ) ^ Cl' * Real.exp (-cl * ϕ ^ (3 : ℝ))) *
        (10 * (N : ℝ)) ^ p = (((N : ℝ) + 1) * (10 * N)) ^ p *
          ((N : ℝ) ^ Cl' * Real.exp (-cl * ϕ ^ (3 : ℝ))) := by
      rw [mul_pow (((N : ℝ) + 1)) (10 * (N : ℝ)) p]; ring
    rw [e]
    calc (((N : ℝ) + 1) * (10 * N)) ^ p * ((N : ℝ) ^ Cl' * Real.exp (-cl * ϕ ^ (3 : ℝ)))
        ≤ ((N : ℝ) ^ 3) ^ p * ((N : ℝ) ^ Cl' * Real.exp (-cl * ϕ ^ (3 : ℝ))) := by
          gcongr
      _ = Real.exp (3 * (p * Real.log N) + Cl' * Real.log N + -cl * ϕ ^ 3) := by
          rw [hcube, ← Real.exp_nat_mul, hrp, hpow3, ← Real.exp_add, ← Real.exp_add]
          congr 1; ring
      _ ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 hexp
  rw [_root_.one_div_pow, le_div_iff₀ (by positivity)]
  exact key

/-- The final bound of the Markov step: `3 · 2^{-p} ≤ N e^{-(log 2) φ}` for `p ≥ φ - 2` and
`N ≥ 12`. -/
private lemma lsq_final_arith {N : ℕ} {ϕ Y T R D : ℝ} {p : ℕ} (hN : 12 ≤ N) (hT : 0 < T)
    (hp : ϕ - 2 ≤ p) (h1 : Y ^ p ≤ T ^ p) (h2 : R ≤ T ^ p) (h3 : D ≤ T ^ p) :
    (Y ^ p + D + R) / (2 * T) ^ p ≤
      (N : ℝ) ^ 1 * Real.exp (-Real.log 2 * ϕ ^ (1 : ℝ)) := by
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN
  have hTp : 0 < T ^ p := pow_pos hT p
  have h2p : (2 : ℝ) ^ p = Real.exp (p * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have h4 : Real.exp (2 * Real.log 2) = 4 := by
    rw [show (2 : ℝ) * Real.log 2 = ((2 : ℕ) : ℝ) * Real.log 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log two_pos]; norm_num
  have hE : Real.exp (-Real.log 2 * ϕ) * (2 : ℝ) ^ p ≥ 1 / 4 := by
    rw [h2p, ← Real.exp_add]
    have : Real.exp (-(2 * Real.log 2)) ≤ Real.exp (-Real.log 2 * ϕ + p * Real.log 2) := by
      apply Real.exp_le_exp.2
      have := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
      nlinarith
    rw [Real.exp_neg, h4] at this
    linarith
  rw [Real.rpow_one, pow_one, div_le_iff₀ (by positivity), mul_pow]
  have h5 : Y ^ p + D + R ≤ 3 * T ^ p := by linarith
  have h6 : (3 : ℝ) ≤ N * (Real.exp (-Real.log 2 * ϕ) * (2 : ℝ) ^ p) := by nlinarith
  calc Y ^ p + D + R ≤ 3 * T ^ p := h5
    _ ≤ (N * (Real.exp (-Real.log 2 * ϕ) * (2 : ℝ) ^ p)) * T ^ p :=
        mul_le_mul_of_nonneg_right h6 hTp.le
    _ = _ := by ring

/-! ### The one-point bound -/

/-- (5.24) at one point of `S(C)` for `H_γ`: the probability that `|m - m_sc| ≥ 2 φ^E (N η)⁻¹`
is at most `N e^{-(log 2) φ}`. The proof applies the local law (3.2)-(3.3) to the match `H̃` at its
own support parameter, then the moment comparison, then Markov's inequality at an even
`p ≈ φ`. -/
private lemma lsq_point {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ Cx > (0 : ℝ), ∃ E > (0 : ℝ), ∃ N1 : ℕ, ∀ N ≥ N1, ∀ L : EntryLaws N,
      SmallQInterpClass C1 φs N L → ∀ z ∈ specDomain N Cx,
        L.law {ω | 2 * (phi N ^ E / (N * z.im)) ≤ ‖stieltjesM (symOfEntries ω) z - msc z‖} ≤
          ENNReal.ofReal ((N : ℝ) ^ 1 * Real.exp (-Real.log 2 * phi N ^ (1 : ℝ))) := by
  have hφq : 0 < min φs (1 / 4) := lt_min hφs (by norm_num)
  obtain ⟨C0m, hC0m, hmc⟩ := moment_comparison (C1 := C1) (φq := min φs (1 / 4)) hφq
  obtain ⟨Cll, hCll, cl, hcl, Cl', hCl', Nl, hl⟩ :=
    localLaw (ζ := 3) (C0 := max C1 1) (c := 1) (by norm_num) (le_max_of_le_right zero_le_one)
      one_pos
  obtain ⟨Cm, hCm, N0m, hm⟩ := hmc cl hcl (Cl' : ℝ) (by exact_mod_cast hCl')
  have hev : ∀ᶠ N : ℕ in atTop, 16 ≤ N ∧ N0m ≤ N ∧ Nl ≤ N ∧
      ⌈(8 * ((2 * C1 + 4) * C1)) ^ 8⌉₊ ≤ N ∧
      phi N ^ Cll ≤ (N : ℝ) ^ ((1 : ℝ) / 4) ∧
      3 * (10 * ((2 * C1 + 4) * C1) ^ 2 + 2) ≤ phi N ∧ 12 * Cm ^ Cm ≤ phi N ∧
      ((3 : ℝ) + Cl') / cl ≤ phi N := by
    filter_upwards [eventually_ge_atTop 16, eventually_ge_atTop N0m, eventually_ge_atTop Nl,
      eventually_ge_atTop ⌈(8 * ((2 * C1 + 4) * C1)) ^ 8⌉₊,
      phi_rpow_le_rpow Cll (by norm_num : (0 : ℝ) < 1 / 4),
      tendsto_phi_atTop.eventually_ge_atTop (3 * (10 * ((2 * C1 + 4) * C1) ^ 2 + 2)),
      tendsto_phi_atTop.eventually_ge_atTop (12 * Cm ^ Cm),
      tendsto_phi_atTop.eventually_ge_atTop (((3 : ℝ) + Cl') / cl)] with N h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  refine ⟨max C0m Cll, lt_max_of_lt_left hC0m, Cm + (2 * Cll + 3) + 1, by linarith, N1,
    fun N hN L hL z hz => ?_⟩
  obtain ⟨h16, hN0m, hNl, hNK, hϕC, hϕK, hϕm, hϕc⟩ := hN1 N hN
  have hN3 : 3 ≤ N := by omega
  have hNr := lsq_natCast_pos hN3
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hϕ1 := sc_one_le_phi hN3
  have hϕ0 : 0 < phi N := by linarith
  have hlogϕ : Real.log N ≤ phi N := log_le_phi h16
  have hCx0 : 0 ≤ max C0m Cll := (lt_max_of_lt_left hC0m).le
  have hz0 : z ∈ specDomain N C0m := lsq_specDomain_mono hN3 (le_max_left _ _) hz
  have hzl : z ∈ specDomain N Cll := lsq_specDomain_mono hN3 (le_max_right _ _) hz
  have ht1 := lsq_one_lt_mul_im hN3 hCx0 hz
  have hη : 0 < z.im := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hη10 : z.im ≤ 10 := hz.2.2
  obtain ⟨Lv, Lw, γ, hv, hw, rfl⟩ := hL
  have hqt := tilde_pos hN3 hv.1 hw
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hKpos : 0 < (2 * C1 + 4) * C1 := by
    have h1 : 0 < (2 * C1 + 4) * C1 * Real.log N :=
      (div_pos_iff_of_pos_left (Real.sqrt_pos.mpr hNr)).1 hqt
    exact (mul_pos_iff_of_pos_right hlog).1 h1
  have hmp0 := MatchedPair.of_smallQ hN3 hv hw
  have hmp := hmp0.interp γ
  have hNK' : (8 * ((2 * C1 + 4) * C1)) ^ 8 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  have hq1 := rpow_quarter_le_tilde hN3 hKpos hNK'
  have hq : (N : ℝ) ^ (min φs (1 / 4)) ≤
      min ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) :=
    le_min (Real.rpow_le_rpow_of_exponent_le h1N (min_le_left _ _))
      ((Real.rpow_le_rpow_of_exponent_le h1N (min_le_right _ _)).trans hq1)
  -- the local law for the match
  have hGW : Lw.IsGenWigner (max C1 1) := (MatchedPair.isGenWigner hmp0).2
  have hSP : Lw.SupportParam (phi N ^ Cll) 1
      (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) :=
    ⟨hϕC.trans hq1, hw.2.1.boundedSupport 1, hw.2.1.tailVarOff 1⟩
  obtain ⟨hX0, hY0, hX2, hY1⟩ := lsq_err_bound (Cl := Cll) (C := Cll) h16 hCll.le hCll.le hKpos
    hϕK hzl
  set X := entryErr N Cll (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) z with hXdef
  set Y := avgErr N Cll (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) z with hYdef
  have hsub : {ω : Entries N | ∀ q, Lw.SupportParam (phi N ^ Cll) 1 q → ω ∈ localLawEvent N Cll q} ⊆
      {ω | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
        ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y} := by
    intro ω hω
    have h := hω _ hSP z hzl
    refine ⟨fun i j hij => ?_, h.1⟩
    have h2 := h.2 i j
    have h3 : (if i = j then msc z else 0) = 0 := by simp [hij]
    rw [h3, sub_zero] at h2
    exact h2
  have hA : Lw.law {ω : Entries N | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
        ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ (Cl' : ℝ) * Real.exp (-cl * phi N ^ (3 : ℝ))) := by
    rw [Real.rpow_natCast]
    exact (measure_mono (Set.compl_subset_compl.2 hsub)).trans (hl N hNl Lw hGW)
  -- the even exponent `p ≈ φ`
  obtain ⟨p, hpev, hpϕ, hpge⟩ : ∃ p : ℕ, Even p ∧ (p : ℝ) ≤ phi N ∧ phi N - 2 ≤ p := by
    refine ⟨2 * ⌊phi N / 2⌋₊, even_two_mul _, ?_, ?_⟩
    · have := Nat.floor_le (show 0 ≤ phi N / 2 by positivity)
      push_cast; linarith
    · have := Nat.lt_floor_add_one (phi N / 2)
      push_cast; linarith
  have hmom := hm N hN0m _ Lw _ hmp hq z hz0 X Y hX0 hY0 hA p hpev hpϕ
  -- the scales
  set t : ℝ := (N : ℝ) * z.im with ht
  have ht0 : 0 < t := by linarith
  have ht10 : t ≤ 10 * N := by rw [ht]; nlinarith
  set D : ℝ := 2 * Cll + 3 with hD
  have hD1 : 1 ≤ D := by linarith
  set E : ℝ := Cm + D + 1 with hE
  set T : ℝ := phi N ^ E / t with hT
  have hT0 : 0 < T := div_pos (Real.rpow_pos_of_pos hϕ0 _) ht0
  have hYT : Y ≤ T :=
    hY1.trans (div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hϕ1 (by linarith))
      ht0.le)
  have hS : X ^ 2 + Y + phi N / N ≤ 12 * phi N ^ D / t := by
    have hD' : phi N ≤ phi N ^ D := by
      calc phi N = phi N ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ phi N ^ D := Real.rpow_le_rpow_of_exponent_le hϕ1 hD1
    have h1 : phi N / N ≤ 10 * phi N ^ D / t := by
      rw [div_le_div_iff₀ hNr ht0]
      calc phi N * t ≤ phi N * (10 * N) := mul_le_mul_of_nonneg_left ht10 hϕ0.le
        _ ≤ phi N ^ D * (10 * N) := mul_le_mul_of_nonneg_right hD' (by positivity)
        _ = 10 * phi N ^ D * N := by ring
    calc X ^ 2 + Y + phi N / N ≤ phi N ^ D / t + phi N ^ D / t + 10 * phi N ^ D / t :=
          add_le_add (add_le_add hX2 hY1) h1
      _ = 12 * phi N ^ D / t := by ring
  have hRle : (Cm * p) ^ (Cm * p) * (X ^ 2 + Y + phi N / N) ^ p ≤ T ^ p := by
    have hCmp : 0 ≤ Cm * p := by positivity
    have hS0 : 0 ≤ X ^ 2 + Y + phi N / N := by positivity
    rw [Real.rpow_mul_natCast hCmp Cm p, ← mul_pow]
    refine pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg hCmp _) hS0) ?_ p
    have e1 : (Cm * p) ^ Cm ≤ Cm ^ Cm * phi N ^ Cm := by
      rw [← Real.mul_rpow hCm.le hϕ0.le]
      exact Real.rpow_le_rpow hCmp (mul_le_mul_of_nonneg_left hpϕ hCm.le) hCm.le
    have hpow : phi N ^ E = phi N * (phi N ^ Cm * phi N ^ D) := by
      rw [hE, Real.rpow_add hϕ0, Real.rpow_add hϕ0, Real.rpow_one]; ring
    calc (Cm * p) ^ Cm * (X ^ 2 + Y + phi N / N)
        ≤ (Cm ^ Cm * phi N ^ Cm) * (12 * phi N ^ D / t) :=
          mul_le_mul e1 hS hS0 (by positivity)
      _ = (12 * Cm ^ Cm) * (phi N ^ Cm * phi N ^ D) / t := by ring
      _ ≤ phi N * (phi N ^ Cm * phi N ^ D) / t := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hϕm (by positivity)) ht0.le
      _ = T := by rw [hT, hpow]
  have hTlow : 1 / (10 * (N : ℝ)) ≤ T := by
    rw [hT, div_le_div_iff₀ (by positivity) ht0]
    have : 1 ≤ phi N ^ E := Real.one_le_rpow hϕ1 (by linarith)
    nlinarith
  have hBδ : ((N : ℝ) + 1) ^ p * ((N : ℝ) ^ (Cl' : ℝ) * Real.exp (-cl * phi N ^ (3 : ℝ))) ≤
      T ^ p :=
    (lsq_tiny (by omega) hlogϕ hϕ1 hpϕ hcl (by positivity) hϕc).trans
      (pow_le_pow_left₀ (by positivity) hTlow p)
  -- Markov's inequality
  have := isProbabilityMeasure_law hmp.isProb_v
  have := isProbabilityMeasure_law hmp.isProb_w
  have hbadsub : {ω : Entries N | Y < ‖stieltjesM (symOfEntries ω) z - msc z‖} ⊆
      {ω : Entries N | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
        ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y}ᶜ := by
    intro ω hω hG
    exact absurd hG.2 (not_le.2 hω)
  have hbad : Lw.law {ω | Y < ‖stieltjesM (symOfEntries ω) z - msc z‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ (Cl' : ℝ) * Real.exp (-cl * phi N ^ (3 : ℝ))) :=
    (measure_mono hbadsub).trans hA
  have hmark := lsq_markov (μ := (interp (lexPos N) γ Lv Lw).law) (ν := Lw.law)
    (f := fun ω => ‖stieltjesM (symOfEntries ω) z - msc z‖)
    (((lsq_measurable_stieltjesM z).sub_const (msc z)).norm) (fun ω => norm_nonneg _)
    (B := (N : ℝ) + 1) (by positivity) (fun ω => lsq_norm_sub_le hN3 hCx0 hz ω) (p := p)
    (Y := Y) (T := T) hY0 hT0 (by positivity) hmom hbad
  refine hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  exact lsq_final_arith (by omega) hT0 hpge (pow_le_pow_left₀ hY0 hYT p) hRle hBδ

/-! ### The grid in `z` -/

open Classical in
/-- The grid of mesh `N⁻²` in `S(C)`: the points `(a + i b) N⁻²` with `|a| ≤ 5 N²`,
`1 ≤ b ≤ 10 N²` and `b N⁻² > φ^C / N`, for `N ≥ 121`. -/
private def lsqGrid (N : ℕ) (C : ℝ) : Finset (ℤ × ℕ) :=
  if 121 ≤ N then
    Finset.Icc (-(5 * (N : ℤ) ^ 2)) (5 * (N : ℤ) ^ 2) ×ˢ
      (Finset.Icc 1 (10 * N ^ 2)).filter (fun b : ℕ => phi N ^ C / N < (b : ℝ) / (N : ℝ) ^ 2)
  else ∅

/-- The point `(a + i b) N⁻²` of the grid. -/
private def lsqPt (N : ℕ) (k : ℤ × ℕ) : ℂ := ⟨(k.1 : ℝ) / (N : ℝ) ^ 2, (k.2 : ℝ) / (N : ℝ) ^ 2⟩

private lemma lsqGrid_card (N : ℕ) (C : ℝ) : ((lsqGrid N C).card : ℝ) ≤ (N : ℝ) ^ 5 := by
  unfold lsqGrid
  split_ifs with h
  · have hI : (Finset.Icc (-(5 * (N : ℤ) ^ 2)) (5 * (N : ℤ) ^ 2)).card = 10 * N ^ 2 + 1 := by
      rw [Int.card_Icc]
      have : (N : ℤ) ^ 2 = ((N ^ 2 : ℕ) : ℤ) := by push_cast; ring
      rw [this]
      omega
    have hc : ((Finset.Icc (-(5 * (N : ℤ) ^ 2)) (5 * (N : ℤ) ^ 2) ×ˢ
        (Finset.Icc 1 (10 * N ^ 2)).filter
          (fun b : ℕ => phi N ^ C / N < (b : ℝ) / (N : ℝ) ^ 2)).card) ≤
        (10 * N ^ 2 + 1) * (10 * N ^ 2) := by
      rw [Finset.card_product, hI]
      refine Nat.mul_le_mul le_rfl ((Finset.card_filter_le _ _).trans ?_)
      simp
    have hNr : (121 : ℝ) ≤ N := by exact_mod_cast h
    calc _ ≤ (((10 * N ^ 2 + 1) * (10 * N ^ 2) : ℕ) : ℝ) := by exact_mod_cast hc
      _ = (10 * (N : ℝ) ^ 2 + 1) * (10 * (N : ℝ) ^ 2) := by push_cast; ring
      _ ≤ (N : ℝ) ^ 5 := by
          have h2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
          have h3 : (121 : ℝ) * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
            nlinarith [mul_le_mul_of_nonneg_left hNr h2]
          have h4 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h3 h2, mul_nonneg h2 h2]
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity

private lemma lsqGrid_mem {N : ℕ} {C : ℝ} {k : ℤ × ℕ} (hk : k ∈ lsqGrid N C) :
    121 ≤ N ∧ lsqPt N k ∈ specDomain N C := by
  unfold lsqGrid at hk
  split_ifs at hk with h
  · refine ⟨h, ?_⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hb3⟩ := hk
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by
      have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      positivity
    have ha1' : -(5 * (N : ℝ) ^ 2) ≤ (k.1 : ℝ) := by exact_mod_cast ha1
    have ha2' : (k.1 : ℝ) ≤ 5 * (N : ℝ) ^ 2 := by exact_mod_cast ha2
    have hb2' : (k.2 : ℝ) ≤ 10 * (N : ℝ) ^ 2 := by exact_mod_cast hb2
    refine ⟨?_, hb3, ?_⟩
    · change |(k.1 : ℝ) / (N : ℝ) ^ 2| ≤ 5
      rw [abs_div, abs_of_pos hN2, div_le_iff₀ hN2, abs_le]
      constructor <;> linarith
    · change (k.2 : ℝ) / (N : ℝ) ^ 2 ≤ 10
      rw [div_le_iff₀ hN2]
      linarith
  · simp at hk

/-- From the bound `|m - m_sc| < 2 φ^E (N Im w)⁻¹` at the grid points `w` of `S(C_x)` to the bound
`|m - m_sc| ≤ φ^C (N Im z)⁻¹` on all of `S(C)`, `C = max(C_x, E + 1)`. Every `z ∈ S(C)` lies within
`2 N⁻²` of a grid point at least as high, and `|m(z) - m(w)|`, `|m_sc(z) - m_sc(w)|` are at most
`|z - w| / (Im z Im w)`. -/
private lemma lsq_grid_step {N : ℕ} {Cx E : ℝ} (hN : 121 ≤ N) (hCx : 0 ≤ Cx) (hE : 0 ≤ E)
    (hϕ : 6 ≤ phi N) (ω : Entries N)
    (hω : ∀ k ∈ lsqGrid N Cx, ‖stieltjesM (symOfEntries ω) (lsqPt N k) - msc (lsqPt N k)‖ <
      2 * (phi N ^ E / (N * (lsqPt N k).im)))
    {z : ℂ} (hz : z ∈ specDomain N (max Cx (E + 1))) :
    ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ (max Cx (E + 1)) / (N * z.im) := by
  have hN3 : 3 ≤ N := by omega
  have hNr := lsq_natCast_pos hN3
  have hϕ1 : 1 ≤ phi N := by linarith
  have hϕ0 : 0 < phi N := by linarith
  have hCz0 : 0 ≤ max Cx (E + 1) := le_max_of_le_left hCx
  have hzCx : z ∈ specDomain N Cx := lsq_specDomain_mono hN3 (le_max_left _ _) hz
  have ht1 := lsq_one_lt_mul_im hN3 hCz0 hz
  have hη : 0 < z.im := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hre := abs_le.1 hz.1
  have hη10 : z.im ≤ 10 := hz.2.2
  have hlo : -(5 * (N : ℝ) ^ 2) ≤ z.re * (N : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hre.1 hN2.le]
  have hhi : z.im * (N : ℝ) ^ 2 ≤ 10 * (N : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hη10 hN2.le]
  obtain ⟨a, ha0, ha1, ha2⟩ : ∃ a : ℤ, -(5 * (N : ℤ) ^ 2) ≤ a ∧ (a : ℝ) ≤ z.re * (N : ℝ) ^ 2 ∧
      z.re * (N : ℝ) ^ 2 < a + 1 :=
    ⟨⌊z.re * (N : ℝ) ^ 2⌋, Int.le_floor.2 (by push_cast; exact hlo), Int.floor_le _,
      Int.lt_floor_add_one _⟩
  obtain ⟨b, hb0, hb1, hb2⟩ : ∃ b : ℕ, b ≤ 10 * N ^ 2 ∧ z.im * (N : ℝ) ^ 2 ≤ b ∧
      (b : ℝ) < z.im * (N : ℝ) ^ 2 + 1 :=
    ⟨⌈z.im * (N : ℝ) ^ 2⌉₊, Nat.ceil_le.2 (by push_cast; exact hhi), Nat.le_ceil _,
      Nat.ceil_lt_add_one (by positivity)⟩
  have hzb : z.im ≤ (b : ℝ) / (N : ℝ) ^ 2 := by rw [le_div_iff₀ hN2]; exact hb1
  have hk : (a, b) ∈ lsqGrid N Cx := by
    simp only [lsqGrid, hN, ↓reduceIte]
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨ha0, ?_⟩, ⟨?_, hb0⟩, ?_⟩
    · have : (a : ℝ) ≤ ((5 * (N : ℤ) ^ 2 : ℤ) : ℝ) := by
        push_cast; nlinarith [mul_le_mul_of_nonneg_right hre.2 hN2.le]
      exact_mod_cast this
    · have : (0 : ℝ) < b := by
        have : 0 < z.im * (N : ℝ) ^ 2 := by positivity
        linarith
      exact_mod_cast this
    · exact lt_of_lt_of_le hzCx.2.1 hzb
  have hwim : z.im ≤ (lsqPt N (a, b)).im := hzb
  have hwpos : 0 < (lsqPt N (a, b)).im := lt_of_lt_of_le hη hwim
  -- the distance to the grid point
  have hdre : |z.re - (lsqPt N (a, b)).re| ≤ 1 / (N : ℝ) ^ 2 := by
    have h1 : (a : ℝ) / (N : ℝ) ^ 2 ≤ z.re := by rw [div_le_iff₀ hN2]; exact ha1
    have h2 : z.re < ((a : ℝ) + 1) / (N : ℝ) ^ 2 := by rw [lt_div_iff₀ hN2]; exact ha2
    have h3 : ((a : ℝ) + 1) / (N : ℝ) ^ 2 = (a : ℝ) / (N : ℝ) ^ 2 + 1 / (N : ℝ) ^ 2 := by
      rw [add_div]
    change |z.re - (a : ℝ) / (N : ℝ) ^ 2| ≤ 1 / (N : ℝ) ^ 2
    rw [abs_le]
    constructor <;> linarith [one_div_pos.2 hN2]
  have hdim : |z.im - (lsqPt N (a, b)).im| ≤ 1 / (N : ℝ) ^ 2 := by
    have h2 : (b : ℝ) / (N : ℝ) ^ 2 < z.im + 1 / (N : ℝ) ^ 2 := by
      rw [div_lt_iff₀ hN2, add_mul, one_div, inv_mul_cancel₀ hN2.ne']
      exact hb2
    change |z.im - (b : ℝ) / (N : ℝ) ^ 2| ≤ 1 / (N : ℝ) ^ 2
    rw [abs_le]
    constructor <;> linarith [one_div_pos.2 hN2]
  have hdist : ‖z - lsqPt N (a, b)‖ ≤ 2 / (N : ℝ) ^ 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have : (2 : ℝ) / (N : ℝ) ^ 2 = 1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) ^ 2 := by ring
    rw [this]
    exact add_le_add hdre hdim
  -- Lipschitz bounds
  set w := lsqPt N (a, b) with hw
  have hlip : ‖z - w‖ / (z.im * w.im) ≤ 2 / (N * z.im) := by
    calc ‖z - w‖ / (z.im * w.im) ≤ (2 / (N : ℝ) ^ 2) / (z.im * z.im) := by
          apply div_le_div₀ (by positivity) hdist (by positivity)
          exact mul_le_mul_of_nonneg_left hwim hη.le
      _ ≤ 2 / (N * z.im) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_pos hNr hη]
  have hL1 := weak_norm_stieltjesM_sub_le (H := symOfEntries ω) (by omega)
    (symOfEntries_isHermitian ω) hη hwpos
  have hL2 := weak_norm_msc_sub_le hη hwpos
  have hgrid := hω (a, b) hk
  have hgrid' : ‖stieltjesM (symOfEntries ω) w - msc w‖ ≤ 2 * phi N ^ E / (N * z.im) := by
    refine hgrid.le.trans ?_
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hwim hNr.le
  have e : stieltjesM (symOfEntries ω) z - msc z =
      (stieltjesM (symOfEntries ω) w - msc w) + (stieltjesM (symOfEntries ω) z -
        stieltjesM (symOfEntries ω) w) - (msc z - msc w) := by ring
  have hmain : ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤
      2 * phi N ^ E / (N * z.im) + 2 / (N * z.im) + 2 / (N * z.im) := by
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := norm_add_le (stieltjesM (symOfEntries ω) w - msc w)
      (stieltjesM (symOfEntries ω) z - stieltjesM (symOfEntries ω) w)
    linarith
  refine hmain.trans ?_
  have hpE : 1 ≤ phi N ^ E := Real.one_le_rpow hϕ1 hE
  have hpE1 : phi N ^ (E + 1) = phi N ^ E * phi N := by
    rw [Real.rpow_add hϕ0, Real.rpow_one]
  have hmax : phi N ^ (E + 1) ≤ phi N ^ (max Cx (E + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hϕ1 (le_max_right _ _)
  have ht0 : 0 < (N : ℝ) * z.im := by positivity
  calc 2 * phi N ^ E / (N * z.im) + 2 / (N * z.im) + 2 / (N * z.im)
      = (2 * phi N ^ E + 4) / (N * z.im) := by ring
    _ ≤ phi N ^ (E + 1) / (N * z.im) := by
        refine div_le_div_of_nonneg_right ?_ ht0.le
        rw [hpE1]
        nlinarith
    _ ≤ _ := div_le_div_of_nonneg_right hmax ht0.le

/-! ### (5.24) -/

/-- (5.24) for every `H_γ` between a law of Theorem 3.6 and its match (used for
(6.82)); `γ = γmax` gives the law itself. -/
theorem stieltjes_local_smallQInterp {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ C > (0 : ℝ), HighProbOn 1 (SmallQInterpClass C1 φs)
      (fun N _ => {ω | ∀ z ∈ specDomain N C,
        ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ C / (N * z.im)}) := by
  obtain ⟨Cx, hCx, E, hE, N1, hpt⟩ := lsq_point (C1 := C1) hφs
  refine ⟨max Cx (E + 1), lt_max_of_lt_left hCx, ?_⟩
  have hcard : ∀ N : ℕ, (Fintype.card (lsqGrid N Cx) : ℝ) ≤ (N : ℝ) ^ (5 : ℝ) := by
    intro N
    rw [Fintype.card_coe, show (N : ℝ) ^ (5 : ℝ) = (N : ℝ) ^ 5 by
      rw [← Real.rpow_natCast]; norm_num]
    exact lsqGrid_card N Cx
  have hgrid := HighProbOn.iInter (ζ := 1) (K := 5) (Cls := SmallQInterpClass C1 φs)
    (ι := fun N => lsqGrid N Cx) hcard
    (Ω := fun N k _ => {ω : Entries N | ‖stieltjesM (symOfEntries ω) (lsqPt N k.1) -
      msc (lsqPt N k.1)‖ < 2 * (phi N ^ E / (N * (lsqPt N k.1).im))})
    ⟨Real.log 2, Real.log_pos one_lt_two, 1, one_pos, max N1 121, fun N hN k L hL => ?_⟩
  · obtain ⟨N6, hN6⟩ := eventually_atTop.1 (tendsto_phi_atTop.eventually_ge_atTop 6)
    refine HighProbOn.mono_eventually hgrid (fun N L h => h)
      ⟨max N6 121, fun N hN L hL ω hω z hz => ?_⟩
    exact lsq_grid_step (le_trans (le_max_right _ _) hN) hCx.le hE.le
      (hN6 N (le_trans (le_max_left _ _) hN)) ω (fun k hk => Set.mem_iInter.1 hω ⟨k, hk⟩) hz
  · obtain ⟨-, hmem⟩ := lsqGrid_mem k.2
    have h := hpt N (le_trans (le_max_left _ _) hN) L hL _ hmem
    have heq : ({ω : Entries N | ‖stieltjesM (symOfEntries ω) (lsqPt N k.1) -
        msc (lsqPt N k.1)‖ < 2 * (phi N ^ E / (N * (lsqPt N k.1).im))})ᶜ =
        {ω : Entries N | 2 * (phi N ^ E / (N * (lsqPt N k.1).im)) ≤
          ‖stieltjesM (symOfEntries ω) (lsqPt N k.1) - msc (lsqPt N k.1)‖} := by
      ext ω
      simp
    rw [heq]
    exact h

/-- (5.24): `max_{z ∈ S(C)} |m - m_sc| ≤ φ^C (Nη)⁻¹` with high probability. -/
theorem stieltjes_local_smallQ {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ C > (0 : ℝ), HighProbOn 1 (SmallQClass C1 φs)
      (fun N _ => {ω | ∀ z ∈ specDomain N C,
        ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ C / (N * z.im)}) := by
  obtain ⟨C, hC, c, hc, C', hC', N0, h⟩ := stieltjes_local_smallQInterp (C1 := C1) hφs
  refine ⟨C, hC, c, hc, C', hC', max N0 3, fun N hN L hL => ?_⟩
  obtain ⟨Lw, hw⟩ := exists_isMomentMatch (le_trans (le_max_right _ _) hN) hL.1
  exact h N (le_trans (le_max_left _ _) hN) L
    ⟨L, Lw, N * (N + 1) / 2, hL, hw, (interp_lexPos_top L Lw).symm⟩

/-! ### Nondegenerate instances of the classes -/

/-- For large `N` the Rademacher laws satisfy the moment conditions of Theorem 3.6 with `C1 = 2`
and are almost surely bounded by `N^{-2/5}`. -/
private lemma lsq_radLaws_smallQ :
    ∀ᶠ N : ℕ in atTop, SmallQClass 2 (2 / 5) N (radLaws N) := by
  filter_upwards [expansion_matchedPair_radLaws, eventually_ge_atTop 32] with N hmp h32
  have hNpos : 0 < N := by omega
  have hsupp := radLaws_boundedSupportAS h32
  refine ⟨⟨hmp.isProb_v, (hsupp.integrable_pow hmp.isProb_v 2).1,
    (hsupp.integrable_pow hmp.isProb_v 4).2, hmp.mean_diag, hmp.mean_off, hmp.var_diag_le,
    hmp.var_off, fun p => ?_, hmp.fourth_off_le⟩, hsupp⟩
  rw [integral_abs_pow_three_radLaws_off hNpos p]
  have : 0 ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  linarith

/-- The class of Theorem 3.6 is nonempty for all large `N` (the Rademacher laws, `C1 = 2`,
`φs = 2/5`), and every interpolation `H_γ` of such a law with a Lemma 5.1 match lies in
`SmallQInterpClass`; so the hypotheses of both targets are satisfiable for every large `N`. -/
example : ∀ᶠ N : ℕ in atTop, SmallQClass 2 (2 / 5) N (radLaws N) ∧
    ∀ γ : ℕ, ∃ Lw : EntryLaws N,
      SmallQInterpClass 2 (2 / 5) N (interp (lexPos N) γ (radLaws N) Lw) := by
  filter_upwards [lsq_radLaws_smallQ, eventually_ge_atTop 3] with N hc h3
  refine ⟨hc, fun γ => ?_⟩
  obtain ⟨Lw, hw⟩ := exists_isMomentMatch h3 hc.1
  exact ⟨Lw, radLaws N, Lw, γ, hc, hw, rfl⟩

/-- A second instance at `N = 16`, `C1 = 2`, `φs = 1/4`, where the law and its match differ: the
law `lawV` and `H_5` between `lawV` and its match `lawW`. -/
example : SmallQClass 2 (1 / 4) 16 lawV ∧
    SmallQInterpClass 2 (1 / 4) 16 (interp (lexPos 16) 5 lawV lawW) :=
  ⟨⟨lawV_momentCond, lawV_supp⟩,
    ⟨lawV, lawW, 5, ⟨lawV_momentCond, lawV_supp⟩, lawVW_isMomentMatch, rfl⟩⟩

#print axioms stieltjes_local_smallQInterp
#print axioms stieltjes_local_smallQ

end WEdgeNS
