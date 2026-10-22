import WEdgeNS.Comparison.IterateWeight
import WEdgeNS.Semicircle.Stieltjes

/-!
# Off-diagonal resolvent moments for small support (Lemma 3.8)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private tilde_pos rpow_quarter_le_tilde from WEdgeNS.Comparison.Classes
open private expansion_matchedPair_radLaws from WEdgeNS.Comparison.Expansion

/-! ### Inputs: the lower bound on `Im m_sc`, the local law of `H̃`, and `η > 10` -/

/-- `Im m_sc(z) ≥ η/(49 + η²)` for `|E| ≤ 5`, `η > 0`: in `m_sc(z) = ∫ ρ_sc(x)(x - z)⁻¹ dx`
(Definition 2.5, (2.8)–(2.9)) the support of `ρ_sc` is `[-2, 2]`, so `|x - E| ≤ 7`. For `η ≤ 10`
this gives `N⁻¹ ≤ 149 Im m_sc/(Nη)`, the lower bound of the right side of (3.15) used in
(6.40)–(6.41). -/
private theorem div_le_im_msc {z : ℂ} (hE : |z.re| ≤ 5) (hz : 0 < z.im) :
    z.im / (49 + z.im ^ 2) ≤ (msc z).im := by
  have hprob := isProbabilityMeasure_semicircle
  set f : ℝ → ℂ := fun x => ((x : ℂ) - z)⁻¹ with hf
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := by
    intro x h
    have h1 : ((x : ℂ) - z).im = 0 := by rw [h]; rfl
    simp at h1
    linarith
  have hfc : Continuous f := Continuous.inv₀ (by fun_prop) hne
  have hfint : Integrable f semicircle := by
    refine Integrable.of_bound hfc.aestronglyMeasurable (1 / z.im) (Eventually.of_forall
      fun x => ?_)
    rw [hf, norm_inv, one_div]
    refine inv_anti₀ hz ?_
    calc z.im = |((x : ℂ) - z).im| := by simp [abs_of_pos hz]
      _ ≤ ‖(x : ℂ) - z‖ := Complex.abs_im_le_norm _
  have hrt : resolventTransform semicircle z = ∫ x, f x ∂semicircle := by
    rw [resolventTransform_apply]
    congr 1
    funext x
    simp [resolvent, hf, Ring.inverse_eq_inv']
  have him : (∫ x, f x ∂semicircle).im = ∫ x, (f x).im ∂semicircle :=
    (Complex.imCLM.integral_comp_comm hfint).symm
  have hfim : ∀ x : ℝ, (f x).im = z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
    intro x
    simp only [hf, Complex.inv_im, Complex.sub_im, Complex.ofReal_im, Complex.normSq_apply,
      Complex.sub_re, Complex.ofReal_re]
    ring
  have hsupp : ∀ᵐ x ∂semicircle, |x| ≤ 2 := by
    unfold semicircle
    rw [ae_withDensity_iff (by
      have : Continuous rhoSc := by unfold rhoSc; fun_prop
      exact this.measurable.ennreal_ofReal)]
    refine Eventually.of_forall fun x hx => ?_
    by_contra hlt
    rw [not_le] at hlt
    apply hx
    rw [ENNReal.ofReal_eq_zero]
    unfold rhoSc
    rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [abs_mul_abs_self x, abs_nonneg x]), zero_div]
  rw [msc_eq_resolventTransform hz, hrt, him]
  have hconst : ∫ _x, z.im / (49 + z.im ^ 2) ∂semicircle = z.im / (49 + z.im ^ 2) := by simp
  rw [← hconst]
  refine integral_mono_ae (integrable_const _) (hfint.im) ?_
  filter_upwards [hsupp] with x hx
  rw [hfim]
  have h7 : (x - z.re) ^ 2 ≤ 49 := by
    have h1 : |x - z.re| ≤ 7 := (abs_sub _ _).trans (by linarith)
    have h2 : (x - z.re) ^ 2 = |x - z.re| ^ 2 := (sq_abs _).symm
    rw [h2]
    nlinarith [abs_nonneg (x - z.re)]
  exact div_le_div_of_nonneg_left hz.le (by positivity) (by linarith)

/-- The local law (3.3) (Lemma 3.1 with Remark 3.2, at `ζ = 1`) for the Lemma 5.1 match `H̃` of a
law of Theorem 3.6, with the support `q̃ = √N/((2C1+4)C1 log N)` of `H̃` itself, on `S(C)`, with
high probability; this is the input (6.39). -/
private theorem localLaw_isMomentMatch {C1 φs : ℝ} :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ Lv Lw : EntryLaws N,
      SmallQClass C1 φs N Lv → Lv.IsMomentMatch Lw C1 →
      Lw.law {ω | ∀ z ∈ specDomain N C, ∀ x y,
          ‖resS z ω x y - (if x = y then msc z else 0)‖ ≤
            entryErr N C (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) z}ᶜ ≤
        ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c * phi N)) := by
  obtain ⟨CL, hCL, hHP⟩ := localLaw (ζ := 1) (C0 := max C1 1) (c := 1) one_pos
    (le_max_of_le_right zero_le_one) one_pos
  obtain ⟨ch, hch, Ch, hCh, Nh, hP⟩ := hHP
  have hev := (eventually_ge_atTop (max Nh (max 3 ⌈(8 * ((2 * C1 + 4) * C1)) ^ 8⌉₊))).and
    (phi_rpow_le_rpow CL (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨CL, hCL, ch, hch, (Ch : ℝ), by exact_mod_cast hCh, N0, fun N hN Lv Lw hv hw => ?_⟩
  obtain ⟨hNbig, hφ⟩ := hN0 N hN
  have hNh : Nh ≤ N := le_trans (le_max_left _ _) hNbig
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNbig
  have hNKn : ⌈(8 * ((2 * C1 + 4) * C1)) ^ 8⌉₊ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNbig
  have hNK : (8 * ((2 * C1 + 4) * C1)) ^ 8 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNKn)
  have hN0r : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hKpos : 0 < (2 * C1 + 4) * C1 := by
    have h1 : 0 < (2 * C1 + 4) * C1 * Real.log N :=
      (div_pos_iff_of_pos_left (Real.sqrt_pos.mpr hN0r)).1 (tilde_pos hN3 hv.1 hw)
    exact (mul_pos_iff_of_pos_right hlogN).1 h1
  set qt : ℝ := Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N) with hqt
  have hqt4 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ qt := rpow_quarter_le_tilde hN3 hKpos hNK
  have hGW : Lw.IsGenWigner (max C1 1) := (MatchedPair.of_smallQ hN3 hv hw).isGenWigner.2
  have hSP : Lw.SupportParam (phi N ^ CL) 1 qt :=
    ⟨hφ.trans hqt4, hw.2.1.boundedSupport 1, hw.2.1.tailVarOff 1⟩
  have h := hP N hNh Lw hGW
  rw [Real.rpow_one, ← Real.rpow_natCast] at h
  refine le_trans (measure_mono (Set.compl_subset_compl.2 fun ω hω => ?_)) h
  intro z hz x y
  exact (hω qt hSP z hz).2 x y

/-- `E Σ_{k,l} A_kl x_k x_l = Σ_k A_kk E x_k²` for pairwise independent, centred, bounded `x_k`. -/
private lemma integral_sum_sum_mul {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : Finset κ) (x : κ → Ω → ℝ) (A : κ → κ → ℝ) {M : ℝ}
    (hm : ∀ k, Measurable (x k)) (hb : ∀ k, ∀ᵐ ω ∂μ, |x k ω| ≤ M)
    (hind : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → IndepFun (x k) (x l) μ)
    (hmean : ∀ k ∈ S, ∫ ω, x k ω ∂μ = 0) :
    ∫ ω, ∑ k ∈ S, ∑ l ∈ S, A k l * (x k ω * x l ω) ∂μ =
      ∑ k ∈ S, A k k * ∫ ω, x k ω ^ 2 ∂μ := by
  have hint : ∀ k l, Integrable (fun ω => x k ω * x l ω) μ := fun k l =>
    Integrable.of_bound ((hm k).mul (hm l)).aestronglyMeasurable (M * M) (by
      filter_upwards [hb k, hb l] with ω h1 h2
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => (hint k l).const_mul _)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ (fun l _ => (hint k l).const_mul _), Finset.sum_eq_single k]
  · rw [integral_const_mul]
    congr 1
    congr 1
    funext ω
    ring
  · intro l hl hlk
    rw [integral_const_mul, (hind k hk l hl (Ne.symm hlk)).integral_fun_mul_eq_mul_integral
      (hm k).aestronglyMeasurable (hm l).aestronglyMeasurable, hmean k hk]
    simp
  · intro h
    exact absurd hk h

/-- `E|Σ_k c_k x_k|² = Σ_k |c_k|² E x_k²` for pairwise independent, centred, bounded real `x_k`. -/
private lemma integral_norm_sq_sum_mul {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : Finset κ) (x : κ → Ω → ℝ) (c : κ → ℂ) {M : ℝ}
    (hm : ∀ k, Measurable (x k)) (hb : ∀ k, ∀ᵐ ω ∂μ, |x k ω| ≤ M)
    (hind : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → IndepFun (x k) (x l) μ)
    (hmean : ∀ k ∈ S, ∫ ω, x k ω ∂μ = 0) :
    ∫ ω, ‖∑ k ∈ S, c k * (x k ω : ℂ)‖ ^ 2 ∂μ = ∑ k ∈ S, ‖c k‖ ^ 2 * ∫ ω, x k ω ^ 2 ∂μ := by
  have hpt : ∀ ω, ‖∑ k ∈ S, c k * (x k ω : ℂ)‖ ^ 2 =
      ∑ k ∈ S, ∑ l ∈ S, (c k * (starRingEnd ℂ) (c l)).re * (x k ω * x l ω) := by
    intro ω
    have h1 : ((‖∑ k ∈ S, c k * (x k ω : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ k ∈ S, ∑ l ∈ S, (c k * (starRingEnd ℂ) (c l)) * ((x k ω * x l ω : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    have h2 := congrArg Complex.re h1
    rw [Complex.ofReal_re] at h2
    rw [h2, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.re_mul_ofReal]
  simp_rw [hpt]
  rw [integral_sum_sum_mul S x _ hm hb hind hmean]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The coordinate of `ω` holding the entry `(a, b)` of `symOfEntries ω`. -/
private def entryOf {N : ℕ} (a b : Fin N) : Fin N ⊕ OffDiag N :=
  if h : a < b then Sum.inr ⟨(a, b), h⟩ else if h' : b < a then Sum.inr ⟨(b, a), h'⟩ else Sum.inl a

private lemma symOfEntries_eq_entryCoord {N : ℕ} (ω : Entries N) (a b : Fin N) :
    symOfEntries ω a b = entryCoord (entryOf a b) ω := by
  unfold symOfEntries entryOf
  by_cases h : a < b
  · simp [h, ne_of_lt h, entryCoord]
  · by_cases h' : b < a
    · simp [h, h', ne_of_gt h', entryCoord]
    · have hab : a = b := le_antisymm (not_lt.mp h') (not_lt.mp h)
      subst hab
      simp [entryCoord]

private lemma entryOf_inj {N : ℕ} {r k l : Fin N} (hk : k ≠ r) (hl : l ≠ r)
    (h : entryOf r k = entryOf r l) : k = l := by
  unfold entryOf at h
  have hk' : (k : ℕ) ≠ r := fun e => hk (Fin.ext e)
  have hl' : (l : ℕ) ≠ r := fun e => hl (Fin.ext e)
  apply Fin.ext
  split_ifs at h with h1 h2 h3 h4 h5 h6 <;>
    simp only [Sum.inr.injEq, Subtype.mk.injEq, Prod.mk.injEq]
      at h <;>
    simp only [Fin.lt_def] at * <;> omega

private lemma continuous_entryCoord {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    Continuous (entryCoord (N := N) e) := by
  rcases e with i | p
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply p).comp continuous_snd

private lemma continuous_symOfEntries_apply {N : ℕ} (a b : Fin N) :
    Continuous fun ω : Entries N => symOfEntries ω a b := by
  simp_rw [symOfEntries_eq_entryCoord]
  exact continuous_entryCoord _

private lemma measurePreserving_entryCoord {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    (e : Fin N ⊕ OffDiag N) :
    MeasurePreserving (entryCoord e) L.law (Sum.elim L.diag L.off e) := by
  have := hL.diag
  have := hL.off
  rcases e with i | p
  · exact (measurePreserving_eval (fun i => L.diag i) i).comp
      (measurePreserving_fst (μ := Measure.pi L.diag) (ν := Measure.pi L.off))
  · exact (measurePreserving_eval (fun p => L.off p) p).comp
      (measurePreserving_snd (μ := Measure.pi L.diag) (ν := Measure.pi L.off))

/-- Almost surely every entry of `symOfEntries ω` is at most `q⁻¹`. -/
private lemma ae_abs_symOfEntries_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q : ℝ}
    (hs : L.BoundedSupportAS q) : ∀ᵐ ω ∂L.law, ∀ a b, |symOfEntries ω a b| ≤ q⁻¹ := by
  have he : ∀ e : Fin N ⊕ OffDiag N, ∀ᵐ ω ∂L.law, |entryCoord e ω| ≤ q⁻¹ := by
    intro e
    have hT : MeasurableSet {x : ℝ | q⁻¹ < |x|} :=
      measurableSet_lt measurable_const measurable_abs
    have h0 : Sum.elim L.diag L.off e {x : ℝ | q⁻¹ < |x|} = 0 := by
      rcases e with i | p
      · exact hs.1 i
      · exact hs.2 p
    rw [ae_iff]
    simp only [not_le]
    exact ((measurePreserving_entryCoord hL e).measure_preimage hT.nullMeasurableSet).trans h0
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  simp_rw [symOfEntries_eq_entryCoord]
  exact he _

/-- Mean and variance of an off-diagonal entry. -/
private lemma integral_symOfEntries_off {N : ℕ} {L : EntryLaws N} {C1 : ℝ} (hL : L.MomentCond C1)
    {a b : Fin N} (hab : a ≠ b) :
    ∫ ω, symOfEntries ω a b ∂L.law = 0 ∧ ∫ ω, symOfEntries ω a b ^ 2 ∂L.law = (N : ℝ)⁻¹ := by
  have hmp := measurePreserving_entryCoord hL.isProb (entryOf a b)
  have hoff : ∃ p : OffDiag N, entryOf a b = Sum.inr p := by
    unfold entryOf
    by_cases h : a < b
    · exact ⟨⟨(a, b), h⟩, by simp [h]⟩
    · by_cases h' : b < a
      · exact ⟨⟨(b, a), h'⟩, by simp [h, h']⟩
      · exact absurd (le_antisymm (not_lt.mp h') (not_lt.mp h)) hab
  obtain ⟨p, hp⟩ := hoff
  simp_rw [symOfEntries_eq_entryCoord]
  have key : ∀ g : ℝ → ℝ, Continuous g →
      ∫ ω, g (entryCoord (entryOf a b) ω) ∂L.law = ∫ x, g x ∂(L.off p) := by
    intro g hg
    rw [← integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable, hmp.map_eq, hp]
    rfl
  exact ⟨(key (fun x => x) continuous_id).trans (hL.mean_off p),
    (key (fun x => x ^ 2) (continuous_pow 2)).trans (hL.var_off p)⟩

/-- `E|Σ_{k∈U} c_k h_rk|² = N⁻¹ Σ_{k∈U} |c_k|²` for `r ∉ U`. -/
private lemma integral_norm_sq_row {N : ℕ} {L : EntryLaws N} {C1 q : ℝ} (hL : L.MomentCond C1)
    (hs : L.BoundedSupportAS q) (r : Fin N) (U : Finset (Fin N)) (hU : r ∉ U) (c : Fin N → ℂ) :
    ∫ ω, ‖∑ k ∈ U, c k * (symOfEntries ω r k : ℂ)‖ ^ 2 ∂L.law = (∑ k ∈ U, ‖c k‖ ^ 2) / N := by
  have := isProbabilityMeasure_law hL.isProb
  have hae := ae_abs_symOfEntries_le hL.isProb hs
  have hne : ∀ k ∈ U, k ≠ r := by
    rintro k hk rfl
    exact hU hk
  rw [integral_norm_sq_sum_mul U (fun k ω => symOfEntries ω r k) c (M := q⁻¹)
    (fun k => (continuous_symOfEntries_apply r k).measurable)
    (fun k => by filter_upwards [hae] with ω h using h r k) ?_ ?_, Finset.sum_div]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [(integral_symOfEntries_off hL (hne k hk).symm).2, div_eq_mul_inv]
  · intro k hk l hl hkl
    have h := (iIndepFun_entryCoord hL.isProb).indepFun
      (fun e => hkl (entryOf_inj (hne k hk) (hne l hl) e))
    simp_rw [symOfEntries_eq_entryCoord]
    exact h
  · intro k hk
    exact (integral_symOfEntries_off hL (hne k hk).symm).1

private lemma symOfEntries_rowsMix_of_mem {N : ℕ} {T : Finset (Fin N)} {r : Fin N} (hr : r ∈ T)
    (ω ω' : Entries N) (k : Fin N) :
    symOfEntries (rowsMix T ω ω') r k = symOfEntries ω' r k := by
  rw [symOfEntries_eq_entryCoord, symOfEntries_eq_entryCoord]
  unfold entryOf
  split_ifs with h1 h2 <;> simp [entryCoord, rowsMix, hr]

private lemma symOfEntries_comm {N : ℕ} (ω : Entries N) (a b : Fin N) :
    symOfEntries ω a b = symOfEntries ω b a := by
  have h := (symOfEntries_isHermitian ω).apply a b
  simp only [star_trivial] at h
  exact h.symm

private lemma continuous_zeroEntries' {N : ℕ} (T : Finset (Fin N)) :
    Continuous (zeroEntries (N := N) T) := by
  unfold zeroEntries rowsMix
  refine Continuous.prodMk (continuous_pi fun k => ?_) (continuous_pi fun p => ?_)
  · by_cases h : k ∈ T
    · simp only [h, ↓reduceIte]
      exact continuous_const
    · simp only [h, ↓reduceIte]
      exact (continuous_apply k).comp continuous_fst
  · by_cases h : p.1.1 ∈ T ∨ p.1.2 ∈ T
    · simp only [h, ↓reduceIte]
      exact continuous_const
    · simp only [h, ↓reduceIte]
      exact (continuous_apply p).comp continuous_snd

private lemma continuous_resolventC_zeroRC {N : ℕ} {z : ℂ} (hz : z.im ≠ 0) (T : Finset (Fin N))
    (k l : Fin N) :
    Continuous fun ω : Entries N => resolventC (zeroRC T (symOfEntries ω)) z k l := by
  simp_rw [← symOfEntries_zeroEntries]
  exact (continuous_resolventC_symOfEntries hz k l).comp (continuous_zeroEntries' T)

/-- `η > 10`: the Schur complement (3.13) of [15] gives `E|G_ij|² ≤ 3/(N η⁴)`. -/
private theorem offDiag_sq_le_largeEta {C1 φs : ℝ} {N : ℕ} {L : EntryLaws N}
    (hL : SmallQClass C1 φs N L) {z : ℂ} (hz : 10 < z.im) {i j : Fin N} (hij : i ≠ j) :
    ∫ ω, ‖resolventC (symOfEntries ω) z i j‖ ^ 2 ∂L.law ≤ 3 / (N * z.im ^ 4) := by
  have hz0 : 0 < z.im := by linarith
  have hP := hL.1.isProb
  have := isProbabilityMeasure_law hP
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Fin.pos i)
  set M : ℝ := ((N : ℝ) ^ φs)⁻¹ with hM
  have hM0 : 0 ≤ M := (inv_pos.2 (Real.rpow_pos_of_pos hN0 _)).le
  have hae := ae_abs_symOfEntries_le hP hL.2
  set U : Finset (Fin N) := Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j) with hU
  have hiU : i ∉ U := by simp [hU]
  have hjU : j ∉ U := by simp [hU]
  have hUc : (U.card : ℝ) ≤ N := by
    have : U.card ≤ N := (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  set B : Entries N → Fin N → Fin N → ℂ :=
    fun ω => resolventC (zeroRC {i, j} (symOfEntries ω)) z with hB
  set Y : Fin N → Entries N → ℂ :=
    fun k ω => ∑ l ∈ U, B ω k l * (symOfEntries ω j l : ℂ) with hY
  set S : Entries N → ℂ := fun ω => ∑ k ∈ U, Y k ω * (symOfEntries ω i k : ℂ) with hS
  have hBn : ∀ ω k l, ‖B ω k l‖ ≤ 1 / z.im := fun ω k l =>
    norm_resolventC_apply_le (zeroRC_isHermitian (symOfEntries_isHermitian ω) _) hz0 k l
  -- the Schur complement formula
  have hschur : ∀ ω, resolventC (symOfEntries ω) z i j =
      -resolventC (symOfEntries ω) z i i * resolventC (zeroRC {i} (symOfEntries ω)) z j j *
        ((symOfEntries ω i j : ℂ) - S ω) := by
    intro ω
    rw [resolventC_offDiag_eq (symOfEntries_isHermitian ω) hz0 hij]
    congr 2
    have h1 : S ω = ∑ k ∈ U, ∑ l ∈ U,
        (symOfEntries ω i k : ℂ) * B ω k l * symOfEntries ω l j := by
      simp only [hS, hY, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [symOfEntries_comm ω j l]
      ring
    rw [h1, hU, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_filter]
    split_ifs with hk
    · refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)
    · refine Finset.sum_eq_zero fun l _ => ?_
      simp only [show k = i ∨ k = j ∨ l = i ∨ l = j by tauto, ↓reduceIte]
  -- the pointwise bound
  have hpt : ∀ ω, ‖resolventC (symOfEntries ω) z i j‖ ^ 2 ≤
      (1 / z.im) ^ 4 * (2 * symOfEntries ω i j ^ 2 + 2 * ‖S ω‖ ^ 2) := by
    intro ω
    have ha := norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz0 i i
    have hb := norm_resolventC_apply_le
      (zeroRC_isHermitian (symOfEntries_isHermitian ω) {i}) hz0 j j
    have hc : ‖(symOfEntries ω i j : ℂ) - S ω‖ ≤ |symOfEntries ω i j| + ‖S ω‖ :=
      (norm_sub_le _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs])
    rw [hschur ω, norm_mul, norm_mul, norm_neg]
    have hη : 0 ≤ 1 / z.im := by positivity
    calc (‖resolventC (symOfEntries ω) z i i‖ * ‖resolventC (zeroRC {i} (symOfEntries ω)) z j j‖ *
          ‖(symOfEntries ω i j : ℂ) - S ω‖) ^ 2
        ≤ (1 / z.im * (1 / z.im) * (|symOfEntries ω i j| + ‖S ω‖)) ^ 2 := by
          gcongr
      _ = (1 / z.im) ^ 4 * (|symOfEntries ω i j| + ‖S ω‖) ^ 2 := by ring
      _ ≤ (1 / z.im) ^ 4 * (2 * symOfEntries ω i j ^ 2 + 2 * ‖S ω‖ ^ 2) := by
          gcongr
          nlinarith [sq_abs (symOfEntries ω i j), sq_nonneg (|symOfEntries ω i j| - ‖S ω‖)]
  -- continuity and almost sure bounds
  have hcB : ∀ k l, Continuous fun ω => B ω k l := fun k l =>
    continuous_resolventC_zeroRC hz0.ne' _ k l
  have hcY : ∀ k, Continuous (Y k) := fun k =>
    continuous_finsetSum _ fun l _ =>
      (hcB k l).mul (Complex.continuous_ofReal.comp (continuous_symOfEntries_apply j l))
  have hcS : Continuous S :=
    continuous_finsetSum _ fun k _ =>
      (hcY k).mul (Complex.continuous_ofReal.comp (continuous_symOfEntries_apply i k))
  have hYb : ∀ᵐ ω ∂L.law, ∀ k, ‖Y k ω‖ ≤ N * (1 / z.im * M) := by
    filter_upwards [hae] with ω hω k
    calc ‖Y k ω‖ ≤ ∑ l ∈ U, ‖B ω k l * (symOfEntries ω j l : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ U, 1 / z.im * M := Finset.sum_le_sum fun l _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul (hBn ω k l) (hω j l) (abs_nonneg _) (by positivity)
      _ = U.card * (1 / z.im * M) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (1 / z.im * M) := by gcongr
  have hSb : ∀ᵐ ω ∂L.law, ‖S ω‖ ≤ N * (N * (1 / z.im * M) * M) := by
    filter_upwards [hae, hYb] with ω hω hY'
    calc ‖S ω‖ ≤ ∑ k ∈ U, ‖Y k ω * (symOfEntries ω i k : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ U, N * (1 / z.im * M) * M := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul (hY' k) (hω i k) (abs_nonneg _) (by positivity)
      _ = U.card * (N * (1 / z.im * M) * M) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (N * (1 / z.im * M) * M) := by gcongr
  have hsqb : ∀ {f : Entries N → ℂ} {K : ℝ}, Continuous f → (∀ᵐ ω ∂L.law, ‖f ω‖ ≤ K) →
      Integrable (fun ω => ‖f ω‖ ^ 2) L.law := by
    intro f K hf hK
    refine Integrable.of_bound (hf.norm.pow 2).aestronglyMeasurable (K ^ 2) ?_
    filter_upwards [hK] with ω h
    rw [Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hIS : Integrable (fun ω => ‖S ω‖ ^ 2) L.law := hsqb hcS hSb
  have hIY : ∀ k, Integrable (fun ω => ‖Y k ω‖ ^ 2) L.law := fun k =>
    hsqb (hcY k) (hYb.mono fun ω h => h k)
  have hIB : ∀ k l, Integrable (fun ω => ‖B ω k l‖ ^ 2) L.law := fun k l =>
    hsqb (hcB k l) (Eventually.of_forall fun ω => hBn ω k l)
  have hIh : Integrable (fun ω => symOfEntries ω i j ^ 2) L.law := by
    refine Integrable.of_bound ((continuous_symOfEntries_apply i j).pow 2).aestronglyMeasurable
      (M ^ 2) ?_
    filter_upwards [hae] with ω h
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
  have hIG : Integrable (fun ω => ‖resolventC (symOfEntries ω) z i j‖ ^ 2) L.law :=
    hsqb (continuous_resolventC_symOfEntries hz0.ne' i j)
      (Eventually.of_forall fun ω => norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz0 i j)
  -- second level: `E|Y_k|² ≤ 1/(N η²)`
  have hEY : ∀ k, ∫ ω, ‖Y k ω‖ ^ 2 ∂L.law ≤ 1 / (N * z.im ^ 2) := by
    intro k
    have hre : ∀ ω, L.rowsExp {j} (fun ω => ((‖Y k ω‖ ^ 2 : ℝ) : ℂ)) ω =
        (((∑ l ∈ U, ‖B ω k l‖ ^ 2) / N : ℝ) : ℂ) := by
      intro ω
      have hY' : ∀ ω', Y k (rowsMix {j} ω ω') =
          ∑ l ∈ U, B ω k l * (symOfEntries ω' j l : ℂ) := by
        intro ω'
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [symOfEntries_rowsMix_of_mem (Finset.mem_singleton_self j)]
        congr 1
        exact rowIndep_iff_rowsMix.mp (rowIndep_resolventC_zeroRC (T := {j}) (V := {i, j})
          (by simp) z k l) ω ω'
      unfold EntryLaws.rowsExp
      simp_rw [hY']
      rw [integral_complex_ofReal, integral_norm_sq_row hL.1 hL.2 j U hjU]
    have h := integral_rowsExp hP {j} (X := fun ω => ((‖Y k ω‖ ^ 2 : ℝ) : ℂ)) (hIY k).ofReal
    rw [funext hre] at h
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    rw [← Complex.ofReal_injective h]
    have hpt' : ∀ ω, (∑ l ∈ U, ‖B ω k l‖ ^ 2) / N ≤ 1 / z.im ^ 2 / N := by
      intro ω
      gcongr
      calc ∑ l ∈ U, ‖B ω k l‖ ^ 2 ≤ ∑ l, ‖B ω k l‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => by positivity)
        _ = (B ω k k).im / z.im :=
            sum_norm_sq_resolventC_zeroRC (symOfEntries_isHermitian ω) _ hz0 k
        _ ≤ (1 / z.im) / z.im := by
            gcongr
            exact (Complex.im_le_norm _).trans (hBn ω k k)
        _ = 1 / z.im ^ 2 := by ring
    calc ∫ ω, (∑ l ∈ U, ‖B ω k l‖ ^ 2) / N ∂L.law ≤ ∫ _ω, 1 / z.im ^ 2 / N ∂L.law :=
          integral_mono ((integrable_finsetSum _ fun l _ => hIB k l).div_const _)
            (integrable_const _) hpt'
      _ = 1 / (N * z.im ^ 2) := by
          rw [integral_const, probReal_univ, one_smul]
          field_simp
  -- first level: `E|S|² ≤ 1/(N η²)`
  have hES : ∫ ω, ‖S ω‖ ^ 2 ∂L.law ≤ 1 / (N * z.im ^ 2) := by
    have hre : ∀ ω, L.rowsExp {i} (fun ω => ((‖S ω‖ ^ 2 : ℝ) : ℂ)) ω =
        (((∑ k ∈ U, ‖Y k ω‖ ^ 2) / N : ℝ) : ℂ) := by
      intro ω
      have hS' : ∀ ω', S (rowsMix {i} ω ω') = ∑ k ∈ U, Y k ω * (symOfEntries ω' i k : ℂ) := by
        intro ω'
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [symOfEntries_rowsMix_of_mem (Finset.mem_singleton_self i)]
        congr 1
        refine Finset.sum_congr rfl fun l hl => ?_
        have hli : l ≠ i := by
          rintro rfl
          exact hiU hl
        congr 1
        · exact rowIndep_iff_rowsMix.mp (rowIndep_resolventC_zeroRC (T := {i}) (V := {i, j})
            (by simp) z k l) ω ω'
        · rw [rowIndep_iff_rowsMix.mp (rowIndep_symOfEntries_apply (T := {i})
            (by simpa using hij.symm) (by simpa using hli)) ω ω']
      unfold EntryLaws.rowsExp
      simp_rw [hS']
      rw [integral_complex_ofReal, integral_norm_sq_row hL.1 hL.2 i U hiU]
    have h := integral_rowsExp hP {i} (X := fun ω => ((‖S ω‖ ^ 2 : ℝ) : ℂ)) hIS.ofReal
    rw [funext hre] at h
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    rw [← Complex.ofReal_injective h, integral_div, integral_finsetSum _ fun k _ => hIY k]
    calc (∑ k ∈ U, ∫ ω, ‖Y k ω‖ ^ 2 ∂L.law) / N ≤ (∑ _k ∈ U, 1 / (N * z.im ^ 2)) / N := by
          gcongr with k hk
          exact hEY k
      _ = U.card * (1 / (N * z.im ^ 2)) / N := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (1 / (N * z.im ^ 2)) / N := by gcongr
      _ = 1 / (N * z.im ^ 2) := by field_simp
  have hvar := (integral_symOfEntries_off hL.1 hij).2
  have hη2 : 2 / z.im ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  calc ∫ ω, ‖resolventC (symOfEntries ω) z i j‖ ^ 2 ∂L.law
      ≤ ∫ ω, (1 / z.im) ^ 4 * (2 * symOfEntries ω i j ^ 2 + 2 * ‖S ω‖ ^ 2) ∂L.law :=
        integral_mono hIG (((hIh.const_mul 2).add (hIS.const_mul 2)).const_mul _) hpt
    _ = (1 / z.im) ^ 4 * (2 * ∫ ω, symOfEntries ω i j ^ 2 ∂L.law +
          2 * ∫ ω, ‖S ω‖ ^ 2 ∂L.law) := by
        rw [integral_const_mul, integral_add (hIh.const_mul 2) (hIS.const_mul 2),
          integral_const_mul, integral_const_mul]
    _ ≤ (1 / z.im) ^ 4 * (2 * (N : ℝ)⁻¹ + 2 * (1 / (N * z.im ^ 2))) := by
        rw [hvar]
        gcongr
    _ = (2 + 2 / z.im ^ 2) / (N * z.im ^ 4) := by
        field_simp
    _ ≤ 3 / (N * z.im ^ 4) := by
        gcongr
        linarith

/-! ### Lemma 3.8 -/

/-- `(log N)³ ≤ φ` and `L ≤ log N` for all large `N`. -/
private lemma log_cube_le_phi (L : ℝ) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ 3 ≤ phi N ∧ L ≤ Real.log N ∧ 1 ≤ Real.log N := by
  have h1 := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 := Real.tendsto_log_atTop.comp h1
  filter_upwards [h1.eventually_ge_atTop (max L 1), h2.eventually_ge_atTop 3] with N hL h3
  simp only [Function.comp] at hL h3
  have hl1 : 1 ≤ Real.log N := (le_max_right _ _).trans hL
  refine ⟨?_, (le_max_left _ _).trans hL, hl1⟩
  unfold phi
  calc Real.log N ^ 3 = Real.log N ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast _ 3).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hl1 (by exact_mod_cast h3)

/-- `3/(Nη⁴) ≤ Im m/(Nη)` for `η > 10` when `Im m ≥ η/(49 + η²)`. -/
private lemma largeEta_le_ratio {N η m : ℝ} (hN : 0 < N) (hη : 10 < η) (h1 : η / (49 + η ^ 2) ≤ m) :
    3 / (N * η ^ 4) ≤ m / (N * η) := by
  have hη0 : 0 < η := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hη2 : (100 : ℝ) ≤ η ^ 2 := by nlinarith only [hη]
  have h3 : 3 * (49 + η ^ 2) ≤ η ^ 4 := by
    have : η ^ 4 = η ^ 2 * η ^ 2 := by ring
    rw [this]; nlinarith only [hη2]
  have h5 : η ≤ m * (49 + η ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at h1; linarith only [h1]
  have hm : 0 ≤ m := le_trans (by positivity) h1
  calc 3 * (N * η) ≤ 3 * N * (m * (49 + η ^ 2)) := by rw [← mul_assoc]; gcongr
    _ = N * m * (3 * (49 + η ^ 2)) := by ring
    _ ≤ N * m * η ^ 4 := by gcongr
    _ = m * (N * η ^ 4) := by ring

/-- The bad-event term: `298 N (N+1)^S N^A e^{-c φ} ≤ 1` once `7 + 2S + |A| ≤ c log N`,
`1 ≤ log N` and `(log N)³ ≤ φ`. -/
private lemma badEvent_le_one {N : ℕ} (hN : 2 ≤ N) {S : ℕ} {A c ϕ : ℝ} (hc : 0 < c)
    (hX : 7 + 2 * S + |A| ≤ c * Real.log N) (hl1 : 1 ≤ Real.log N)
    (hϕ : Real.log N ^ 3 ≤ ϕ) :
    298 * (N : ℝ) * ((N : ℝ) + 1) ^ S * ((N : ℝ) ^ A * Real.exp (-c * ϕ)) ≤ 1 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0r : (0 : ℝ) < N := by linarith
  have hN1 : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by nlinarith only [hNr]
  have hexpN : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hN0r).symm
  have h298 : (298 : ℝ) ≤ Real.exp 6 := by
    have h1 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    rw [h1]
    calc (298 : ℝ) ≤ 2.7 ^ 6 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 6
  have hpow : ((N : ℝ) + 1) ^ S ≤ Real.exp (2 * S * Real.log N) := by
    calc ((N : ℝ) + 1) ^ S ≤ ((N : ℝ) ^ 2) ^ S := pow_le_pow_left₀ (by positivity) hN1 S
      _ = Real.exp (2 * S * Real.log N) := by
        rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hN0r]
        push_cast; ring_nf
  have hrp : (N : ℝ) ^ A ≤ Real.exp (|A| * Real.log N) := by
    rw [Real.rpow_def_of_pos hN0r]
    have hl0 : 0 ≤ Real.log N := by linarith
    exact Real.exp_le_exp.2 (by nlinarith only [le_abs_self A, hl0])
  have hlhs : 298 * (N : ℝ) * ((N : ℝ) + 1) ^ S * ((N : ℝ) ^ A * Real.exp (-c * ϕ)) ≤
      Real.exp (6 + Real.log N + 2 * S * Real.log N + |A| * Real.log N + (-c * ϕ)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, ← hexpN]
    calc 298 * (N : ℝ) * ((N : ℝ) + 1) ^ S * ((N : ℝ) ^ A * Real.exp (-c * ϕ))
        ≤ Real.exp 6 * (N : ℝ) * Real.exp (2 * S * Real.log N) *
          (Real.exp (|A| * Real.log N) * Real.exp (-c * ϕ)) := by gcongr
      _ = _ := by ring
  refine hlhs.trans (Real.exp_le_one_iff.2 ?_)
  have hl0 : 0 ≤ Real.log N := by linarith
  have h2 : Real.log N ≤ Real.log N ^ 2 := by nlinarith only [hl1]
  have h3 : Real.log N ^ 2 * Real.log N = Real.log N ^ 3 := by ring
  have h4 : (7 + 2 * S + |A|) * Real.log N ≤ c * Real.log N ^ 3 := by
    calc (7 + 2 * S + |A|) * Real.log N ≤ c * Real.log N * Real.log N :=
          mul_le_mul_of_nonneg_right hX hl0
      _ ≤ c * (Real.log N ^ 2 * Real.log N) := by
          rw [mul_assoc]; gcongr
      _ = _ := by rw [h3]
  have h5 : c * Real.log N ^ 3 ≤ c * ϕ := mul_le_mul_of_nonneg_left hϕ hc.le
  have hA : 0 ≤ |A| := abs_nonneg _
  nlinarith only [h4, h5, hl1, hA, hl0]

/-- `a ℓ² + b ≤ φ` from `a + b ≤ ℓ`, `1 ≤ ℓ`, `ℓ³ ≤ φ`. -/
private lemma le_phi_of_log {ℓ ϕ a b : ℝ} (h1 : 1 ≤ ℓ) (hb : 0 ≤ b)
    (hℓ : a + b ≤ ℓ) (hϕ : ℓ ^ 3 ≤ ϕ) : a * ℓ ^ 2 + b ≤ ϕ := by
  have h2 : 1 ≤ ℓ ^ 2 := one_le_pow₀ h1
  have h3 : ℓ ^ 2 * (a + b) ≤ ℓ ^ 2 * ℓ := mul_le_mul_of_nonneg_left hℓ (by positivity)
  have h4 : ℓ ^ 2 * ℓ = ℓ ^ 3 := by ring
  nlinarith only [h2, h3, h4, hb, hϕ]

/-- `ε ≤ 1` and `ε² ≤ 3 p² (u² + v² + w²)` for `ε = p (u + v + w)` with `p ≤ N^{c/4}`,
`u, v, w ≤ N^{-c/2}` and `3 ≤ N^{c/4}`. -/
private lemma entryErr_le_one {N p u v w c : ℝ} (hN : 0 < N) (hp0 : 0 ≤ p) (hp : p ≤ N ^ (c / 4))
    (hu' : u ≤ N ^ (-(c / 2))) (hv' : v ≤ N ^ (-(c / 2))) (hw' : w ≤ N ^ (-(c / 2)))
    (h3 : 3 ≤ N ^ (c / 4)) :
    p * (u + v + w) ≤ 1 ∧ (p * (u + v + w)) ^ 2 ≤ 3 * p ^ 2 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  constructor
  · have h1 : p * N ^ (-(c / 2)) ≤ N ^ (-(c / 4)) := by
      calc p * N ^ (-(c / 2)) ≤ N ^ (c / 4) * N ^ (-(c / 2)) :=
            mul_le_mul_of_nonneg_right hp (by positivity)
        _ = N ^ (-(c / 4)) := by rw [← Real.rpow_add hN]; ring_nf
    have h2 : 3 * N ^ (-(c / 4)) ≤ 1 := by
      have h3' : N ^ (c / 4) * N ^ (-(c / 4)) = 1 := by
        rw [← Real.rpow_add hN]; simp
      have : 0 < N ^ (-(c / 4)) := by positivity
      nlinarith only [h3, h3', this]
    calc p * (u + v + w) ≤ p * (3 * N ^ (-(c / 2))) := by
          gcongr; linarith only [hu', hv', hw']
      _ = 3 * (p * N ^ (-(c / 2))) := by ring
      _ ≤ 3 * N ^ (-(c / 4)) := by linarith only [h1]
      _ ≤ 1 := h2
  · have h2 : (u + v + w) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
      nlinarith only [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (u - w)]
    calc (p * (u + v + w)) ^ 2 = p ^ 2 * (u + v + w) ^ 2 := by ring
      _ ≤ p ^ 2 * (3 * (u ^ 2 + v ^ 2 + w ^ 2)) := by gcongr
      _ = _ := by ring

/-- Lemma 3.8 (3.15) for every `η ≥ N^{-1+c}` (the range `η > 10` by the
Schur-complement bound). -/
theorem offDiag_sq_le_smallQ {C1 φs c : ℝ} (hφs : 0 < φs) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, SmallQClass C1 φs N L →
      ∀ z : ℂ, |z.re| ≤ 5 → (N : ℝ) ^ (-1 + c) ≤ z.im → ∀ i j : Fin N, i ≠ j →
        ∫ ω, ‖resolventC (symOfEntries ω) z i j‖ ^ 2 ∂L.law ≤
          phi N ^ C * ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2) := by
  -- the argument holds for every `c > 0`; the hypothesis `c < 1` is not needed
  have _ := hc1
  set φ : ℝ := min φs (1 / 4) with hφdef
  have hφ : 0 < φ := lt_min hφs (by norm_num)
  obtain ⟨C0, hC0, N0s, hS2⟩ := comparison_iterate_sum (C1 := C1) (φq := φ) (Ks := 3) hφ
    (by norm_num)
  obtain ⟨CL, hCL, cL, hcL, CL', hCL', N0l, hloc⟩ := localLaw_isMomentMatch (C1 := C1) (φs := φs)
  obtain ⟨N0w, hW⟩ := iterWeight_sum_le (φq := φ) (ζ := 1) hφ le_rfl 2
  set n : ℕ := ⌈6 * 1 / φ⌉₊ with hn
  set ξ : ℕ := xiOf (2 * 1 + 3) φ with hξ
  set S : ℕ := 2 + n * ξ with hS
  set K : ℝ := (2 * C1 + 4) * C1 with hK
  set c' : ℝ := min c (1 / 2) with hc'
  have hc'0 : 0 < c' := lt_min hc0 (by norm_num)
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'h : c' ≤ 1 / 2 := min_le_right _ _
  set a0 : ℝ := 6 * 149 * K ^ 2 with ha0
  set b0 : ℝ := 7 + 149 * (4 * n + 1) with hb0
  set L0 : ℝ := a0 + b0 + (7 + 2 * S + |CL'|) / cL with hL0
  have hev := (eventually_ge_atTop (max (max N0s N0l) (max N0w (max 16 ⌈(8 * K) ^ 8⌉₊)))).and <|
    (phi_rpow_le_rpow (max C0 CL) (half_pos hc0)).and <|
    (phi_rpow_le_rpow CL (by positivity : (0 : ℝ) < c' / 4)).and <|
    (((tendsto_rpow_atTop (by positivity : (0 : ℝ) < c' / 4)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 3).and <|
    (log_cube_le_phi L0)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨2 * CL + 1, by positivity, N0, fun N hN L hL z hE hη i j hij => ?_⟩
  obtain ⟨hNbig, hφC, hφCL, h3c, hlog3, hlogL, hlog1⟩ := hN0 N hN
  simp only [Function.comp] at h3c
  have hNs : N0s ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNbig
  have hNl : N0l ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNbig
  have hNw : N0w ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNbig
  have hN16 : 16 ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_right _ _))) hNbig
  have hNKn : ⌈(8 * K) ^ 8⌉₊ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNbig
  have hNK : (8 * K) ^ 8 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNKn)
  have hN3 : 3 ≤ N := by omega
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0r : (0 : ℝ) < N := by linarith only [hNr]
  have hN1r : (1 : ℝ) ≤ N := by linarith only [hNr]
  have hϕ1 : 1 ≤ phi N := by
    have := log_le_phi hN16
    linarith only [this, hlog1]
  have hϕ0 : 0 < phi N := by linarith only [hϕ1]
  -- the spectral parameter
  have hηpos : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0r _) hη
  have hNη : (N : ℝ) ^ c ≤ N * z.im := by
    have : (N : ℝ) * (N : ℝ) ^ (-1 + c) = (N : ℝ) ^ c := by
      rw [← Real.rpow_one_add' hN0r.le (by linarith only [hc0])]; ring_nf
    rw [← this]
    exact mul_le_mul_of_nonneg_left hη hN0r.le
  have hNc1 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1r hc0.le
  have hNη0 : 0 < (N : ℝ) * z.im := by positivity
  have hinvη : 1 / z.im ≤ N := by
    rw [div_le_iff₀ hηpos]; linarith only [hNc1, hNη, mul_comm (N : ℝ) z.im]
  have hmsc := norm_msc_eq_inv_and_lt_one hηpos
  have hIm0 : 0 < (msc z).im := im_msc_pos hηpos
  have hIm1 : (msc z).im ≤ 1 := (Complex.im_le_norm _).trans hmsc.2.le
  set R : ℝ := (msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have hRa : (msc z).im / (N * z.im) ≤ R := le_add_of_nonneg_right (by positivity)
  have hϕC : 1 ≤ phi N ^ (2 * CL + 1) := Real.one_le_rpow hϕ1 (by positivity)
  by_cases hη10 : z.im ≤ 10
  swap
  · -- `η > 10`: the Schur complement
    replace hη10 : 10 < z.im := not_le.mp hη10
    refine (offDiag_sq_le_largeEta hL hη10 hij).trans ?_
    calc _ ≤ (msc z).im / (N * z.im) := largeEta_le_ratio hN0r hη10 (div_le_im_msc hE hηpos)
      _ ≤ R := hRa
      _ = 1 * R := (one_mul R).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hϕC hR0
  -- `η ≤ 10`: the sum form of the iteration
  obtain ⟨Lw, hw⟩ := exists_isMomentMatch hN3 hL.1
  have hmp := MatchedPair.of_smallQ hN3 hL hw
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith only [hNr])
  have hKpos : 0 < K := by
    have h1 : 0 < (2 * C1 + 4) * C1 * Real.log N :=
      (div_pos_iff_of_pos_left (Real.sqrt_pos.mpr hN0r)).1 (tilde_pos hN3 hL.1 hw)
    exact (mul_pos_iff_of_pos_right hlogN).1 h1
  set qt : ℝ := Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N) with hqt
  have hqt4 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ qt := rpow_quarter_le_tilde hN3 hKpos hNK
  have hqt0 : 0 < qt := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0r _) hqt4
  have hq : (N : ℝ) ^ φ ≤ min ((N : ℝ) ^ φs) qt :=
    le_min (Real.rpow_le_rpow_of_exponent_le hN1r (min_le_left _ _))
      ((Real.rpow_le_rpow_of_exponent_le hN1r (min_le_right _ _)).trans hqt4)
  -- `z ∈ S(C0) ∩ S(CL)`
  have hdom : ∀ C', C' ≤ max C0 CL → z ∈ specDomain N C' := by
    intro C' hC'
    refine ⟨hE, ?_, hη10⟩
    have h1 : phi N ^ C' ≤ phi N ^ (max C0 CL) := Real.rpow_le_rpow_of_exponent_le hϕ1 hC'
    have h2 : (N : ℝ) ^ (c / 2) < (N : ℝ) ^ c :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith only [hNr]) (by linarith only [hc0])
    have h3 : (N : ℝ) ^ c / N = (N : ℝ) ^ (-1 + c) := by
      rw [div_eq_iff hN0r.ne', mul_comm, ← Real.rpow_one_add' hN0r.le (by linarith only [hc0])]
      ring_nf
    calc phi N ^ C' / N < (N : ℝ) ^ c / N :=
          div_lt_div_of_pos_right (lt_of_le_of_lt (h1.trans hφC) h2) hN0r
      _ = _ := h3
      _ ≤ _ := hη
  have hz0 := hdom C0 (le_max_left _ _)
  have hzL := hdom CL (le_max_right _ _)
  -- the sum form at `γ₀ = N(N+1)/2`, `ζ = 1`, `s = 2`, `F = G_ij Ḡ_ij`
  set F : FSum N := [(1, [⟨.g, i, j⟩, ⟨.gbar, i, j⟩])] with hFdef
  have hF : ∀ cw ∈ F, 0 ≤ cw.1 ∧ cw.2.length = 2 := by simp [hFdef]
  have hS2' := hS2 N hNs L Lw _ hmp hq (N * (N + 1) / 2) 1 le_rfl hϕ1 2 (by norm_num) z hz0 F hF
    (by simp [hFdef])
  rw [interp_lexPos_top, ← hξ, ← hn] at hS2'
  -- the left side is `E|G_ij|²`
  have hLHS : ∀ ω, evalF (resS z ω) (msc z) F =
      ((‖resolventC (symOfEntries ω) z i j‖ ^ 2 : ℝ) : ℂ) := by
    intro ω
    simp only [hFdef, evalF, evalWord, evalLetter, resS, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero,
      Complex.ofReal_one, one_mul]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint : ‖∫ ω, evalF (resS z ω) (msc z) F ∂L.law‖ =
      ∫ ω, ‖resolventC (symOfEntries ω) z i j‖ ^ 2 ∂L.law := by
    simp_rw [hLHS]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg fun ω => by positivity)]
  rw [hint] at hS2'
  -- the event of the local law for `H̃`
  have := isProbabilityMeasure_law hw.1
  set ε : ℝ := entryErr N CL qt z with hεdef
  set Ω : Set (Entries N) := {ω | ∀ z ∈ specDomain N CL, ∀ x y,
      ‖resS z ω x y - (if x = y then msc z else 0)‖ ≤ entryErr N CL qt z} with hΩdef
  have hΩ : ∀ ω ∈ Ω, ∀ x y, ‖resS z ω x y - (if x = y then msc z else 0)‖ ≤ ε :=
    fun ω hω x y => hω z hzL x y
  have hP := hloc N hNl L Lw hL hw
  set P : ℝ := (Lw.law Ωᶜ).toReal with hPdef
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  have hPle : P ≤ (N : ℝ) ^ CL' * Real.exp (-cL * phi N) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hP
  -- `ε ≤ 1` and `ε² ≤ 3 φ^{2CL} (1/q̃² + Im m/(Nη) + 1/(Nη)²)`
  have hNc' : 1 / (N * z.im) ≤ (N : ℝ) ^ (-c') := by
    calc 1 / (N * z.im) ≤ 1 / (N : ℝ) ^ c := one_div_le_one_div_of_le (by positivity) hNη
      _ = (N : ℝ) ^ (-c) := by rw [Real.rpow_neg hN0r.le, one_div]
      _ ≤ (N : ℝ) ^ (-c') := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith only [hc'c])
  have hsq : Real.sqrt ((msc z).im / (N * z.im)) ≤ (N : ℝ) ^ (-(c' / 2)) := by
    have h1 : (msc z).im / (N * z.im) ≤ (N : ℝ) ^ (-c') :=
      (div_le_div_of_nonneg_right hIm1 hNη0.le).trans hNc'
    calc Real.sqrt ((msc z).im / (N * z.im)) ≤ Real.sqrt ((N : ℝ) ^ (-c')) := Real.sqrt_le_sqrt h1
      _ = (N : ℝ) ^ (-(c' / 2)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0r.le]; ring_nf
  have hinvNη : 1 / (N * z.im) ≤ (N : ℝ) ^ (-(c' / 2)) :=
    hNc'.trans (Real.rpow_le_rpow_of_exponent_le hN1r (by linarith only [hc'0]))
  have hinvq : 1 / qt ≤ (N : ℝ) ^ (-(c' / 2)) := by
    calc 1 / qt ≤ 1 / (N : ℝ) ^ ((1 : ℝ) / 4) := one_div_le_one_div_of_le (by positivity) hqt4
      _ = (N : ℝ) ^ (-((1 : ℝ) / 4)) := by rw [Real.rpow_neg hN0r.le, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1r (by linarith only [hc'h])
  obtain ⟨hε1, hε2'⟩ := entryErr_le_one hN0r (by positivity) hφCL hinvq hsq hinvNη h3c
  have hεeq : ε = phi N ^ CL * (1 / qt + Real.sqrt ((msc z).im / (N * z.im)) + 1 / (N * z.im)) :=
    rfl
  rw [← hεeq] at hε1 hε2'
  have hε0 : 0 ≤ ε := by rw [hεeq]; positivity
  have hIma : 1 / (149 * N) ≤ (msc z).im / (N * z.im) := by
    have h1 := div_le_im_msc hE hηpos
    rw [div_le_div_iff₀ (by positivity) hNη0]
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : z.im * (149 : ℝ) ≤ (msc z).im * (49 + z.im ^ 2) * 149 :=
      mul_le_mul_of_nonneg_right h1 (by norm_num)
    have h3 : (msc z).im * (49 + z.im ^ 2) ≤ (msc z).im * 149 := by
      have : z.im ^ 2 ≤ 100 := by nlinarith only [hη10, hηpos]
      nlinarith only [this, hIm0]
    nlinarith only [h1, h3, hN0r, hηpos]
  have hinvN : 1 / (N : ℝ) ≤ 149 * R := by
    have := hIma.trans hRa
    rw [div_le_iff₀ (by positivity)] at this
    rw [div_le_iff₀ hN0r]
    linarith only [this]
  have hq2 : (1 / qt) ^ 2 = K ^ 2 * Real.log N ^ 2 / N := by
    rw [hqt, one_div_div, div_pow, Real.sq_sqrt hN0r.le, mul_pow]
  have hε2 : ε ^ 2 ≤ 3 * phi N ^ (2 * CL) * ((149 * K ^ 2 * Real.log N ^ 2 + 1) * R) := by
    have hϕsq : (phi N ^ CL) ^ 2 = phi N ^ (2 * CL) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hϕ0.le]; ring_nf
    have hs2 : Real.sqrt ((msc z).im / (N * z.im)) ^ 2 = (msc z).im / (N * z.im) :=
      Real.sq_sqrt (by positivity)
    have h3 : (1 / qt) ^ 2 ≤ 149 * K ^ 2 * Real.log N ^ 2 * R := by
      rw [hq2]
      have hk : 0 ≤ K ^ 2 * Real.log N ^ 2 := by positivity
      calc K ^ 2 * Real.log N ^ 2 / N = K ^ 2 * Real.log N ^ 2 * (1 / N) := by ring
        _ ≤ K ^ 2 * Real.log N ^ 2 * (149 * R) := mul_le_mul_of_nonneg_left hinvN hk
        _ = _ := by ring
    have h4 : Real.sqrt ((msc z).im / (N * z.im)) ^ 2 + (1 / (N * z.im)) ^ 2 ≤ R := by
      rw [hs2, hR, div_pow, one_pow]
    rw [hϕsq] at hε2'
    have hϕ2 : 0 ≤ phi N ^ (2 * CL) := by positivity
    calc ε ^ 2 ≤ 3 * phi N ^ (2 * CL) * ((1 / qt) ^ 2 +
          Real.sqrt ((msc z).im / (N * z.im)) ^ 2 + (1 / (N * z.im)) ^ 2) := hε2'
      _ ≤ 3 * phi N ^ (2 * CL) * (149 * K ^ 2 * Real.log N ^ 2 * R + R) := by
          exact mul_le_mul_of_nonneg_left (by linarith only [h3, h4]) (by positivity)
      _ = _ := by ring
  -- each term of the sum
  have hterm : ∀ d ∈ iterAdmSet N ξ 2 n,
      iterWeight N φ d * ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖ ≤
        iterWeight N φ d * 4 ^ (d.map fun x => x.2.sum).sum * (ε ^ 2 + (N + 1) ^ S * P) +
        (if touchesData i j d then iterWeight N φ d * 4 ^ (d.map fun x => x.2.sum).sum * 4
          else 0) := by
    intro d hd
    have hw0 : 0 ≤ iterWeight N φ d := by
      unfold iterWeight
      refine List.prod_nonneg fun x hx => ?_
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      have : 0 ≤ entryWeight N y.1 := by cases y.1 <;> simp [entryWeight]
      positivity
    obtain ⟨hdn, hda⟩ := (mem_iterAdmSet n 2 d).1 hd
    have h1 := norm_integral_evalF_iterP_le (μ := Lw.law) hηpos hij hε0 hε1 Ω hΩ hdn hda
    have h2 : (1 / z.im + 1) ^ (2 + n * ξ) ≤ ((N : ℝ) + 1) ^ S := by
      rw [hS]; gcongr
    set Y : ℝ := 4 ^ (d.map fun x => x.2.sum).sum with hY
    have h4 : (0 : ℝ) ≤ Y := by positivity
    have h5 : (1 / z.im + 1) ^ (2 + n * ξ) * P ≤ ((N : ℝ) + 1) ^ S * P :=
      mul_le_mul_of_nonneg_right h2 hP0
    have hP' : (Lw.law Ωᶜ).toReal = P := rfl
    rw [hP'] at h1
    have hwY : 0 ≤ iterWeight N φ d * Y := mul_nonneg hw0 h4
    have hε2n : 0 ≤ ε ^ 2 := sq_nonneg ε
    split_ifs with ht
    · rw [ht] at h1
      simp only [↓reduceIte] at h1
      calc _ ≤ iterWeight N φ d * (Y * (4 + (1 / z.im + 1) ^ (2 + n * ξ) * P)) :=
            mul_le_mul_of_nonneg_left h1 hw0
        _ = iterWeight N φ d * Y * ((1 / z.im + 1) ^ (2 + n * ξ) * P) +
            iterWeight N φ d * Y * 4 := by ring
        _ ≤ iterWeight N φ d * Y * (ε ^ 2 + (N + 1) ^ S * P) + iterWeight N φ d * Y * 4 := by
            gcongr; linarith only [h5, hε2n]
    · simp only [Bool.not_eq_true] at ht
      rw [ht] at h1
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      rw [add_zero]
      calc _ ≤ iterWeight N φ d * (Y * (ε ^ 2 + (1 / z.im + 1) ^ (2 + n * ξ) * P)) :=
            mul_le_mul_of_nonneg_left h1 hw0
        _ = iterWeight N φ d * Y * (ε ^ 2 + (1 / z.im + 1) ^ (2 + n * ξ) * P) := by ring
        _ ≤ _ := by gcongr
  obtain ⟨hW1, hW2⟩ := hW N hNw i j
  have hX : 0 ≤ ε ^ 2 + (N + 1) ^ S * P := by positivity
  have hsum : ∑ d ∈ iterAdmSet N ξ 2 n,
      iterWeight N φ d * ‖∫ ω, evalF (resS z ω) (msc z) (iterP d F) ∂Lw.law‖ ≤
        2 * (ε ^ 2 + (N + 1) ^ S * P) + 4 * ((n : ℝ) / N) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_filter, ← Finset.sum_mul]
    have h1 := mul_le_mul_of_nonneg_right hW1 hX
    have h2 := mul_le_mul_of_nonneg_right hW2 (by norm_num : (0 : ℝ) ≤ 4)
    linarith only [h1, h2]
  -- the final count
  have hlogge : (7 + 2 * S + |CL'|) / cL ≤ Real.log N := by
    have : 0 ≤ a0 + b0 := by positivity
    linarith only [hlogL, this]
  have hB := badEvent_le_one (by omega : 2 ≤ N) (S := S) (A := CL') hcL
    (by rw [div_le_iff₀ hcL] at hlogge; linarith only [hlogge]) hlog1 hlog3
  have hϕbig : a0 * Real.log N ^ 2 + b0 ≤ phi N := by
    refine le_phi_of_log hlog1 (by positivity) ?_ hlog3
    have : 0 ≤ (7 + 2 * S + |CL'|) / cL := by positivity
    linarith only [hlogL, this]
  have hNinv : (N : ℝ) ^ (-(1 : ℝ)) ≤ 149 * R := by
    rw [Real.rpow_neg_one, inv_eq_one_div]; exact hinvN
  have hnN : 4 * ((n : ℝ) / N) ≤ 149 * (4 * n) * R := by
    have : 4 * ((n : ℝ) / N) = 4 * n * (1 / N) := by ring
    rw [this]
    have hn0 : (0 : ℝ) ≤ 4 * n := by positivity
    calc 4 * (n : ℝ) * (1 / N) ≤ 4 * n * (149 * R) := mul_le_mul_of_nonneg_left hinvN hn0
      _ = _ := by ring
  have hBR : 2 * (((N : ℝ) + 1) ^ S * P) ≤ R := by
    have h1 : 2 * (((N : ℝ) + 1) ^ S * P) ≤
        2 * (((N : ℝ) + 1) ^ S * ((N : ℝ) ^ CL' * Real.exp (-cL * phi N))) := by
      gcongr
    have h2 : 1 / (149 * (N : ℝ)) ≤ R := hIma.trans hRa
    have h3 : 2 * (((N : ℝ) + 1) ^ S * ((N : ℝ) ^ CL' * Real.exp (-cL * phi N))) ≤
        1 / (149 * N) := by
      rw [le_div_iff₀ (by positivity)]
      calc 2 * (((N : ℝ) + 1) ^ S * ((N : ℝ) ^ CL' * Real.exp (-cL * phi N))) * (149 * N)
          = 298 * (N : ℝ) * ((N : ℝ) + 1) ^ S * ((N : ℝ) ^ CL' * Real.exp (-cL * phi N)) := by
            ring
        _ ≤ 1 := hB
    linarith only [h1, h2, h3]
  have hϕ2CL : 1 ≤ phi N ^ (2 * CL) := Real.one_le_rpow hϕ1 (by positivity)
  have hsplit : phi N ^ (2 * CL + 1) = phi N ^ (2 * CL) * phi N := by
    rw [Real.rpow_add hϕ0, Real.rpow_one]
  have hY : 0 ≤ (1 + 149 * (4 * (n : ℝ) + 1)) * R := by positivity
  have hY2 := mul_le_mul_of_nonneg_right hϕ2CL hY
  have hfin : (6 * (149 * K ^ 2 * Real.log N ^ 2 + 1) + 1 + 149 * (4 * n + 1)) ≤ phi N := by
    have : a0 * Real.log N ^ 2 + b0 = 6 * (149 * K ^ 2 * Real.log N ^ 2 + 1) + 1 +
        149 * (4 * n + 1) := by rw [ha0, hb0]; ring
    linarith only [hϕbig, this]
  calc ∫ ω, ‖resolventC (symOfEntries ω) z i j‖ ^ 2 ∂L.law
      ≤ 2 * (ε ^ 2 + (N + 1) ^ S * P) + 4 * ((n : ℝ) / N) + (N : ℝ) ^ (-(1 : ℝ)) :=
        hS2'.trans (by linarith only [hsum])
    _ ≤ 2 * (3 * phi N ^ (2 * CL) * ((149 * K ^ 2 * Real.log N ^ 2 + 1) * R)) + R +
        149 * (4 * n) * R + 149 * R := by linarith only [hε2, hBR, hnN, hNinv]
    _ = phi N ^ (2 * CL) * (6 * (149 * K ^ 2 * Real.log N ^ 2 + 1) * R) +
        1 * ((1 + 149 * (4 * (n : ℝ) + 1)) * R) := by ring
    _ ≤ phi N ^ (2 * CL) * (6 * (149 * K ^ 2 * Real.log N ^ 2 + 1) * R) +
        phi N ^ (2 * CL) * ((1 + 149 * (4 * (n : ℝ) + 1)) * R) := by linarith only [hY2]
    _ = phi N ^ (2 * CL) * ((6 * (149 * K ^ 2 * Real.log N ^ 2 + 1) + 1 + 149 * (4 * n + 1)) *
        R) := by ring
    _ ≤ phi N ^ (2 * CL) * (phi N * R) := by gcongr
    _ = _ := by rw [hsplit]; ring

/-! ### Compiled checks at a concrete nondegenerate point -/

/-- For all large `N` the Rademacher laws `±N^{-1/2}` (diagonal `±√2 N^{-1/2}`) lie in the class
of Theorem 3.6 with `C1 = 2` and support exponent `φs = 2/5`. -/
private lemma radLaws_smallQ :
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

/-- (3.15) at `C1 = 2`, `φs = 2/5`, `c = 1/2`, for the Rademacher laws, which lie in
`SmallQClass` for every `N ≥ N0`, at the entry `(1, 2)` and at `z = i` (`η = 1`, the comparison
range) and `z = 20i` (`η > 10`): all hypotheses of `offDiag_sq_le_smallQ` hold. -/
example : ∃ C > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∃ i j : Fin N, i ≠ j ∧
    SmallQClass 2 (2 / 5) N (radLaws N) ∧
    ∫ ω, ‖resolventC (symOfEntries ω) Complex.I i j‖ ^ 2 ∂(radLaws N).law ≤
      phi N ^ C * ((msc Complex.I).im / (N * Complex.I.im) + 1 / (N * Complex.I.im) ^ 2) ∧
    ∫ ω, ‖resolventC (symOfEntries ω) (20 * Complex.I) i j‖ ^ 2 ∂(radLaws N).law ≤
      phi N ^ C * ((msc (20 * Complex.I)).im / (N * (20 * Complex.I).im) +
        1 / (N * (20 * Complex.I).im) ^ 2) := by
  obtain ⟨C, hC, N0, h⟩ := offDiag_sq_le_smallQ (C1 := 2) (φs := 2 / 5) (c := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (radLaws_smallQ.and (eventually_ge_atTop 2))
  refine ⟨C, hC, max N0 N1, fun N hN => ?_⟩
  obtain ⟨hcl, h2⟩ := hN1 N (le_trans (le_max_right _ _) hN)
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpow : (N : ℝ) ^ (-1 + 1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1r (by norm_num)
  have hij : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  refine ⟨_, _, hij, hcl, h N hN0 _ hcl _ (by simp) (by simpa using hpow) _ _ hij,
    h N hN0 _ hcl _ (by simp) ?_ _ _ hij⟩
  simp only [Complex.mul_im, Complex.I_im, Complex.I_re, mul_zero, mul_one, add_zero]
  norm_num at hpow ⊢
  linarith

#print axioms offDiag_sq_le_smallQ

end WEdgeNS
