import WEdgeNS.Comparison.MomentCompare
import WEdgeNS.LocalLaw.Norm
import WEdgeNS.LocalLaw.OutOfSpectrum

/-!
# The norm bound for small support
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- The positivity of the support parameter of Lemma 5.1.
open private tilde_pos from WEdgeNS.Comparison.Classes

/-! ### Reflection `H ↦ -H` -/

/-- Integrals against the law of `-h`, where `h` has law `μ`. -/
private lemma nsq_integral_neg (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ x, f x ∂(μ.map (fun x => -1 * x)) = ∫ x, f (-x) ∂μ := by
  rw [integral_map (measurable_const_mul _).aemeasurable hf.aestronglyMeasurable]
  simp

private lemma nsq_integrable_neg {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hfe : ∀ x, f (-x) = f x) (h : Integrable f μ) :
    Integrable f (μ.map (fun x => -1 * x)) := by
  rw [integrable_map_measure hf.aestronglyMeasurable (measurable_const_mul _).aemeasurable]
  have e : f ∘ (fun x => -1 * x) = f := funext fun x => by simp [hfe]
  rw [e]; exact h

private lemma nsq_tail_neg (μ : Measure ℝ) (q : ℝ) :
    μ.map (fun x => -1 * x) {x | q⁻¹ < |x|} = μ {x | q⁻¹ < |x|} := by
  rw [Measure.map_apply (measurable_const_mul _)
    (measurableSet_lt measurable_const measurable_abs)]
  congr 1
  ext x
  simp

/-- The class of Theorem 3.6 is invariant under `h ↦ -h`. -/
private lemma nsq_smallQ_neg {C1 φs : ℝ} {N : ℕ} {L : EntryLaws N}
    (h : SmallQClass C1 φs N L) : SmallQClass C1 φs N (scale (-1) L) := by
  obtain ⟨hM, hS⟩ := h
  have := hM.isProb.diag; have := hM.isProb.off
  refine ⟨⟨⟨fun i => ?_, fun p => ?_⟩, fun i => ?_, fun p => ?_, fun i => ?_, fun p => ?_,
    fun i => ?_, fun p => ?_, fun p => ?_, fun p => ?_⟩, ⟨fun i => ?_, fun p => ?_⟩⟩
  · simp only [scale]; infer_instance
  · simp only [scale]; infer_instance
  · exact nsq_integrable_neg (continuous_pow 2) (fun x => by ring) (hM.sq_int_diag i)
  · exact nsq_integrable_neg (continuous_pow 4) (fun x => by ring) (hM.fourth_int_off p)
  · simp only [scale]
    rw [nsq_integral_neg _ (fun x => x) continuous_id]
    rw [integral_neg, hM.mean_diag i, neg_zero]
  · simp only [scale]
    rw [nsq_integral_neg _ (fun x => x) continuous_id]
    rw [integral_neg, hM.mean_off p, neg_zero]
  · simp only [scale]
    rw [nsq_integral_neg _ _ (continuous_pow 2)]
    simpa using hM.var_diag_le i
  · simp only [scale]
    rw [nsq_integral_neg _ _ (continuous_pow 2)]
    simpa using hM.var_off p
  · simp only [scale]
    rw [nsq_integral_neg _ (fun x => |x| ^ 3) (continuous_abs.pow 3)]
    simpa using hM.third_off_le p
  · simp only [scale]
    rw [nsq_integral_neg _ _ (continuous_pow 4)]
    simpa [Even.neg_pow (by decide : Even 4)] using hM.fourth_off_le p
  · simp only [scale]; rw [nsq_tail_neg]; exact hS.1 i
  · simp only [scale]; rw [nsq_tail_neg]; exact hS.2 p

/-- The joint law of `-ω` is the joint law of the reflected entry laws. -/
private lemma nsq_law_neg {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) :
    (scale (-1) L).law = L.law.map (fun ω => -ω) := by
  have := hL.diag; have := hL.off
  have h1 : Measure.pi (fun i => (L.diag i).map (fun x => -1 * x)) =
      (Measure.pi L.diag).map (fun x i => -1 * x i) :=
    (Measure.pi_map_pi (fun i => (measurable_const_mul _).aemeasurable)).symm
  have h2 : Measure.pi (fun p => (L.off p).map (fun x => -1 * x)) =
      (Measure.pi L.off).map (fun x p => -1 * x p) :=
    (Measure.pi_map_pi (fun p => (measurable_const_mul _).aemeasurable)).symm
  simp only [law, scale]
  rw [h1, h2, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  congr 1
  funext ω
  ext <;> simp

private lemma nsq_symOfEntries_neg {N : ℕ} (ω : Entries N) :
    symOfEntries (-ω) = -symOfEntries ω := by
  ext i j
  simp only [symOfEntries, Matrix.neg_apply]
  split_ifs <;> simp

/-- Every eigenvalue of `H` is minus an eigenvalue of `-H`. -/
private lemma nsq_exists_eig_neg {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : B = -A) (α : Fin N) :
    ∃ β, hB.eigenvalues β = -hA.eigenvalues α := by
  have h1 : -hA.eigenvalues α ∈ spectrum ℝ B := by
    rw [hAB, ← spectrum.neg_eq]
    exact Set.neg_mem_neg.mpr (hA.eigenvalues_mem_spectrum_real α)
  rw [hB.spectrum_real_eq_range_eigenvalues] at h1
  exact h1

/-- An event of `ζ`-high probability on the class of Theorem 3.6 also holds for `-H`. -/
private lemma nsq_highProb_neg {ζ C1 φs : ℝ} {Ω : ∀ N : ℕ, Set (Entries N)}
    (h : HighProbOn ζ (SmallQClass C1 φs) (fun N _ => Ω N)) :
    HighProbOn ζ (SmallQClass C1 φs) (fun N _ => (fun ω => -ω) ⁻¹' Ω N) := by
  obtain ⟨c, hc, C, hC, N0, h⟩ := h
  refine ⟨c, hc, C, hC, N0, fun N hN L hL => ?_⟩
  rw [← Set.preimage_compl]
  calc L.law ((fun ω => -ω) ⁻¹' (Ω N)ᶜ) ≤ (L.law.map (fun ω => -ω)) (Ω N)ᶜ :=
        Measure.le_map_apply measurable_neg.aemeasurable _
    _ = (scale (-1) L).law (Ω N)ᶜ := by rw [nsq_law_neg hL.1.isProb]
    _ ≤ _ := h N hN _ (nsq_smallQ_neg hL)

/-! ### Moments of `m - m_sc` -/

private lemma nsq_continuous_stieltjesM {N : ℕ} {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Entries N => stieltjesM (symOfEntries ω) z := by
  simp only [stieltjesM, Matrix.trace, Matrix.diag]
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_resolventC_symOfEntries hz i i)

/-- `|m(z)| ≤ η⁻¹`. -/
private lemma nsq_norm_stieltjesM_le {N : ℕ} (ω : Entries N) {z : ℂ} (hz : 0 < z.im) :
    ‖stieltjesM (symOfEntries ω) z‖ ≤ 1 / z.im := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [show stieltjesM (symOfEntries ω) z = 0 by simp [stieltjesM], norm_zero]
    positivity
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : ‖∑ i, resolventC (symOfEntries ω) z i i‖ ≤ N * (1 / z.im) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖resolventC (symOfEntries ω) z i i‖ ≤ ∑ _i : Fin N, 1 / z.im :=
          Finset.sum_le_sum fun i _ =>
            norm_resolventC_apply_le (symOfEntries_isHermitian ω) hz i i
      _ = _ := by simp
  have e : stieltjesM (symOfEntries ω) z =
      (N : ℂ)⁻¹ * ∑ i, resolventC (symOfEntries ω) z i i := rfl
  rw [e, norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hNr]
  exact h1

/-- `|m(z) - m_sc(z)| ≤ η⁻¹ + 1`. -/
private lemma nsq_dist_le {N : ℕ} (ω : Entries N) {z : ℂ} (hz : 0 < z.im) :
    ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ 1 / z.im + 1 :=
  (norm_sub_le _ _).trans (add_le_add (nsq_norm_stieltjesM_le ω hz)
    (norm_msc_eq_inv_and_lt_one hz).2.le)

private lemma nsq_integrable {N : ℕ} (μ : Measure (Entries N)) [IsFiniteMeasure μ] {z : ℂ}
    (hz : 0 < z.im) (p : ℕ) :
    Integrable (fun ω => ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p) μ :=
  Integrable.of_bound
    (((nsq_continuous_stieltjesM hz.ne').sub continuous_const).norm.pow p).aestronglyMeasurable
    ((1 / z.im + 1) ^ p) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (nsq_dist_le ω hz) p)

/-- `E|m - m_sc|^p ≤ Y^p + (η⁻¹ + 1)^p P(|m - m_sc| > Y)`. -/
private lemma nsq_integral_le {N : ℕ} (μ : Measure (Entries N)) [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) {Y r : ℝ} (hY : 0 ≤ Y) (hr : 0 ≤ r)
    (h : μ {ω | ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y}ᶜ ≤ ENNReal.ofReal r) (p : ℕ) :
    ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ∂μ ≤ Y ^ p + (1 / z.im + 1) ^ p * r := by
  set A := {ω : Entries N | ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y} with hA
  set T := toMeasurable μ Aᶜ with hTdef
  have hT : MeasurableSet T := measurableSet_toMeasurable _ _
  set M := (1 / z.im + 1) ^ p with hM
  have hM0 : 0 ≤ M := by positivity
  have hle : ∀ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ≤
      Y ^ p + T.indicator (fun _ => M) ω := by
    intro ω
    have hi : 0 ≤ T.indicator (fun _ => M) ω := Set.indicator_nonneg (fun _ _ => hM0) ω
    by_cases hω : ω ∈ A
    · have : ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ≤ Y ^ p :=
        pow_le_pow_left₀ (norm_nonneg _) hω p
      linarith
    · have hωT : ω ∈ T := subset_toMeasurable _ _ hω
      rw [Set.indicator_of_mem hωT]
      have := pow_le_pow_left₀ (norm_nonneg _) (nsq_dist_le ω hz) p
      have : 0 ≤ Y ^ p := by positivity
      linarith
  have hgi : Integrable (fun ω => Y ^ p + T.indicator (fun _ => M) ω) μ :=
    (integrable_const _).add ((integrable_const M).indicator hT)
  have hTr : μ.real T ≤ r := by
    rw [measureReal_def, hTdef, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hr h
  calc ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ∂μ
      ≤ ∫ ω, (Y ^ p + T.indicator (fun _ => M) ω) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) hgi (ae_of_all _ hle)
    _ = Y ^ p + μ.real T * M := by
        rw [integral_add (integrable_const _) ((integrable_const M).indicator hT),
          integral_indicator_const _ hT]
        simp
    _ ≤ Y ^ p + M * r := by
        have := mul_le_mul_of_nonneg_left hTr hM0
        linarith

/-- Markov's inequality for `|m - m_sc|^p`. -/
private lemma nsq_markov {N : ℕ} (μ : Measure (Entries N)) [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) {R : ℝ} (hR : 0 < R) {p : ℕ}
    (h : ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ∂μ ≤ 3 * R ^ p) :
    μ {ω | 2 * R ≤ ‖stieltjesM (symOfEntries ω) z - msc z‖} ≤ ENNReal.ofReal (3 / 2 ^ p) := by
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => by positivity)
    (nsq_integrable μ hz p) ((2 * R) ^ p)
  have hsub : {ω : Entries N | 2 * R ≤ ‖stieltjesM (symOfEntries ω) z - msc z‖} ⊆
      {ω : Entries N | (2 * R) ^ p ≤ ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p} :=
    fun ω hω => pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * R) hω p
  have h2 : μ.real {ω : Entries N | (2 * R) ^ p ≤ ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p} ≤
      3 / 2 ^ p := by
    set S := μ.real {ω : Entries N | (2 * R) ^ p ≤ ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p}
    rw [le_div_iff₀ (by positivity)]
    have e : (2 * R) ^ p = 2 ^ p * R ^ p := mul_pow _ _ _
    have hRp : 0 < R ^ p := pow_pos hR p
    have h3 : R ^ p * (S * 2 ^ p) ≤ R ^ p * 3 := by
      have := hmk.trans h
      rw [e] at this
      linarith
    exact le_of_mul_le_mul_left h3 hRp
  exact (measure_mono hsub).trans
    ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 h2)

/-! ### The grid -/

/-- If no eigenvalue lies within `N⁻¹` of a point `b + k/N ≤ 3`, `k < N`, then no eigenvalue lies
in `[b, 3]`. -/
private lemma nsq_grid {N : ℕ} (hN : 0 < N) {lam b : ℝ} (hb : 2 < b)
    (h : ∀ k : Fin N, b + k / N ≤ 3 → 1 / N < |lam - (b + k / N)|) (hl : lam ≤ 3) : lam < b := by
  by_contra hlb
  rw [not_lt] at hlb
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set k : ℕ := ⌊(lam - b) * N⌋₊ with hk
  have hk1 : (k : ℝ) ≤ (lam - b) * N := Nat.floor_le (by nlinarith)
  have hk2 : (lam - b) * N < k + 1 := Nat.lt_floor_add_one _
  have hkN : k < N := by
    have : (k : ℝ) < N := by nlinarith
    exact_mod_cast this
  have hkN' : (k : ℝ) / N ≤ lam - b := by rw [div_le_iff₀ hNr]; linarith
  have h3 := h ⟨k, hkN⟩ (by simp only; linarith)
  simp only at h3
  have h4 : lam - (b + k / N) < 1 / N := by
    rw [show lam - (b + k / N) = ((lam - b) * N - k) / N by field_simp; ring]
    exact div_lt_div_of_pos_right (by linarith) hNr
  rw [abs_of_nonneg (by linarith)] at h3
  linarith

/-- Smaller class, larger events from some `N1` on. -/
private lemma nsq_mono {ζ : ℝ} {Cls Cls' : ∀ N : ℕ, EntryLaws N → Prop}
    {Ω Ω' : ∀ N : ℕ, EntryLaws N → Set (Entries N)} (h : HighProbOn ζ Cls Ω)
    (hcls : ∀ N L, Cls' N L → Cls N L) (N1 : ℕ)
    (hsub : ∀ N ≥ N1, ∀ L, Cls' N L → Ω N L ⊆ Ω' N L) : HighProbOn ζ Cls' Ω' := by
  obtain ⟨c, hc, C, hC, N0, h⟩ := h
  exact ⟨c, hc, C, hC, max N0 N1, fun N hN L hL =>
    (measure_mono (Set.compl_subset_compl.mpr
      (hsub N (le_trans (le_max_right _ _) hN) L hL))).trans
      (h N (le_trans (le_max_left _ _) hN) L (hcls N L hL))⟩

/-! ### Parameter bounds at one point of the window -/

/-- With `η = P/(N s)`, `N s³ ≥ V³ ≥ P²A²φ²` and `Wφ² ≤ A²`: the bounds of (5.20)–(5.22). -/
private lemma nsq_arith {n s P A V ϕ W Cm : ℝ} (hn : 0 < n) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hP : 1 ≤ P) (hA : 2 ≤ A) (hϕ : 1 ≤ ϕ) (hW : 0 ≤ W) (hV : P ^ 2 * A ^ 2 * ϕ ^ 2 ≤ V ^ 3)
    (hVs : V ^ 3 ≤ n * s ^ 3) (hWA : W * ϕ ^ 2 ≤ A ^ 2) (hCm : 10 * Cm ≤ ϕ ^ 2)
    (h15 : 15 ≤ ϕ ^ 2) :
    1 / n ≤ P / (n * s) ∧ P / (n * s) ≤ s ^ 2 ∧
    Cm * (P / (n * s) / s) ≤ (n * (P / (n * s)))⁻¹ / 10 ∧
    (A ^ 3 * n * (P / (n * s)))⁻¹ ≤ (n * (P / (n * s)))⁻¹ / 5 ∧
    W * ((A * n * (P / (n * s)))⁻¹ ^ 2 + (A ^ 3 * n * (P / (n * s)))⁻¹ + ϕ / n) ≤
      (n * (P / (n * s)))⁻¹ / 5 ∧
    1 / (P / (n * s)) + 1 ≤ 2 * n * (n * (P / (n * s)))⁻¹ := by
  have hP0 : 0 < P := by linarith
  have hA0 : 0 < A := by linarith
  have hns : 0 < n * s := by positivity
  have hu : (n * (P / (n * s)))⁻¹ = s / P := by
    rw [show n * (P / (n * s)) = P / s by field_simp, inv_div]
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hϕ2 : 1 ≤ ϕ ^ 2 := by nlinarith
  have hAϕ : 1 ≤ A ^ 2 * ϕ ^ 2 := one_le_mul_of_one_le_of_one_le hA2 hϕ2
  have hPP : P ≤ P ^ 2 := by nlinarith
  have hX : P ^ 2 ≤ P ^ 2 * A ^ 2 * ϕ ^ 2 := by
    rw [mul_assoc]; exact le_mul_of_one_le_right (by positivity) hAϕ
  have hns3 : P ^ 2 * A ^ 2 * ϕ ^ 2 ≤ n * s ^ 3 := hV.trans hVs
  have hPle : P ≤ n * s ^ 3 := hPP.trans (hX.trans hns3)
  have hs3 : s ^ 3 ≤ s := by
    have : s ^ 3 = s * s ^ 2 := by ring
    rw [this]; exact mul_le_of_le_one_right hs0.le (pow_le_one₀ hs0.le hs1)
  have hns' : n * s ^ 3 ≤ n * s := mul_le_mul_of_nonneg_left hs3 hn.le
  have hη1 : P / (n * s) ≤ 1 := by rw [div_le_one hns]; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hn hns]; nlinarith
  · rw [div_le_iff₀ hns]
    have : s ^ 2 * (n * s) = n * s ^ 3 := by ring
    linarith
  · rw [hu]
    have e : Cm * (P / (n * s) / s) = Cm * P / (n * s ^ 2) := by field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : 10 * Cm * P ^ 2 ≤ n * s ^ 3 := by
      have : 10 * Cm * P ^ 2 ≤ P ^ 2 * A ^ 2 * ϕ ^ 2 := by
        have h2 : 10 * Cm ≤ A ^ 2 * ϕ ^ 2 := hCm.trans (le_mul_of_one_le_left (by positivity) hA2)
        have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ P ^ 2)
        linarith
      linarith
    have e2 : s / P / 10 * (n * s ^ 2) = n * s ^ 3 / (10 * P) := by field_simp
    rw [e2, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [show A ^ 3 * n * (P / (n * s)) = A ^ 3 * (n * (P / (n * s))) by ring, mul_inv, hu]
    have hA3 : 5 ≤ A ^ 3 := by nlinarith
    rw [inv_mul_le_iff₀ (by positivity)]
    have hsP : 0 ≤ s / P := by positivity
    nlinarith
  · have e1 : (A * n * (P / (n * s)))⁻¹ = s / P / A := by
      rw [show A * n * (P / (n * s)) = A * (n * (P / (n * s))) by ring, mul_inv, hu]
      field_simp
    have e2 : (A ^ 3 * n * (P / (n * s)))⁻¹ = s / P / A ^ 3 := by
      rw [show A ^ 3 * n * (P / (n * s)) = A ^ 3 * (n * (P / (n * s))) by ring, mul_inv, hu]
      field_simp
    rw [e1, e2, hu]
    have hu0 : 0 < s / P := by positivity
    have hu1 : s / P ≤ 1 := by rw [div_le_one hP0]; linarith
    have t1 : (s / P / A) ^ 2 ≤ s / P / A ^ 2 := by
      rw [div_pow, div_le_div_iff_of_pos_right (by positivity)]
      have : (s / P) ^ 2 = s / P * (s / P) := by ring
      rw [this]; exact mul_le_of_le_one_right hu0.le hu1
    have t2 : s / P / A ^ 3 ≤ s / P / A ^ 2 :=
      div_le_div_of_nonneg_left hu0.le (by positivity) (by nlinarith)
    have t3 : ϕ / n ≤ s / P / A ^ 2 := by
      rw [div_div, div_le_div_iff₀ hn (by positivity)]
      have h1 : ϕ * (P * A ^ 2) ≤ P ^ 2 * A ^ 2 * ϕ ^ 2 := by
        have e : P ^ 2 * A ^ 2 * ϕ ^ 2 = ϕ * (P * A ^ 2) * (P * ϕ) := by ring
        rw [e]
        exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hP hϕ)
      have : s * n = n * s := mul_comm _ _
      linarith
    have hsum : (s / P / A) ^ 2 + s / P / A ^ 3 + ϕ / n ≤ 3 * (s / P / A ^ 2) := by linarith
    have hfin : W * (3 * (s / P / A ^ 2)) ≤ s / P / 5 := by
      have e3 : W * (3 * (s / P / A ^ 2)) = 3 * (s / P) * W / A ^ 2 := by ring
      rw [e3, div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 := mul_le_mul_of_nonneg_left hWA (by positivity : (0 : ℝ) ≤ 15 * (s / P))
      have h2 : 3 * (s / P) * W * 5 * ϕ ^ 2 ≤ 15 * (s / P) * (W * ϕ ^ 2) := by ring_nf; rfl
      have h3 : 3 * (s / P) * W * 5 ≤ 3 * (s / P) * W * 5 * ϕ ^ 2 :=
        le_mul_of_one_le_right (by positivity) hϕ2
      have h4 : 15 * (s / P) * A ^ 2 ≤ s / P * A ^ 2 * ϕ ^ 2 := by
        have := mul_le_mul_of_nonneg_left h15 (by positivity : (0 : ℝ) ≤ s / P * A ^ 2)
        linarith
      nlinarith
    calc W * ((s / P / A) ^ 2 + s / P / A ^ 3 + ϕ / n) ≤ W * (3 * (s / P / A ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum hW
      _ ≤ s / P / 5 := hfin
  · rw [hu]
    have e : 1 / (P / (n * s)) = n * s / P := by rw [one_div, inv_div]
    rw [e]
    have : 1 ≤ n * s / P := by rw [le_div_iff₀ hP0]; rw [div_le_one hns] at hη1; linarith
    have e2 : 2 * n * (s / P) = 2 * (n * s / P) := by ring
    rw [e2]; linarith

/-- `N^{C'} e^{-c φ⁴} ≤ N e^{-φ³}` once `c φ ≥ C' + 2` and `log N ≤ φ`. -/
private lemma nsq_level {N C' : ℕ} {ϕ c : ℝ} (hN : 1 ≤ N) (hϕ : 1 ≤ ϕ)
    (hlog : Real.log N ≤ ϕ) (hC'0 : 0 < C') (hc : (C' : ℝ) + 2 ≤ c * ϕ) :
    (N : ℝ) ^ C' * Real.exp (-c * ϕ ^ (4 : ℝ)) ≤
      (N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * ϕ ^ (3 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hC' : (0 : ℝ) < C' := Nat.cast_pos.mpr hC'0
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hN0, ← Real.exp_add,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e4 : ϕ ^ (4 : ℝ) = ϕ ^ 3 * ϕ := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have e3 : ϕ ^ (3 : ℝ) = ϕ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e4, e3]
  have h3 : ϕ ≤ ϕ ^ 3 := le_self_pow₀ hϕ (by norm_num)
  have h1 : (C' : ℝ) * Real.log N ≤ C' * ϕ ^ 3 :=
    mul_le_mul_of_nonneg_left (hlog.trans h3) hC'.le
  have h2 : ((C' : ℝ) + 2) * ϕ ^ 3 ≤ c * ϕ * ϕ ^ 3 := mul_le_mul_of_nonneg_right hc (by positivity)
  have hl0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  nlinarith

/-- `(10N)^p N e^{-φ³} ≤ 1` for `p ≤ φ`, `log N ≤ φ`, `φ ≥ 3` and `N ≥ 10`. -/
private lemma nsq_tail {N p : ℕ} {ϕ : ℝ} (hN : 10 ≤ N) (hϕ : 3 ≤ ϕ) (hlog : Real.log N ≤ ϕ)
    (hp : (p : ℝ) ≤ ϕ) :
    (10 * (N : ℝ)) ^ p * ((N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * ϕ ^ (3 : ℝ))) ≤ 1 := by
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have e3 : ϕ ^ (3 : ℝ) = ϕ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.rpow_one, e3]
  have h1 : (10 * (N : ℝ)) ^ p ≤ ((N : ℝ) ^ 2) ^ p :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) p
  have h2 : ((N : ℝ) ^ 2) ^ p * N = Real.exp ((2 * p + 1) * Real.log N) := by
    rw [show (2 * (p : ℝ) + 1) * Real.log N = ((2 * p + 1 : ℕ) : ℝ) * Real.log N by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hN0]
    ring
  have h3 : (2 * (p : ℝ) + 1) * Real.log N ≤ ϕ ^ 3 := by
    have : (2 * (p : ℝ) + 1) * Real.log N ≤ (2 * ϕ + 1) * ϕ :=
      mul_le_mul (by linarith) hlog hl0 (by linarith)
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hϕ) (by linarith : (0 : ℝ) ≤ ϕ + 1))
      (by linarith : (0 : ℝ) ≤ ϕ)]
  have hE : 0 < Real.exp (-1 * ϕ ^ 3) := Real.exp_pos _
  calc (10 * (N : ℝ)) ^ p * ((N : ℝ) * Real.exp (-1 * ϕ ^ 3))
      ≤ ((N : ℝ) ^ 2) ^ p * N * Real.exp (-1 * ϕ ^ 3) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hN0.le) hE.le
    _ = Real.exp ((2 * p + 1) * Real.log N) * Real.exp (-1 * ϕ ^ 3) := by rw [h2]
    _ ≤ Real.exp (ϕ ^ 3) * Real.exp (-1 * ϕ ^ 3) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h3) hE.le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- `3 · 2^{-p} ≤ N e^{-(log 2) φ}` for `p ≥ φ - 2` and `N ≥ 12`. -/
private lemma nsq_prob {N p : ℕ} {ϕ : ℝ} (hN : 12 ≤ N) (hp : ϕ - 2 ≤ p) :
    3 / (2 : ℝ) ^ p ≤ (N : ℝ) ^ (1 : ℕ) * Real.exp (-Real.log 2 * ϕ ^ (1 : ℝ)) := by
  rw [pow_one, Real.rpow_one]
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h4 : Real.exp (2 * Real.log 2) = 4 := by
    rw [show (2 : ℝ) * Real.log 2 = ((2 : ℕ) : ℝ) * Real.log 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log two_pos]
    norm_num
  have e : 3 / (2 : ℝ) ^ p = 3 * Real.exp (-(p * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, div_eq_mul_inv]
  have h5 : Real.exp (-(p * Real.log 2)) ≤
      Real.exp (2 * Real.log 2) * Real.exp (-Real.log 2 * ϕ) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [e]
  rw [h4] at h5
  nlinarith [Real.exp_pos (-Real.log 2 * ϕ)]

/-- `K log N · N^{2/5} ≤ √N` for all large `N`. -/
private lemma nsq_eventually_tilde (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K * Real.log N * (N : ℝ) ^ (2 / 5 : ℝ) ≤ Real.sqrt N := by
  filter_upwards [((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (20 * |K|), eventually_ge_atTop 1]
    with N hN h1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hN0 : (0 : ℝ) < N := by linarith
  simp only [Function.comp] at hN
  have hlog : Real.log N ≤ (N : ℝ) ^ (1 / 20 : ℝ) / (1 / 20) :=
    Real.log_le_rpow_div hN0.le (by norm_num)
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  set t := (N : ℝ) ^ (1 / 20 : ℝ) with ht
  have ht0 : 0 ≤ t := by positivity
  have hsq : Real.sqrt N = t * t * (N : ℝ) ^ (2 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ht, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; norm_num
  have hr : 0 ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by positivity
  rw [hsq]
  have : K * Real.log N ≤ t * t := by
    calc K * Real.log N ≤ |K| * Real.log N := mul_le_mul_of_nonneg_right (le_abs_self K) hl0
      _ ≤ |K| * (20 * t) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg K)
          have : t / (1 / 20) = 20 * t := by ring
          linarith
      _ ≤ t * t := by nlinarith [abs_nonneg K]
  exact mul_le_mul_of_nonneg_right this hr

/-- `T ≤ φ` for all large `N`. -/
private lemma nsq_eventually_phi (T : ℝ) : ∀ᶠ N : ℕ in atTop, T ≤ phi N := by
  filter_upwards [eventually_ge_atTop 16, (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop T] with N h16 hT
  exact hT.trans (log_le_phi h16)

/-! ### (5.17): the upper edge -/

/-- (5.18)–(5.22) at one point `E ∈ [2 + φ^{C_t} N^{-2/3}, 3]`, `η = φ^{K+a}/(N√κ)`: `N⁻¹ ≤ η ≤ 1`,
`E + iη ∈ S(C_0)`, `Im m_sc ≤ (10Nη)⁻¹`, `(φ^a N η)⁻¹ ≤ (5Nη)⁻¹`, the error term of (5.11) with
`X = (φ^{a/3}Nη)⁻¹`, `Y = (φ^a Nη)⁻¹` is at most `(5Nη)⁻¹`, and `η⁻¹ + 1 ≤ 2N(Nη)⁻¹`. -/
private lemma nsq_window {N : ℕ} {K a Ct Cs Cm C0m E : ℝ} (hN : 16 ≤ N) (hK : 0 < K)
    (hCs : 0 < Cs) (hCm : 0 ≤ Cm) (hC0m : 0 < C0m) (ha : a = 49 + 3 * Cs + C0m)
    (hCt : 2 * (K + a) + 2 * (a / 3) + 2 ≤ 3 * (Ct / 2))
    (hmsc : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → z.im ≤ kappa z.re → 2 ≤ |z.re| →
      (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im)))
    (hϕ16 : 16 ≤ phi N) (hϕCm : 10 * Cm ≤ phi N)
    (hbE : 2 + phi N ^ Ct * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ E) (hE3 : E ≤ 3) :
    1 / (N : ℝ) ≤ outEta N K a E ∧ outEta N K a E ≤ 1 ∧
    (⟨E, outEta N K a E⟩ : ℂ) ∈ specDomain N C0m ∧
    (msc ⟨E, outEta N K a E⟩).im ≤ (N * outEta N K a E)⁻¹ / 10 ∧
    (phi N ^ a * N * outEta N K a E)⁻¹ ≤ (N * outEta N K a E)⁻¹ / 5 ∧
    phi N ^ (2 * Cs) * ((phi N ^ (a / 3) * N * outEta N K a E)⁻¹ ^ 2 +
      (phi N ^ a * N * outEta N K a E)⁻¹ + phi N / N) ≤ (N * outEta N K a E)⁻¹ / 5 ∧
    1 / outEta N K a E + 1 ≤ 2 * N * (N * outEta N K a E)⁻¹ := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0r : (0 : ℝ) < N := by linarith
  set ϕ := phi N with hϕdef
  have hϕ0 : 0 < ϕ := by linarith
  have hϕ1 : 1 ≤ ϕ := by linarith
  -- powers of `φ`
  have rp2 : ∀ y : ℝ, ϕ ^ (y * 2) = (ϕ ^ y) ^ 2 := fun y => by
    rw [show y * 2 = y * ((2 : ℕ) : ℝ) by norm_num, Real.rpow_mul_natCast hϕ0.le]
  have rp3 : ∀ y : ℝ, ϕ ^ (y * 3) = (ϕ ^ y) ^ 3 := fun y => by
    rw [show y * 3 = y * ((3 : ℕ) : ℝ) by norm_num, Real.rpow_mul_natCast hϕ0.le]
  set P : ℝ := ϕ ^ (K + a) with hP
  set A : ℝ := ϕ ^ (a / 3) with hA
  set V : ℝ := ϕ ^ (Ct / 2) with hV
  set W : ℝ := ϕ ^ (2 * Cs) with hW
  have hAa : ϕ ^ a = A ^ 3 := by rw [← rp3]; congr 1; ring
  have hVC : ϕ ^ Ct = V ^ 2 := by rw [← rp2]; congr 1; ring
  have hP1 : 1 ≤ P := Real.one_le_rpow hϕ1 (by rw [ha]; positivity)
  have hA2 : 2 ≤ A := by
    have : ϕ ^ (1 : ℝ) ≤ A := Real.rpow_le_rpow_of_exponent_le hϕ1 (by rw [ha]; linarith)
    rw [Real.rpow_one] at this
    linarith
  have hW0 : 0 ≤ W := by positivity
  have hPAV : P ^ 2 * A ^ 2 * ϕ ^ 2 ≤ V ^ 3 := by
    have e : P ^ 2 * A ^ 2 * ϕ ^ 2 = ϕ ^ ((K + a) * 2 + a / 3 * 2 + 2) := by
      rw [Real.rpow_add hϕ0, Real.rpow_add hϕ0, rp2, rp2]
      norm_num
      left; rfl
    rw [e, hV, ← rp3]
    exact Real.rpow_le_rpow_of_exponent_le hϕ1 (by linarith)
  have hWA : W * ϕ ^ 2 ≤ A ^ 2 := by
    have e : W * ϕ ^ 2 = ϕ ^ (2 * Cs + 2) := by
      rw [Real.rpow_add hϕ0]; norm_num
      left; rfl
    rw [e, hA, ← rp2]
    exact Real.rpow_le_rpow_of_exponent_le hϕ1 (by rw [ha]; linarith)
  -- `ρ = N^{-1/3}`
  set ρ : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hN0r _
  have hρ2 : (N : ℝ) ^ (-(2 : ℝ) / 3) = ρ ^ 2 := by
    rw [hρ, ← Real.rpow_mul_natCast hN0r.le]; norm_num
  have hρ3 : (N : ℝ) * ρ ^ 3 = 1 := by
    rw [hρ, ← Real.rpow_mul_natCast hN0r.le]
    norm_num
    rw [Real.rpow_neg_one, mul_inv_cancel₀ hN0r.ne']
  -- `κ = E - 2 ≥ (Vρ)²`
  have hb2 : ϕ ^ Ct * (N : ℝ) ^ (-(2 : ℝ) / 3) = (V * ρ) ^ 2 := by rw [mul_pow, ← hVC, ← hρ2]
  rw [hb2] at hbE
  have hVρ : 0 < V * ρ := mul_pos (Real.rpow_pos_of_pos hϕ0 _) hρ0
  have hE2 : 2 ≤ E := by
    have := sq_nonneg (V * ρ)
    linarith
  have hκ : kappa E = E - 2 := by
    unfold kappa
    rw [abs_of_nonneg (show (0 : ℝ) ≤ E by linarith), abs_of_nonneg (by linarith)]
  set sκ : ℝ := Real.sqrt (kappa E) with hsκ
  have hs1 : sκ ≤ 1 := by
    rw [hsκ, Real.sqrt_le_one, hκ]; linarith
  have hsVρ : V * ρ ≤ sκ := by
    rw [hsκ, Real.le_sqrt hVρ.le (by rw [hκ]; linarith), hκ]
    linarith
  have hs0 : 0 < sκ := hVρ.trans_le hsVρ
  have hVs : V ^ 3 ≤ N * sκ ^ 3 := by
    have h1 : (V * ρ) ^ 3 ≤ sκ ^ 3 := pow_le_pow_left₀ hVρ.le hsVρ 3
    have h2 : V ^ 3 = N * (V * ρ) ^ 3 := by
      rw [mul_pow]
      calc V ^ 3 = V ^ 3 * (N * ρ ^ 3) := by rw [hρ3, mul_one]
        _ = _ := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hN0r.le
  have hϕ2 : 15 ≤ ϕ ^ 2 := by
    rw [sq]; linarith [mul_le_mul hϕ16 hϕ16 (by norm_num) hϕ0.le]
  have hCm2 : 10 * Cm ≤ ϕ ^ 2 := by
    rw [sq]; linarith [le_mul_of_one_le_right hϕ0.le hϕ1]
  obtain ⟨h1N, hηκ, hImsc, hY5, hB5, hM2⟩ :=
    nsq_arith hN0r hs0 hs1 hP1 hA2 hϕ1 hW0 hPAV hVs hWA hCm2 hϕ2
  have hη : outEta N K a E = P / (N * sκ) := rfl
  set η : ℝ := outEta N K a E with hηdef
  rw [← hη] at h1N hηκ hImsc hY5 hB5 hM2
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) h1N
  have hκs : sκ ^ 2 = kappa E := Real.sq_sqrt (by rw [hκ]; linarith)
  have hη1 : η ≤ 1 := hηκ.trans (by rw [hκs, hκ]; linarith)
  refine ⟨h1N, hη1, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, hM2⟩
  · change |E| ≤ 5
    rw [abs_of_nonneg (by linarith)]; linarith
  · change ϕ ^ C0m / N < η
    have h1 : ϕ ^ C0m < P := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by rw [ha]; linarith)
    have h2 : P / N ≤ η := by
      rw [hη]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_of_le_one_right hN0r.le hs1)
    exact (div_lt_div_of_pos_right h1 hN0r).trans_le h2
  · change η ≤ 10
    linarith
  · have hm := hmsc ⟨E, η⟩ (by change |E| ≤ 5; rw [abs_of_nonneg (by linarith)]; linarith) hη0
      (by change η ≤ 10; linarith) (by change η ≤ kappa E; rw [← hκs]; exact hηκ)
      (by change 2 ≤ |E|; rw [abs_of_nonneg (by linarith)]; exact hE2)
    refine hm.trans (le_trans (mul_le_mul_of_nonneg_left ?_ hCm) hImsc)
    refine div_le_div_of_nonneg_left hη0.le hs0 ?_
    change sκ ≤ Real.sqrt (kappa E + η)
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [hAa]; exact hY5
  · rw [hAa]; exact hB5

/-- (5.17) at one point `E` of the window: the probability that some eigenvalue lies within `N⁻¹`
of `E` is at most `N e^{-(log 2) φ}`. The bound (5.19) for the matched law `H̃` of Lemma 5.1
(support exponent `2/5 > 1/3`) gives (5.10) for `H̃`; Lemma 5.4 with an even `p ≤ φ` and Markov's
inequality give `|m - m_sc| < 2(5Nη)⁻¹` for `H`, hence `Im m < (2Nη)⁻¹`. -/
private lemma nsq_point {N Co' : ℕ} {C1 φs K a Co Ct Cs Cm C0m co : ℝ} {L : EntryLaws N}
    (hK : 0 < K) (hCs : 0 < Cs) (hCm : 1 ≤ Cm) (hC0m : 0 < C0m) (hCo : 0 < Co) (hco : 0 < co)
    (hCo' : 0 < Co') (ha : a = 49 + 3 * Cs + C0m) (hCt : Ct = Co + 2 * K + 3 * a + 2)
    (hmsc : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → z.im ≤ kappa z.re → 2 ≤ |z.re| →
      (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im)))
    (hO : ∀ Lw : EntryLaws N, Lw.IsGenWigner (max C1 1) →
      Lw.law {ω | (∃ q, Lw.SupportParam ((N : ℝ) ^ (2 / 5 : ℝ)) 1 q) →
        ω ∈ outEvent N K a Co}ᶜ ≤
        ENNReal.ofReal ((N : ℝ) ^ Co' * Real.exp (-co * phi N ^ (4 : ℝ))))
    (hMC : ∀ (Lv Lw : EntryLaws N) (q : ℝ), MatchedPair C1 q Lv Lw →
      (N : ℝ) ^ min φs (1 / 4) ≤ q → ∀ z ∈ specDomain N C0m, ∀ X Y : ℝ, 0 ≤ X → 0 ≤ Y →
      Lw.law {ω | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
          ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y}ᶜ ≤
        ENNReal.ofReal ((N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * phi N ^ (3 : ℝ))) →
      ∀ p : ℕ, Even p → (p : ℝ) ≤ phi N →
        ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ∂Lv.law ≤
          ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ∂Lw.law +
            (Cs * p) ^ (Cs * p) * (X ^ 2 + Y + phi N / N) ^ p)
    (hN : 16 ≤ N) (hϕT : 16 + 10 * Cm + Cs + (Co' + 2) / co ≤ phi N)
    (htil : (2 * C1 + 4) * C1 * Real.log N * (N : ℝ) ^ (2 / 5 : ℝ) ≤ Real.sqrt N)
    (hL : SmallQClass C1 φs N L) {E : ℝ}
    (hbE : 2 + phi N ^ Ct * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ E) (hE3 : E ≤ 3) :
    L.law {ω : Entries N | ∀ α, 1 / (N : ℝ) <
        |(symOfEntries_isHermitian ω).eigenvalues α - E|}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ (1 : ℕ) * Real.exp (-Real.log 2 * phi N ^ (1 : ℝ))) := by
  have hN3 : 3 ≤ N := by omega
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0r : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hlogϕ : Real.log N ≤ phi N := log_le_phi hN
  have hCo'0 : (0 : ℝ) ≤ Co' := Nat.cast_nonneg _
  have hT0 : 0 ≤ (Co' + 2) / co := by positivity
  have hϕ16 : 16 ≤ phi N := by linarith
  have hϕCm : 10 * Cm ≤ phi N := by linarith
  have hϕCs : Cs ≤ phi N := by linarith
  have hϕco : (Co' : ℝ) + 2 ≤ co * phi N := by
    have : (Co' + 2) / co ≤ phi N := by linarith
    rw [div_le_iff₀ hco] at this
    linarith
  obtain ⟨h1N, hη1, hzS, hmscim, hY5, hB5, hM2⟩ := nsq_window (K := K) (a := a) (Ct := Ct)
    (C0m := C0m) hN hK hCs (by linarith) hC0m ha (by rw [hCt]; linarith) hmsc hϕ16 hϕCm hbE hE3
  set ϕ := phi N with hϕdef
  have hϕ0 : 0 < ϕ := by linarith
  have hϕ1 : 1 ≤ ϕ := by linarith
  set η : ℝ := outEta N K a E with hηdef
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) h1N
  set z : ℂ := ⟨E, η⟩ with hz
  have hzre : z.re = E := rfl
  have hzim : z.im = η := rfl
  have hzpos : 0 < z.im := hη0
  -- the matched law `H̃` of Lemma 5.1
  obtain ⟨Lw, hw⟩ := exists_isMomentMatch hN3 hL.1
  have hmp := MatchedPair.of_smallQ hN3 hL hw
  have hq0 := tilde_pos hN3 hL.1 hw
  have hq25 : (N : ℝ) ^ (2 / 5 : ℝ) ≤ Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N) := by
    have hD : 0 < (2 * C1 + 4) * C1 * Real.log N :=
      (div_pos_iff_of_pos_left (Real.sqrt_pos.mpr hN0r)).1 hq0
    rw [le_div_iff₀ hD]
    linarith
  have hqφ : (N : ℝ) ^ min φs (1 / 4) ≤
      min ((N : ℝ) ^ φs) (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) :=
    le_min (Real.rpow_le_rpow_of_exponent_le hN1r (min_le_left _ _))
      ((Real.rpow_le_rpow_of_exponent_le hN1r ((min_le_right _ _).trans (by norm_num))).trans
        hq25)
  -- (5.19) for `H̃`, at the level of (5.10)
  have hwS : ∃ q, Lw.SupportParam ((N : ℝ) ^ (2 / 5 : ℝ)) 1 q :=
    ⟨_, hq25, hw.2.1.boundedSupport 1, hw.2.1.tailVarOff 1⟩
  have hOut := hO Lw hmp.isGenWigner.2
  have hEwin : 2 + ϕ ^ Co * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ E := by
    have h1 : ϕ ^ Co ≤ ϕ ^ Ct := Real.rpow_le_rpow_of_exponent_le hϕ1 (by rw [hCt]; linarith)
    have h2 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    linarith
  set X : ℝ := (ϕ ^ (a / 3) * N * η)⁻¹ with hX
  set Y : ℝ := (ϕ ^ a * N * η)⁻¹ with hY
  have hsub : {ω : Entries N | (∀ i j, i ≠ j → ‖resS z ω i j‖ ≤ X) ∧
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y}ᶜ ⊆
      {ω | (∃ q, Lw.SupportParam ((N : ℝ) ^ (2 / 5 : ℝ)) 1 q) → ω ∈ outEvent N K a Co}ᶜ := by
    intro ω hω hω'
    obtain ⟨h1, -, h3⟩ := hω' hwS E hEwin hE3
    exact hω ⟨h3, h1⟩
  have hlev := nsq_level (N := N) (by omega) hϕ1 hlogϕ hCo' hϕco
  have h510 := (measure_mono hsub).trans (hOut.trans (ENNReal.ofReal_le_ofReal hlev))
  -- Lemma 5.4 with an even `p ≤ φ`
  set p : ℕ := 2 * ⌊ϕ / 2⌋₊ with hp
  have hpe : Even p := even_two_mul _
  have hpϕ : (p : ℝ) ≤ ϕ := by
    have := Nat.floor_le (show 0 ≤ ϕ / 2 by positivity)
    rw [hp]; push_cast; linarith
  have hp2 : ϕ - 2 ≤ p := by
    have := Nat.lt_floor_add_one (ϕ / 2)
    rw [hp]; push_cast; linarith
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hcmp := hMC L Lw _ hmp hqφ z hzS X Y hX0 hY0 h510 p hpe hpϕ
  -- the moment of `H̃`
  have hYset : Lw.law {ω | ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ Y}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * ϕ ^ (3 : ℝ))) :=
    (measure_mono (Set.compl_subset_compl.2 fun _ hω => (Set.mem_ofPred_eq ▸ hω :
      (∀ i j, i ≠ j → ‖resS z _ i j‖ ≤ X) ∧ ‖stieltjesM (symOfEntries _) z - msc z‖ ≤ Y).2)).trans
      h510
  have := isProbabilityMeasure_law hmp.isProb_w
  have := isProbabilityMeasure_law hmp.isProb_v
  have hwint := nsq_integral_le Lw.law hzpos hY0 (by positivity) hYset p
  rw [hzim] at hwint
  -- the three terms
  set u : ℝ := (N * η)⁻¹ / 5 with hu
  have hu0 : 0 < u := by positivity
  have t1 : Y ^ p ≤ u ^ p := pow_le_pow_left₀ hY0 hY5 p
  have t2 : (1 / η + 1) ^ p * ((N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * ϕ ^ (3 : ℝ))) ≤ u ^ p := by
    have h1 : 1 / η + 1 ≤ 10 * N * u := by rw [hu]; linarith
    have h2 : (1 / η + 1) ^ p ≤ (10 * (N : ℝ)) ^ p * u ^ p := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 p
    have h3 := nsq_tail (N := N) (p := p) (by omega) (by linarith) hlogϕ hpϕ
    have h4 : 0 ≤ (N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * ϕ ^ (3 : ℝ)) := by positivity
    calc (1 / η + 1) ^ p * ((N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * ϕ ^ (3 : ℝ)))
        ≤ (10 * (N : ℝ)) ^ p * u ^ p *
            ((N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * ϕ ^ (3 : ℝ))) :=
          mul_le_mul_of_nonneg_right h2 h4
      _ = u ^ p * ((10 * (N : ℝ)) ^ p *
            ((N : ℝ) ^ (1 : ℝ) * Real.exp (-1 * ϕ ^ (3 : ℝ)))) := by ring
      _ ≤ u ^ p * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = u ^ p := mul_one _
  have t3 : (Cs * p) ^ (Cs * p) * (X ^ 2 + Y + ϕ / N) ^ p ≤ u ^ p := by
    have hS0 : 0 ≤ X ^ 2 + Y + ϕ / N := by positivity
    have hcp0 : 0 ≤ Cs * p := by positivity
    have e : (Cs * p) ^ (Cs * (p : ℝ)) = ((Cs * p) ^ Cs) ^ p :=
      Real.rpow_mul_natCast hcp0 Cs p
    have hW : (Cs * p) ^ Cs ≤ ϕ ^ (2 * Cs) := by
      have h1 : Cs * p ≤ ϕ * ϕ := mul_le_mul hϕCs hpϕ (Nat.cast_nonneg _) hϕ0.le
      have h2 : ϕ ^ (2 * Cs) = (ϕ * ϕ) ^ Cs := by
        rw [Real.mul_rpow hϕ0.le hϕ0.le, ← Real.rpow_add hϕ0]; ring_nf
      rw [h2]
      exact Real.rpow_le_rpow hcp0 h1 hCs.le
    rw [e, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ p
    exact (mul_le_mul_of_nonneg_right hW hS0).trans hB5
  have hint3 : ∫ ω, ‖stieltjesM (symOfEntries ω) z - msc z‖ ^ p ∂L.law ≤ 3 * u ^ p := by
    linarith
  have hmk := nsq_markov L.law hzpos hu0 hint3
  -- outside the Markov event, `Im m < (2Nη)⁻¹`, hence no eigenvalue within `η` of `E`
  have hsubΩ : {ω : Entries N | ∀ α, 1 / (N : ℝ) <
      |(symOfEntries_isHermitian ω).eigenvalues α - E|}ᶜ ⊆
      {ω | 2 * u ≤ ‖stieltjesM (symOfEntries ω) z - msc z‖} := by
    intro ω hω
    by_contra hlt
    apply hω
    intro α
    have hlt' : ‖stieltjesM (symOfEntries ω) z - msc z‖ < 2 * u := not_le.mp hlt
    have hIm : (stieltjesM (symOfEntries ω) (E + η * Complex.I)).im < 1 / (2 * N * η) := by
      have ez : (E : ℂ) + η * Complex.I = z := Complex.ext (by simp [hzre]) (by simp [hzim])
      rw [ez]
      have h1 : (stieltjesM (symOfEntries ω) z).im =
          (msc z).im + (stieltjesM (symOfEntries ω) z - msc z).im := by simp
      have h2 := Complex.im_le_norm (stieltjesM (symOfEntries ω) z - msc z)
      have h3 : 1 / (2 * N * η) = 5 * u / 2 := by rw [hu]; field_simp
      rw [h1, h3]
      linarith
    have := lt_abs_eigenvalues_sub_of_im_stieltjesM_lt (symOfEntries_isHermitian ω) hη0 hIm α
    linarith
  calc L.law _ ≤ L.law {ω | 2 * u ≤ ‖stieltjesM (symOfEntries ω) z - msc z‖} :=
        measure_mono hsubΩ
    _ ≤ ENNReal.ofReal (3 / 2 ^ p) := hmk
    _ ≤ _ := ENNReal.ofReal_le_ofReal (nsq_prob (N := N) (by omega) hp2)

/-- (5.17): with high probability no eigenvalue of `H` lies in `[2 + φ^C N^{-2/3}, 3]`, by a union
bound over the grid `E_k = 2 + φ^C N^{-2/3} + k/N`, `k < N`. -/
private lemma nsq_upper {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ C > (0 : ℝ), HighProbOn 1 (SmallQClass C1 φs)
      (fun N _ => {ω | ∀ α, (symOfEntries_isHermitian ω).eigenvalues α ≤ 3 →
        (symOfEntries_isHermitian ω).eigenvalues α <
          2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)}) := by
  obtain ⟨K, hK, hO⟩ := outOfSpectrum (ζ := 4) (C0 := max C1 1) (c := 1) (φs := 2 / 5)
    (by norm_num) (le_max_of_le_right zero_le_one) one_pos (by norm_num)
  obtain ⟨C0m, hC0m, hMC⟩ := moment_comparison (C1 := C1) (φq := min φs (1 / 4))
    (lt_min hφs (by norm_num))
  obtain ⟨Cs, hCs, Nm, hMC⟩ := hMC 1 one_pos 1 one_pos
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  have hmsc' : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → z.im ≤ kappa z.re → 2 ≤ |z.re| →
      (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im)) :=
    fun z h1 h2 h3 h4 h5 => ((hmsc z h1 h2 h3).2.2.1 h4 h5).2
  obtain ⟨Co, hCo, co, hco, Co', hCo', No, hO⟩ := hO (49 + 3 * Cs + C0m) (by linarith)
  refine ⟨Co + 2 * K + 3 * (49 + 3 * Cs + C0m) + 2, by positivity, ?_⟩
  set Ct : ℝ := Co + 2 * K + 3 * (49 + 3 * Cs + C0m) + 2 with hCt
  set bN : ℕ → ℝ := fun N => 2 + phi N ^ Ct * (N : ℝ) ^ (-(2 : ℝ) / 3) with hbN
  have hgrid : HighProbOn 1 (SmallQClass C1 φs) (fun N _ => ⋂ k : Fin N,
      {ω : Entries N | bN N + (k : ℝ) / N ≤ 3 → ∀ α, 1 / (N : ℝ) <
        |(symOfEntries_isHermitian ω).eigenvalues α - (bN N + (k : ℝ) / N)|}) := by
    refine HighProbOn.iInter (ι := fun N => Fin N) (K := 1) (fun N => by simp) ?_
    obtain ⟨Nl, hNl⟩ := eventually_atTop.1 ((eventually_ge_atTop (max (max Nm No) 16)).and <|
      (nsq_eventually_phi (16 + 10 * Cm + Cs + (Co' + 2) / co)).and
        (nsq_eventually_tilde ((2 * C1 + 4) * C1)))
    refine ⟨Real.log 2, Real.log_pos one_lt_two, 1, one_pos, Nl, fun N hN k L hL => ?_⟩
    obtain ⟨hNmax, hϕT, htil⟩ := hNl N hN
    have hNm : Nm ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNmax
    have hNo : No ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNmax
    have h16 : 16 ≤ N := le_trans (le_max_right _ _) hNmax
    change L.law {ω : Entries N | bN N + (k : ℝ) / N ≤ 3 → ∀ α, 1 / (N : ℝ) <
        |(symOfEntries_isHermitian ω).eigenvalues α - (bN N + (k : ℝ) / N)|}ᶜ ≤ _
    by_cases hE3 : bN N + (k : ℝ) / N ≤ 3
    · have hbE : bN N ≤ bN N + (k : ℝ) / N := le_add_of_nonneg_right (by positivity)
      exact le_trans (measure_mono (Set.compl_subset_compl.2 fun ω h _ => h))
        (nsq_point hK hCs hCm hC0m hCo hco hCo' rfl hCt hmsc' (fun Lw hLw => hO N hNo Lw hLw)
          (hMC N hNm) h16 hϕT htil hL hbE hE3)
    · refine le_trans (measure_mono (μ := L.law) (t := ∅) fun ω hω =>
        (hω fun h => absurd h hE3).elim) ?_
      simp
  refine nsq_mono hgrid (fun _ _ h => h) 3 fun N hN L _ ω hω α hα => ?_
  have hN0 : 0 < N := by omega
  have hb : 2 < bN N := by
    have h1 : 0 < phi N := by rw [phi_eq_exp hN]; exact Real.exp_pos _
    have h2 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN0) _
    have := mul_pos (Real.rpow_pos_of_pos h1 Ct) h2
    simp only [hbN]
    linarith
  exact nsq_grid hN0 hb (fun k hk => Set.mem_iInter.1 hω k hk α) hα

/-! ### (5.16) on the class of Theorem 3.6 -/

/-- (5.16) on the class of Theorem 3.6: `|λ_α| ≤ 3` for all `α` with high probability. -/
private lemma nsq_norm_three {C1 φs : ℝ} (hφs : 0 < φs) :
    HighProbOn 1 (SmallQClass C1 φs)
      (fun _ _ => {ω | ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3}) := by
  obtain ⟨Cn, hCn, hnorm⟩ := norm_le_two_add (ζ := 1) (C0 := max C1 1) (c := 1) one_pos
    (le_max_of_le_right zero_le_one) one_pos
  set c : ℝ := min φs (1 / 3) with hc
  have hc0 : 0 < c := lt_min hφs (by norm_num)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 ((phi_rpow_le_rpow Cn hc0).and <|
    (((tendsto_rpow_atTop hc0).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2).and
      (eventually_ge_atTop 1))
  refine nsq_mono hnorm (fun _ _ h => h.1.isGenWigner) N1 fun N hN L hL ω hω α => ?_
  obtain ⟨hϕ, hx2, h1⟩ := hN1 N hN
  simp only [Function.comp] at hx2
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast h1
  have hN0r : (0 : ℝ) < N := by linarith
  set x : ℝ := (N : ℝ) ^ c with hx
  have hx0 : 0 < x := by linarith
  have hxφ : x ≤ (N : ℝ) ^ φs := Real.rpow_le_rpow_of_exponent_le hN1r (min_le_left _ _)
  have hS := hω ((N : ℝ) ^ φs) ⟨hϕ.trans hxφ, hL.2.boundedSupport 1, hL.2.tailVarOff 1⟩
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues (symOfEntries_isHermitian ω)
  rw [hσ]
  refine (hS (σ α)).trans ?_
  have h23 : (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 / x ^ 2 := by
    have e : 1 / x ^ 2 = (N : ℝ) ^ (-(c * 2)) := by
      rw [Real.rpow_neg hN0r.le, show c * 2 = c * ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_mul_natCast hN0r.le, one_div]
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by rw [hc]; linarith [min_le_right φs (1 / 3)])
  have hq : 1 / ((N : ℝ) ^ φs) ^ 2 ≤ 1 / x ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hx0.le hxφ 2)
  have hsum : phi N ^ Cn * (1 / ((N : ℝ) ^ φs) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) ≤ 1 := by
    calc phi N ^ Cn * (1 / ((N : ℝ) ^ φs) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3))
        ≤ x * (1 / x ^ 2 + 1 / x ^ 2) :=
          mul_le_mul hϕ (add_le_add hq h23) (by positivity) hx0.le
      _ = 2 / x := by field_simp; ring
      _ ≤ 1 := by rw [div_le_one hx0]; exact hx2
  linarith

/-! ### (5.17) and (5.23) -/

/-- (5.17) and (5.23): `‖H‖ ≤ 2 + φ^C N^{-2/3}` with high probability. -/
theorem abs_eigenvalues_le_smallQ {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ C > (0 : ℝ), HighProbOn 1 (SmallQClass C1 φs)
      (fun N _ => {ω | ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤
        2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)}) := by
  obtain ⟨C, hC, hup⟩ := nsq_upper (C1 := C1) hφs
  refine ⟨C, hC, ?_⟩
  have hlow := nsq_highProb_neg hup
  refine HighProbOn.mono ((nsq_norm_three (C1 := C1) hφs).inter (hup.inter hlow))
    fun N L ω hω α => ?_
  obtain ⟨h3, hu, hl⟩ := hω
  have h3α := abs_le.mp (h3 α)
  obtain ⟨β, hβ⟩ := nsq_exists_eig_neg (symOfEntries_isHermitian ω)
    (symOfEntries_isHermitian (-ω)) (nsq_symOfEntries_neg ω) α
  have hU := hu α h3α.2
  have hL := hl β (by rw [hβ]; linarith)
  rw [hβ] at hL
  rw [abs_le]
  constructor <;> linarith

/-! ### Compiled checks -/

open private expansion_matchedPair_radLaws from WEdgeNS.Comparison.Expansion
open private lawV lawV_momentCond lawV_supp from WEdgeNS.Comparison.Classes
open private oos_window_inst from WEdgeNS.LocalLaw.OutOfSpectrum

/-- For all large `N` the Rademacher laws `±N^{-1/2}` (diagonal `±(2/N)^{1/2}`) lie in the class
of Theorem 3.6 with `C1 = 2` and `φs = 1/4`. -/
private lemma nsq_radLaws_class : ∀ᶠ N : ℕ in atTop, SmallQClass 2 (1 / 4) N (radLaws N) := by
  filter_upwards [expansion_matchedPair_radLaws, eventually_ge_atTop 32] with N hmp h32
  have hN0 : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hsupp := radLaws_boundedSupportAS h32
  have hint := hsupp.integrable_pow hmp.isProb_v
  have hq : (0 : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hle : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hmono : ∀ μ : Measure ℝ, μ {x | ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ < |x|} = 0 →
      μ {x | ((N : ℝ) ^ (1 / 4 : ℝ))⁻¹ < |x|} = 0 := fun μ h =>
    measure_mono_null (fun _ hx => lt_of_le_of_lt (inv_anti₀ hq hle) hx) h
  refine ⟨⟨hmp.isProb_v, (hint 2).1, (hint 4).2, hmp.mean_diag, hmp.mean_off, hmp.var_diag_le,
    hmp.var_off, fun p => ?_, hmp.fourth_off_le⟩,
    ⟨fun i => hmono _ (hsupp.1 i), fun p => hmono _ (hsupp.2 p)⟩⟩
  rw [integral_abs_pow_three_radLaws_off hN0 p]
  have : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
  linarith

/-- The class of `abs_eigenvalues_le_smallQ` is nonempty for all large `N`: it contains the
Rademacher laws, with `C1 = 2` and `φs = 1/4 < 1/3`. -/
example : ∀ᶠ N : ℕ in atTop, ∃ L : EntryLaws N, SmallQClass 2 (1 / 4) N L := by
  filter_upwards [nsq_radLaws_class] with N h
  exact ⟨_, h⟩

/-- A law of the class at `N = 16`, `C1 = 2`, `φs = 1/4` whose off-diagonal entries take the
extreme values `±N^{-1/4} = ±1/2` with probability `1/5`. -/
example : SmallQClass 2 (1 / 4) 16 lawV := ⟨lawV_momentCond, lawV_supp⟩

/-- `abs_eigenvalues_le_smallQ` at `C1 = 2`, `φs = 1/4` for the Rademacher laws: for all large `N`
the laws lie in the class, the bound `2 + φ^C N^{-2/3}` lies in `(2, 5/2]`, and the probability
bound of the theorem applies to them. -/
example : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C' : ℕ, ∀ᶠ N : ℕ in atTop,
    SmallQClass 2 (1 / 4) N (radLaws N) ∧
    2 < 2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ∧
    2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 5 / 2 ∧
    (radLaws N).law {ω | ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤
        2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨C, hC, c, hc, C', -, N0, h⟩ :=
    abs_eigenvalues_le_smallQ (C1 := 2) (φs := 1 / 4) (by norm_num)
  refine ⟨C, hC, c, hc, C', ?_⟩
  filter_upwards [nsq_radLaws_class, eventually_ge_atTop N0, oos_window_inst C,
    eventually_ge_atTop 3] with N hcl hN hw h3
  have h1 : 0 < phi N := by rw [phi_eq_exp h3]; exact Real.exp_pos _
  have h2 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  exact ⟨hcl, by linarith [mul_pos (Real.rpow_pos_of_pos h1 C) h2], hw, h N hN _ hcl⟩

#print axioms abs_eigenvalues_le_smallQ

end WEdgeNS
