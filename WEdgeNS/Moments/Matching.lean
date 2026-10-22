import WEdgeNS.Model.General

/-!
# Lemma 5.2, Remark 5.3 and Lemma 5.1 (moment matching)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-! ### Finitely supported laws -/

/-- The finitely supported measure `∑ i, c i • δ_{z i}` with weights `c`. -/
private def atomLaw {ι : Type*} [Fintype ι] (c z : ι → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (c i) • Measure.dirac (z i)

private lemma atomLaw_integrable {ι : Type*} [Fintype ι] (c z : ι → ℝ) (f : ℝ → ℝ) :
    Integrable f (atomLaw c z) := by
  unfold atomLaw
  refine integrable_finsetSum_measure.mpr fun i _ => ?_
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma atomLaw_integral {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (z : ι → ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(atomLaw c z) = ∑ i, c i * f (z i) := by
  unfold atomLaw
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc i), smul_eq_mul]

private lemma atomLaw_isProb {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h1 : ∑ i, c i = 1) (z : ι → ℝ) : IsProbabilityMeasure (atomLaw c z) := by
  refine ⟨?_⟩
  unfold atomLaw
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hc i), h1, ENNReal.ofReal_one]

private lemma atomLaw_null {ι : Type*} [Fintype ι] (c z : ι → ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (h : ∀ i, z i ∉ S) : atomLaw c z S = 0 := by
  unfold atomLaw
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [Measure.smul_apply, Measure.dirac_apply' _ hS, h i]

/-! ### Laws with prescribed moments -/

/-- A probability law supported in `[-R, R]`, with finite moments of every order, and
moments `0, 1, A, B` of orders `1, 2, 3, 4`. -/
private structure Std4 (μ : Measure ℝ) (R A B : ℝ) : Prop where
  prob : IsProbabilityMeasure μ
  supp : μ (Set.Icc (-R) R)ᶜ = 0
  int : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ
  m1 : ∫ x, x ∂μ = 0
  m2 : ∫ x, x ^ 2 ∂μ = 1
  m3 : ∫ x, x ^ 3 ∂μ = A
  m4 : ∫ x, x ^ 4 ∂μ = B

private lemma Std4.mono {μ : Measure ℝ} {R R' A B : ℝ} (h : Std4 μ R A B) (hR : R ≤ R') :
    Std4 μ R' A B :=
  { h with
    supp := measure_mono_null
      (Set.compl_subset_compl.mpr (Set.Icc_subset_Icc (neg_le_neg hR) hR)) h.supp }

private lemma Std4.mix {μ₁ μ₂ : Measure ℝ} {R A B₁ B₂ θ : ℝ} (h₁ : Std4 μ₁ R A B₁)
    (h₂ : Std4 μ₂ R A B₂) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Std4 (ENNReal.ofReal θ • μ₁ + ENNReal.ofReal (1 - θ) • μ₂) R A (θ * B₁ + (1 - θ) * B₂) := by
  have hθ' : 0 ≤ 1 - θ := by linarith
  have hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k)
      (ENNReal.ofReal θ • μ₁ + ENNReal.ofReal (1 - θ) • μ₂) := fun k =>
    ((h₁.int k).smul_measure ENNReal.ofReal_ne_top).add_measure
      ((h₂.int k).smul_measure ENNReal.ofReal_ne_top)
  have hmix : ∀ f : ℝ → ℝ, Integrable f μ₁ → Integrable f μ₂ →
      ∫ x, f x ∂(ENNReal.ofReal θ • μ₁ + ENNReal.ofReal (1 - θ) • μ₂) =
        θ * ∫ x, f x ∂μ₁ + (1 - θ) * ∫ x, f x ∂μ₂ := fun f hf₁ hf₂ => by
    rw [integral_add_measure (hf₁.smul_measure ENNReal.ofReal_ne_top)
      (hf₂.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal hθ0, ENNReal.toReal_ofReal hθ', smul_eq_mul, smul_eq_mul]
  have := h₁.prob
  have := h₂.prob
  refine ⟨⟨?_⟩, ?_, hint, ?_, ?_, ?_, ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hθ0 hθ', add_sub_cancel, ENNReal.ofReal_one]
  · simp [Measure.add_apply, Measure.smul_apply, h₁.supp, h₂.supp]
  · have := hmix (fun x => x) (by simpa using h₁.int 1) (by simpa using h₂.int 1)
    rw [this, h₁.m1, h₂.m1]; ring
  · rw [hmix (fun x => x ^ 2) (h₁.int 2) (h₂.int 2), h₁.m2, h₂.m2]; ring
  · rw [hmix (fun x => x ^ 3) (h₁.int 3) (h₂.int 3), h₁.m3, h₂.m3]; ring
  · rw [hmix (fun x => x ^ 4) (h₁.int 4) (h₂.int 4), h₁.m4, h₂.m4]

/-- Weights `c` and atoms `z` (finitely many) with `|z i| ≤ R` whose power sums of orders
`1, 2, 3, 4` are `m₁, m₂, m₃, m₄`. -/
private structure AtomMom {ι : Type*} [Fintype ι] (c z : ι → ℝ) (R m₁ m₂ m₃ m₄ : ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ c i
  sum_one : ∑ i, c i = 1
  abs_le : ∀ i, |z i| ≤ R
  mom1 : ∑ i, c i * z i ^ 1 = m₁
  mom2 : ∑ i, c i * z i ^ 2 = m₂
  mom3 : ∑ i, c i * z i ^ 3 = m₃
  mom4 : ∑ i, c i * z i ^ 4 = m₄

private lemma AtomMom.of_eq {ι : Type*} [Fintype ι] {c z : ι → ℝ}
    {R m₁ m₂ m₃ m₄ n₁ n₂ n₃ n₄ : ℝ} (h : AtomMom c z R m₁ m₂ m₃ m₄) (e₁ : m₁ = n₁)
    (e₂ : m₂ = n₂) (e₃ : m₃ = n₃) (e₄ : m₄ = n₄) : AtomMom c z R n₁ n₂ n₃ n₄ := by
  subst e₁ e₂ e₃ e₄; exact h

private lemma AtomMom.std4 {ι : Type*} [Fintype ι] {c z : ι → ℝ} {R A B : ℝ}
    (h : AtomMom c z R 0 1 A B) : Std4 (atomLaw c z) R A B := by
  refine ⟨atomLaw_isProb h.nonneg h.sum_one z, ?_, fun k => atomLaw_integrable _ _ _,
    ?_, ?_, ?_, ?_⟩
  · exact atomLaw_null _ _ measurableSet_Icc.compl fun i => by
      simpa only [Set.mem_compl_iff, not_not, Set.mem_Icc] using _root_.abs_le.mp (h.abs_le i)
  · rw [atomLaw_integral h.nonneg]; simpa using h.mom1
  · rw [atomLaw_integral h.nonneg]; exact h.mom2
  · rw [atomLaw_integral h.nonneg]; exact h.mom3
  · rw [atomLaw_integral h.nonneg]; exact h.mom4

/-- The two-point law on `u < v` with `u v = -1`: weights `v / (v - u)` and `-u / (v - u)`
give moments `0, 1, u + v, (u + v)² + 1`. -/
private lemma atomMom_twoPt {u v R : ℝ} (huv : u * v = -1) (hlt : u < v) (hu : |u| ≤ R)
    (hv : |v| ≤ R) :
    AtomMom ![v / (v - u), -u / (v - u)] ![u, v] R 0 1 (u + v) ((u + v) ^ 2 + 1) := by
  have hu0 : u < 0 := by
    by_contra h
    nlinarith [mul_nonneg (not_lt.mp h) (by linarith : 0 ≤ v)]
  have hv0 : 0 < v := by
    by_contra h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hu0.le (not_lt.mp h)]
  have hd : 0 < v - u := by linarith
  refine ⟨Fin.forall_fin_two.mpr ⟨div_nonneg hv0.le hd.le, div_nonneg (by linarith) hd.le⟩,
    ?_, Fin.forall_fin_two.mpr ⟨hu, hv⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · field_simp; ring
  · field_simp; ring
  · field_simp
    linear_combination (u - v) * huv
  · field_simp
    linear_combination (u ^ 2 - v ^ 2) * huv
  · field_simp
    linear_combination (u - v) * (u ^ 2 + u * v + v ^ 2 + 1) * huv

/-- For every `s` there are `u < v` with `u v = -1`, `u + v = s` and `|u|, |v| ≤ |s| + 1`. -/
private lemma exists_two_atoms (s : ℝ) :
    ∃ u v : ℝ, u * v = -1 ∧ u < v ∧ u + v = s ∧ |u| ≤ |s| + 1 ∧ |v| ≤ |s| + 1 := by
  have hr : Real.sqrt (s ^ 2 + 4) ^ 2 = s ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hr0 : 0 < Real.sqrt (s ^ 2 + 4) := Real.sqrt_pos.mpr (by positivity)
  have hrle : Real.sqrt (s ^ 2 + 4) ≤ |s| + 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_abs s, abs_nonneg s]⟩
  refine ⟨(s - Real.sqrt (s ^ 2 + 4)) / 2, (s + Real.sqrt (s ^ 2 + 4)) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · linarith
  · ring
  · exact abs_le.mpr ⟨by linarith [neg_abs_le s, le_abs_self s],
      by linarith [neg_abs_le s, le_abs_self s]⟩
  · exact abs_le.mpr ⟨by linarith [neg_abs_le s, le_abs_self s],
      by linarith [neg_abs_le s, le_abs_self s]⟩

/-- A symmetric four-atom law with moments `0, 1, 0, t` of orders `1, 2, 3, 4` and atoms in
`[-t, t]` (`t ≥ 1`): mass `p` at `±t` and `1/2 - p` at `±√(t/(1+t))`, where
`p = 1 / (2 t (t² + t - 1))`. -/
private lemma exists_atomMom_symm {t : ℝ} (ht : 1 ≤ t) :
    ∃ c z : Fin 4 → ℝ, AtomMom c z t 0 1 0 t := by
  have ht0 : 0 < t := by linarith
  have hD : 0 < t ^ 2 + t - 1 := by nlinarith
  have hq0 : 0 < t / (1 + t) := by positivity
  have hs2 : Real.sqrt (t / (1 + t)) ^ 2 = t / (1 + t) := Real.sq_sqrt hq0.le
  have hs4 : Real.sqrt (t / (1 + t)) ^ 4 = (t / (1 + t)) ^ 2 := by
    rw [show Real.sqrt (t / (1 + t)) ^ 4 = (Real.sqrt (t / (1 + t)) ^ 2) ^ 2 by ring, hs2]
  have hp0 : 0 < 1 / (2 * t * (t ^ 2 + t - 1)) := by positivity
  have hp1 : 1 / (2 * t * (t ^ 2 + t - 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg (t + 1))]
  have hsle : Real.sqrt (t / (1 + t)) ≤ t :=
    Real.sqrt_le_iff.mpr ⟨ht0.le, by
      rw [div_le_iff₀ (by positivity)]; nlinarith⟩
  have hD' : t ^ 2 + t - 1 ≠ 0 := hD.ne'
  have ht1 : 1 + t ≠ 0 := by positivity
  have ht' : t ≠ 0 := ht0.ne'
  have hex : ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 / 2 ∧
      2 * p * t ^ 2 + (1 - 2 * p) * (t / (1 + t)) = 1 ∧
      2 * p * t ^ 4 + (1 - 2 * p) * (t / (1 + t)) ^ 2 = t := by
    obtain ⟨D, hDd⟩ : ∃ D, D = t ^ 2 + t - 1 := ⟨_, rfl⟩
    have hD0 : D ≠ 0 := hDd ▸ hD'
    rw [← hDd] at hp0 hp1
    refine ⟨1 / (2 * t * D), hp0.le, hp1, ?_, ?_⟩
    · field_simp
      rw [hDd]; ring
    · field_simp
      rw [hDd]; ring
  obtain ⟨p, hp0, hp1, hm2, hm4⟩ := hex
  generalize hsd : Real.sqrt (t / (1 + t)) = σ at hs2 hs4 hsle
  have hσ0 : 0 ≤ σ := hsd ▸ Real.sqrt_nonneg _
  refine ⟨![p, p, 1 / 2 - p, 1 / 2 - p], ![t, -t, σ, -σ], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_succ]; ring
  · intro i
    fin_cases i
    · simp [abs_of_pos ht0]
    · simp [abs_of_pos ht0]
    · simpa [abs_of_nonneg hσ0] using hsle
    · simpa [abs_of_nonneg hσ0] using hsle
  · simp [Fin.sum_univ_succ]
  · simp [Fin.sum_univ_succ]
    linear_combination hm2 + (1 - 2 * p) * hs2
  · simp [Fin.sum_univ_succ]; ring
  · simp [Fin.sum_univ_succ]
    linear_combination hm4 + (1 - 2 * p) * hs4

private lemma sum_prod_mul_pow {ι κ : Type*} [Fintype ι] [Fintype κ] (w x : ι → ℝ)
    (v y : κ → ℝ) (a b : ℕ) :
    ∑ p : ι × κ, w p.1 * v p.2 * (x p.1 ^ a * y p.2 ^ b) =
      (∑ i, w i * x i ^ a) * (∑ j, v j * y j ^ b) := by
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Independent sum, rescaled: the weights `c i * c' j` at the atoms `(z i + z' j) / d`. -/
private lemma AtomMom.conv {ι κ : Type*} [Fintype ι] [Fintype κ] {c z : ι → ℝ}
    {c' z' : κ → ℝ} {R R' d m₁ m₂ m₃ m₄ n₁ n₂ n₃ n₄ : ℝ} (hd : 0 < d)
    (h : AtomMom c z R m₁ m₂ m₃ m₄) (h' : AtomMom c' z' R' n₁ n₂ n₃ n₄) :
    AtomMom (fun p : ι × κ => c p.1 * c' p.2) (fun p => (z p.1 + z' p.2) / d) ((R + R') / d)
      ((m₁ + n₁) / d) ((m₂ + 2 * m₁ * n₁ + n₂) / d ^ 2)
      ((m₃ + 3 * m₂ * n₁ + 3 * m₁ * n₂ + n₃) / d ^ 3)
      ((m₄ + 4 * m₃ * n₁ + 6 * m₂ * n₂ + 4 * m₁ * n₃ + n₄) / d ^ 4) := by
  have hk : ∀ k : ℕ, ∑ p : ι × κ, c p.1 * c' p.2 * ((z p.1 + z' p.2) / d) ^ k =
      (∑ p : ι × κ, c p.1 * c' p.2 * (z p.1 + z' p.2) ^ k) / d ^ k := fun k => by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by rw [div_pow]; ring
  have h0 : ∑ i, c i * z i ^ 0 = 1 := by simpa using h.sum_one
  have h0' : ∑ j, c' j * z' j ^ 0 = 1 := by simpa using h'.sum_one
  have h1 := h.mom1
  have h1' := h'.mom1
  refine ⟨fun p => mul_nonneg (h.nonneg _) (h'.nonneg _), ?_, fun p => ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, h.sum_one, h'.sum_one, mul_one]
  · rw [abs_div, abs_of_pos hd]
    exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add (h.abs_le _)
      (h'.abs_le _))) hd.le
  · rw [hk]
    have e : ∀ p : ι × κ, c p.1 * c' p.2 * (z p.1 + z' p.2) ^ 1 =
        c p.1 * c' p.2 * (z p.1 ^ 1 * z' p.2 ^ 0) + c p.1 * c' p.2 * (z p.1 ^ 0 * z' p.2 ^ 1) :=
      fun p => by ring
    rw [Finset.sum_congr rfl fun p _ => e p]
    simp only [Finset.sum_add_distrib, sum_prod_mul_pow, h0, h0', h1, h1', mul_one, one_mul]
    simp
  · rw [hk]
    have e : ∀ p : ι × κ, c p.1 * c' p.2 * (z p.1 + z' p.2) ^ 2 =
        c p.1 * c' p.2 * (z p.1 ^ 2 * z' p.2 ^ 0) +
        2 * (c p.1 * c' p.2 * (z p.1 ^ 1 * z' p.2 ^ 1)) +
        c p.1 * c' p.2 * (z p.1 ^ 0 * z' p.2 ^ 2) := fun p => by ring
    rw [Finset.sum_congr rfl fun p _ => e p]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_prod_mul_pow, h0, h0', h1, h1',
      h.mom2, h'.mom2, mul_one, one_mul]
    ring
  · rw [hk]
    have e : ∀ p : ι × κ, c p.1 * c' p.2 * (z p.1 + z' p.2) ^ 3 =
        c p.1 * c' p.2 * (z p.1 ^ 3 * z' p.2 ^ 0) +
        3 * (c p.1 * c' p.2 * (z p.1 ^ 2 * z' p.2 ^ 1)) +
        3 * (c p.1 * c' p.2 * (z p.1 ^ 1 * z' p.2 ^ 2)) +
        c p.1 * c' p.2 * (z p.1 ^ 0 * z' p.2 ^ 3) := fun p => by ring
    rw [Finset.sum_congr rfl fun p _ => e p]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_prod_mul_pow, h0, h0', h1, h1',
      h.mom2, h'.mom2, h.mom3, h'.mom3, mul_one, one_mul]
    ring
  · rw [hk]
    have e : ∀ p : ι × κ, c p.1 * c' p.2 * (z p.1 + z' p.2) ^ 4 =
        c p.1 * c' p.2 * (z p.1 ^ 4 * z' p.2 ^ 0) +
        4 * (c p.1 * c' p.2 * (z p.1 ^ 3 * z' p.2 ^ 1)) +
        6 * (c p.1 * c' p.2 * (z p.1 ^ 2 * z' p.2 ^ 2)) +
        4 * (c p.1 * c' p.2 * (z p.1 ^ 1 * z' p.2 ^ 3)) +
        c p.1 * c' p.2 * (z p.1 ^ 0 * z' p.2 ^ 4) := fun p => by ring
    rw [Finset.sum_congr rfl fun p _ => e p]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_prod_mul_pow, h0, h0', h1, h1',
      h.mom2, h'.mom2, h.mom3, h'.mom3, h.mom4, h'.mom4, mul_one, one_mul]
    ring

/-- The construction of (5.8)–(5.9) combined with the symmetric law of
`exists_atomMom_symm` (`x = (X + Y) / √2`, `X` and `Y` independent): moments
`0, 1, A, (8 A² + 7 + t) / 4`. -/
private lemma exists_std4_indep_sum (A : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ∃ μ : Measure ℝ, Std4 μ ((2 * Real.sqrt 2 * |A| + 1 + t) / Real.sqrt 2) A
      ((8 * A ^ 2 + 7 + t) / 4) := by
  have hd0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hd2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨u, v, huv, hlt, hsum, hu, hv⟩ := exists_two_atoms (2 * Real.sqrt 2 * A)
  obtain ⟨c, z, hY⟩ := exists_atomMom_symm ht
  have hX := atomMom_twoPt huv hlt hu hv
  have hc := hX.conv hd0 hY
  have habs : |2 * Real.sqrt 2 * A| = 2 * Real.sqrt 2 * |A| := by
    rw [abs_mul, abs_mul, abs_of_pos hd0, abs_two]
  rw [habs] at hc
  rw [hsum] at hc
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, hd2]
  have h4 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, hd2]; norm_num
  refine ⟨_, (hc.of_eq (by ring) ?_ ?_ ?_).std4⟩
  · rw [hd2]; norm_num
  · rw [h3]; field_simp; ring
  · rw [h4]
    have : (2 * Real.sqrt 2 * A) ^ 2 = 8 * A ^ 2 := by
      rw [mul_pow, mul_pow, hd2]; ring
    rw [this]; ring

/-- A probability law with integrable fourth power has integrable powers of order `k ≤ 4`. -/
private lemma integrable_pow_of_four (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h4 : Integrable (fun x : ℝ => x ^ 4) μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun x : ℝ => x ^ k) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h4)
    (continuous_pow k).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have h4' : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  change |x| ^ k ≤ 1 + x ^ 4
  rcases le_total |x| 1 with h | h
  · have := pow_le_one₀ (abs_nonneg x) h (n := k)
    nlinarith [sq_nonneg (x ^ 2)]
  · have := pow_le_pow_right₀ h hk
    rw [h4'] at this
    linarith


/-! ### Auxiliary facts for the matching lemma -/

private lemma rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 : ℝ) / 2) = ((Real.sqrt x)⁻¹) ^ 3 := by
  rw [show -(3 : ℝ) / 2 = (1 / 2) * (-(3 : ℕ) : ℝ) by norm_num, Real.rpow_mul hx.le,
    ← Real.sqrt_eq_rpow, Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast, inv_pow]

private lemma one_lt_log_of_three_le {N : ℕ} (hN : 3 ≤ N) : 1 < Real.log N := by
  have hNr3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num)
  exact h3.trans_le (Real.log_le_log (by norm_num) hNr3)

private lemma integral_map_mul_pow (c : ℝ) (μ : Measure ℝ) (k : ℕ) :
    ∫ x, x ^ k ∂(μ.map (fun x => c * x)) = c ^ k * ∫ x, x ^ k ∂μ := by
  have hm : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  rw [integral_map hm.aemeasurable (continuous_pow k).aestronglyMeasurable]
  simp_rw [mul_pow]
  exact integral_const_mul _ _

/-- If `x²` has mean `N⁻¹` and `|x|³` has mean at most `C1 N^{-3/2}`, then `C1 ≥ 1`
(Lyapunov: `E|x|³ ≥ (E x²)^{3/2}`, via the tangent line of `u ↦ u^{3/2}`). -/
private lemma one_le_of_third_moment {N : ℕ} (hN : 0 < N) {C1 : ℝ} (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (h4 : Integrable (fun x : ℝ => x ^ 4) μ)
    (h2 : ∫ x, x ^ 2 ∂μ = (N : ℝ)⁻¹)
    (h3 : ∫ x, |x| ^ 3 ∂μ ≤ C1 * (N : ℝ) ^ (-(3 : ℝ) / 2)) : 1 ≤ C1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  obtain ⟨a, ha⟩ : ∃ a, a = (Real.sqrt N)⁻¹ := ⟨_, rfl⟩
  have ha0 : 0 < a := ha ▸ inv_pos.mpr hd
  have ha2 : a ^ 2 = (N : ℝ)⁻¹ := by
    rw [ha, inv_pow, Real.sq_sqrt hNr.le]
  rw [rpow_neg_three_halves hNr, ← ha] at h3
  have i2 := integrable_pow_of_four μ h4 (k := 2) (by norm_num)
  have i3 : Integrable (fun x : ℝ => |x| ^ 3) μ := by
    simpa [abs_pow] using (integrable_pow_of_four μ h4 (k := 3) (by norm_num)).abs
  have hpt : ∀ x : ℝ, 3 / 2 * a * x ^ 2 - a ^ 3 / 2 ≤ |x| ^ 3 := fun x => by
    have h : 0 ≤ (|x| - a) ^ 2 * (|x| + a / 2) := by positivity
    rw [show (|x| - a) ^ 2 * (|x| + a / 2) = |x| ^ 3 - 3 / 2 * a * |x| ^ 2 + a ^ 3 / 2 by ring,
      sq_abs] at h
    linarith
  have il : Integrable (fun x : ℝ => 3 / 2 * a * x ^ 2 - a ^ 3 / 2) μ :=
    (i2.const_mul (3 / 2 * a)).sub (integrable_const (a ^ 3 / 2))
  have hint := integral_mono il i3 hpt
  rw [integral_sub (i2.const_mul _) (integrable_const _), integral_const_mul, h2, ← ha2,
    integral_const] at hint
  simp only [probReal_univ, smul_eq_mul, one_mul] at hint
  have hcube : 0 < a ^ 3 := by positivity
  nlinarith

private lemma integrable_pow_four_map (c : ℝ) {μ : Measure ℝ}
    (h4 : Integrable (fun x : ℝ => x ^ 4) μ) :
    Integrable (fun x : ℝ => x ^ 4) (μ.map (fun x => c * x)) := by
  have hm : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  refine (integrable_map_measure (continuous_pow 4).aestronglyMeasurable hm.aemeasurable).mpr ?_
  simpa [Function.comp_def, mul_pow] using h4.const_mul (c ^ 4)


/-- Lemma 5.2: if `|A| ≤ C` and `A² + 1 ≤ B`, there is a probability law supported in
`[-(2C + 4) B, (2C + 4) B]` with moments `0, 1, A, B` of orders `1, 2, 3, 4`. -/
theorem exists_law_four_moments {C A B : ℝ} (hA : |A| ≤ C) (hB : A ^ 2 + 1 ≤ B) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Set.Icc (-((2 * C + 4) * B)) ((2 * C + 4) * B))ᶜ = 0 ∧
      ∫ x, x ∂μ = 0 ∧ ∫ x, x ^ 2 ∂μ = 1 ∧ ∫ x, x ^ 3 ∂μ = A ∧ ∫ x, x ^ 4 ∂μ = B := by
  have hC : 0 ≤ C := (abs_nonneg A).trans hA
  have hB1 : 1 ≤ B := by nlinarith [sq_nonneg A]
  have hd1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hd0 : 0 < Real.sqrt 2 := by linarith
  suffices h : ∃ μ : Measure ℝ, Std4 μ ((2 * C + 4) * B) A B by
    obtain ⟨μ, hμ⟩ := h
    exact ⟨μ, hμ.prob, hμ.supp, hμ.m1, hμ.m2, hμ.m3, hμ.m4⟩
  by_cases hcase : 2 * A ^ 2 + 2 ≤ B
  · obtain ⟨μ, hμ⟩ := exists_std4_indep_sum A (t := 4 * B - 8 * A ^ 2 - 7) (by linarith)
    refine ⟨μ, ?_⟩
    rw [show (8 * A ^ 2 + 7 + (4 * B - 8 * A ^ 2 - 7)) / 4 = B by ring] at hμ
    refine hμ.mono ?_
    rw [div_le_iff₀ hd0]
    nlinarith [mul_nonneg (mul_nonneg hC hd0.le) (sub_nonneg.2 hB1),
      mul_nonneg (sub_nonneg.2 hB1) (sub_nonneg.2 hd1),
      mul_le_mul_of_nonneg_left hA (by linarith : 0 ≤ 2 * Real.sqrt 2), sq_nonneg A]
  · push Not at hcase
    obtain ⟨u, v, huv, hlt, hsum, hu, hv⟩ := exists_two_atoms A
    have hP := (atomMom_twoPt huv hlt hu hv).of_eq rfl rfl hsum (by rw [hsum]) |>.std4
    obtain ⟨ν, hν⟩ := exists_std4_indep_sum A (t := 1) le_rfl
    have hθ : 0 < A ^ 2 + 1 := by positivity
    have hθ0 : 0 ≤ (2 * A ^ 2 + 2 - B) / (A ^ 2 + 1) := div_nonneg (by linarith) hθ.le
    have hθ1 : (2 * A ^ 2 + 2 - B) / (A ^ 2 + 1) ≤ 1 := by
      rw [div_le_one hθ]; linarith
    have hR : 0 ≤ (2 * C + 4) * (B - 1) := mul_nonneg (by linarith) (sub_nonneg.2 hB1)
    have hP' := hP.mono (R' := (2 * C + 4) * B) (by
      have := (abs_nonneg A); nlinarith)
    have hν' := hν.mono (R' := (2 * C + 4) * B) (by
      rw [div_le_iff₀ hd0]
      nlinarith [mul_nonneg hR hd0.le,
        mul_le_mul_of_nonneg_left hA (by linarith : 0 ≤ 2 * Real.sqrt 2)])
    have hm := hP'.mix hν' hθ0 hθ1
    rw [show (2 * A ^ 2 + 2 - B) / (A ^ 2 + 1) * (A ^ 2 + 1) +
      (1 - (2 * A ^ 2 + 2 - B) / (A ^ 2 + 1)) * ((8 * A ^ 2 + 7 + 1) / 4) = B by
        field_simp; ring] at hm
    exact ⟨_, hm⟩


/-- Remark 5.3: a probability law with integrable fourth power, mean `0` and variance `1`
satisfies `(∫ x³)² + 1 ≤ ∫ x⁴`. -/
theorem sq_moment_three_add_one_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h4 : Integrable (fun x : ℝ => x ^ 4) μ) (h1 : ∫ x, x ∂μ = 0) (h2 : ∫ x, x ^ 2 ∂μ = 1) :
    (∫ x, x ^ 3 ∂μ) ^ 2 + 1 ≤ ∫ x, x ^ 4 ∂μ := by
  have i1 : Integrable (fun x : ℝ => x) μ := by
    simpa using integrable_pow_of_four μ h4 (k := 1) (by norm_num)
  have i2 := integrable_pow_of_four μ h4 (k := 2) (by norm_num)
  have i3 := integrable_pow_of_four μ h4 (k := 3) (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ x, x ^ 3 ∂μ := ⟨_, rfl⟩
  rw [← hA]
  have e : (fun x : ℝ => (x ^ 2 - 1 - A * x) ^ 2) =
      fun x => x ^ 4 + (A ^ 2 - 2) * x ^ 2 + (-2 * A) * x ^ 3 + (2 * A) * x + 1 := by
    funext x; ring
  have key : ∫ x, (x ^ 2 - 1 - A * x) ^ 2 ∂μ = (∫ x, x ^ 4 ∂μ) + (A ^ 2 - 2) * 1 +
      (-2 * A) * A + (2 * A) * 0 + 1 := by
    have j2 : Integrable (fun x : ℝ => (A ^ 2 - 2) * x ^ 2) μ := i2.const_mul _
    have j3 : Integrable (fun x : ℝ => (-2 * A) * x ^ 3) μ := i3.const_mul _
    have j1 : Integrable (fun x : ℝ => (2 * A) * x) μ := i1.const_mul _
    have s2 : Integrable (fun x : ℝ => x ^ 4 + (A ^ 2 - 2) * x ^ 2) μ := h4.add j2
    have s3 : Integrable (fun x : ℝ => x ^ 4 + (A ^ 2 - 2) * x ^ 2 + (-2 * A) * x ^ 3) μ :=
      s2.add j3
    have s4 : Integrable
        (fun x : ℝ => x ^ 4 + (A ^ 2 - 2) * x ^ 2 + (-2 * A) * x ^ 3 + (2 * A) * x) μ :=
      s3.add j1
    rw [e, integral_add s4 (integrable_const _), integral_add s3 j1, integral_add s2 j3,
      integral_add h4 j2, integral_const_mul, integral_const_mul, integral_const_mul, h1, h2,
      ← hA]
    simp
  have := integral_nonneg (μ := μ) (f := fun x : ℝ => (x ^ 2 - 1 - A * x) ^ 2)
    (fun x => sq_nonneg _)
  rw [key] at this
  nlinarith


/-- Both regimes of `exists_law_four_moments` are nonempty: `(A, B) = (1, 5)` has
`B ≥ 2A² + 2`, and `(A, B) = (2, 9)` has `A² + 1 ≤ B < 2A² + 2`. -/
example : (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Set.Icc (-((2 * 1 + 4) * 5)) ((2 * 1 + 4) * 5))ᶜ = 0 ∧
      ∫ x, x ∂μ = 0 ∧ ∫ x, x ^ 2 ∂μ = 1 ∧ ∫ x, x ^ 3 ∂μ = 1 ∧ ∫ x, x ^ 4 ∂μ = 5) ∧
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Set.Icc (-((2 * 2 + 4) * 9)) ((2 * 2 + 4) * 9))ᶜ = 0 ∧
      ∫ x, x ∂μ = 0 ∧ ∫ x, x ^ 2 ∂μ = 1 ∧ ∫ x, x ^ 3 ∂μ = 2 ∧ ∫ x, x ^ 4 ∂μ = 9) :=
  ⟨exists_law_four_moments (by norm_num) (by norm_num),
    exists_law_four_moments (by norm_num) (by norm_num)⟩

/-- Lemma 5.1: for `N ≥ 3` and entry laws satisfying the moment conditions with constant `C1`,
there are probability entry laws, supported (almost surely) in `|h| ≤ (2 C1 + 4) C1 log N / √N`,
whose off-diagonal moments of orders `1, …, 4` and diagonal moments of orders `1, 2` agree with
those of the given laws. -/
theorem exists_momentMatched {N : ℕ} (hN : 3 ≤ N) {C1 : ℝ} {L : EntryLaws N}
    (hL : L.MomentCond C1) :
    ∃ L' : EntryLaws N, L'.IsProb ∧
      L'.BoundedSupportAS (Real.sqrt N / ((2 * C1 + 4) * C1 * Real.log N)) ∧
      (∀ p, ∀ k ∈ Finset.Icc 1 4, ∫ x, x ^ k ∂(L'.off p) = ∫ x, x ^ k ∂(L.off p)) ∧
      (∀ i, ∀ k ∈ Finset.Icc 1 2, ∫ x, x ^ k ∂(L'.diag i) = ∫ x, x ^ k ∂(L.diag i)) := by
  have hNr3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : (0 : ℝ) < N := by linarith
  have hlog : 1 < Real.log N := one_lt_log_of_three_le hN
  obtain ⟨d, hd⟩ : ∃ d, d = Real.sqrt N := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ Real.sqrt_pos.mpr hNr
  have hd2 : d ^ 2 = N := hd ▸ Real.sq_sqrt hNr.le
  have hoff : ∀ p, IsProbabilityMeasure (L.off p) := hL.isProb.off
  have hC1 : 1 ≤ C1 := by
    let p₀ : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
    have := hoff p₀
    exact one_le_of_third_moment (by omega) (L.off p₀) (hL.fourth_int_off p₀) (hL.var_off p₀)
      (hL.third_off_le p₀)
  obtain ⟨K, hK⟩ : ∃ K, K = (2 * C1 + 4) * C1 * Real.log N := ⟨_, rfl⟩
  have hK1 : C1 ≤ K := by
    have : 1 ≤ (2 * C1 + 4) * Real.log N := by nlinarith
    rw [hK]; nlinarith
  have hK0 : 0 < K := by linarith
  -- one probability law in the new scale for each off-diagonal entry
  have key : ∀ p : OffDiag N, ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Set.Icc (-K) K)ᶜ = 0 ∧
      ∀ k ∈ Finset.Icc 1 4, ∫ x, x ^ k ∂μ = d ^ k * ∫ x, x ^ k ∂(L.off p) := by
    intro p
    have := hoff p
    have hm : ∀ k, ∫ x, x ^ k ∂((L.off p).map (fun x => d * x)) =
        d ^ k * ∫ x, x ^ k ∂(L.off p) := integral_map_mul_pow d _
    have hm1 : ∫ x, x ∂((L.off p).map (fun x => d * x)) = 0 := by
      have := hm 1
      simp only [pow_one] at this
      rw [this, hL.mean_off p, mul_zero]
    have hm2 : ∫ x, x ^ 2 ∂((L.off p).map (fun x => d * x)) = 1 := by
      rw [hm 2, hL.var_off p, hd2]; field_simp
    have hsq := sq_moment_three_add_one_le _ (integrable_pow_four_map d (hL.fourth_int_off p))
      hm1 hm2
    have hA : |∫ x, x ^ 3 ∂((L.off p).map (fun x => d * x))| ≤ C1 := by
      rw [hm 3, abs_mul, abs_of_pos (pow_pos hd0 3)]
      calc d ^ 3 * |∫ x, x ^ 3 ∂(L.off p)| ≤ d ^ 3 * ∫ x, |x| ^ 3 ∂(L.off p) := by
            gcongr
            have h := abs_integral_le_integral_abs (f := fun x : ℝ => x ^ 3) (μ := L.off p)
            simp only [abs_pow] at h
            exact h
        _ ≤ d ^ 3 * (C1 * (N : ℝ) ^ (-(3 : ℝ) / 2)) := by
            gcongr; exact hL.third_off_le p
        _ = C1 := by
            rw [rpow_neg_three_halves hNr, ← hd]; field_simp
    have hB : ∫ x, x ^ 4 ∂((L.off p).map (fun x => d * x)) ≤ C1 * Real.log N := by
      rw [hm 4]
      calc d ^ 4 * ∫ x, x ^ 4 ∂(L.off p) ≤ d ^ 4 * (C1 * Real.log N / (N : ℝ) ^ 2) := by
            gcongr; exact hL.fourth_off_le p
        _ = C1 * Real.log N := by
            rw [show d ^ 4 = (N : ℝ) ^ 2 by rw [← hd2]; ring]; field_simp
    obtain ⟨μ, hprob, hsupp, h1, h2, h3, h4⟩ := exists_law_four_moments hA hsq
    refine ⟨μ, hprob, measure_mono_null (Set.compl_subset_compl.mpr (Set.Icc_subset_Icc ?_ ?_))
      hsupp, ?_⟩
    · rw [hK]; nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * C1 + 4) (sub_nonneg.2 hB)]
    · rw [hK]; nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * C1 + 4) (sub_nonneg.2 hB)]
    · intro k hk
      rw [Finset.mem_Icc] at hk
      obtain ⟨hk1, hk4⟩ := hk
      interval_cases k
      · simp only [pow_one] at h1 ⊢
        rw [h1, hL.mean_off p, mul_zero]
      · rw [h2, hL.var_off p, hd2]; field_simp
      · rw [h3, hm 3]
      · rw [h4, hm 4]
  choose μ hμprob hμsupp hμmom using key
  have hK2 : C1 ≤ K ^ 2 := by nlinarith
  have hσ : ∀ i, Real.sqrt (∫ x, x ^ 2 ∂(L.diag i)) ≤ K / d := fun i => by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [div_pow, hd2]
    calc ∫ x, x ^ 2 ∂(L.diag i) ≤ C1 / N := hL.var_diag_le i
      _ ≤ K ^ 2 / N := by gcongr
  have hσ0 : ∀ i, 0 ≤ ∫ x, x ^ 2 ∂(L.diag i) := fun i => integral_nonneg fun x => sq_nonneg x
  have hwt : ∀ j : Fin 2, 0 ≤ (![1 / 2, 1 / 2] : Fin 2 → ℝ) j :=
    Fin.forall_fin_two.mpr ⟨by norm_num, by norm_num⟩
  have hw1 : ∑ j, (![1 / 2, 1 / 2] : Fin 2 → ℝ) j = 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
  have hmeas : Measurable (fun x : ℝ => d⁻¹ * x) := measurable_const.mul measurable_id
  refine ⟨⟨fun i => atomLaw ![1 / 2, 1 / 2] ![Real.sqrt (∫ x, x ^ 2 ∂(L.diag i)),
    -Real.sqrt (∫ x, x ^ 2 ∂(L.diag i))], fun p => (μ p).map (fun x => d⁻¹ * x)⟩,
    ⟨fun i => atomLaw_isProb hwt hw1 _, fun p => ?_⟩, ⟨fun i => ?_, fun p => ?_⟩,
    fun p k hk => ?_, fun i k hk => ?_⟩
  · have := hμprob p
    exact inferInstance
  · rw [← hd, ← hK, inv_div]
    refine atomLaw_null _ _ (measurableSet_lt measurable_const measurable_abs) fun j => ?_
    have := hσ i
    intro hlt
    fin_cases j
    · have hlt' : K / d < |Real.sqrt (∫ x, x ^ 2 ∂(L.diag i))| := hlt
      rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hlt'; linarith
    · have hlt' : K / d < |-Real.sqrt (∫ x, x ^ 2 ∂(L.diag i))| := hlt
      rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)] at hlt'; linarith
  · rw [← hd, ← hK, inv_div]
    change ((μ p).map (fun x => d⁻¹ * x)) {x : ℝ | K / d < |x|} = 0
    rw [Measure.map_apply hmeas (measurableSet_lt measurable_const measurable_abs)]
    refine measure_mono_null (fun y hy => ?_) (hμsupp p)
    intro hmem
    have hy' : K / d < |d⁻¹ * y| := hy
    rw [abs_mul, abs_inv, abs_of_pos hd0] at hy'
    have h1 : d⁻¹ * |y| ≤ K / d := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (_root_.abs_le.mpr hmem) (inv_nonneg.mpr hd0.le)
    linarith
  · have := hμprob p
    change ∫ x, x ^ k ∂((μ p).map (fun x => d⁻¹ * x)) = _
    rw [integral_map_mul_pow, hμmom p k hk, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hd0.ne',
      one_pow, one_mul]
  · rw [Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    dsimp only
    rw [atomLaw_integral hwt]
    interval_cases k
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_one,
        hL.mean_diag i]
      ring
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, neg_sq,
        Real.sq_sqrt (hσ0 i)]
      ring


/-! ### Compiled instances -/

/-- Remark 5.3 for the law with masses `1/3, 1/2, 1/6` at `-1, 0, 2`: mean `0`, variance `1`,
third moment `1`, fourth moment `3`, so `(∫ x³)² + 1 = 2 ≤ 3 = ∫ x⁴`. -/
example : (∫ x, x ^ 3 ∂(atomLaw ![1 / 3, 1 / 2, 1 / 6] ![-1, 0, 2])) ^ 2 + 1 ≤
      ∫ x, x ^ 4 ∂(atomLaw ![1 / 3, 1 / 2, 1 / 6] ![-1, 0, 2]) ∧
    ∫ x, x ^ 3 ∂(atomLaw ![1 / 3, 1 / 2, 1 / 6] ![-1, 0, 2]) = 1 ∧
    ∫ x, x ^ 4 ∂(atomLaw ![1 / 3, 1 / 2, 1 / 6] ![-1, 0, 2]) = 3 := by
  have hc : ∀ j : Fin 3, 0 ≤ (![1 / 3, 1 / 2, 1 / 6] : Fin 3 → ℝ) j := by
    intro j; fin_cases j <;> norm_num
  have hsum : ∑ j, (![1 / 3, 1 / 2, 1 / 6] : Fin 3 → ℝ) j = 1 := by
    simp [Fin.sum_univ_succ]; norm_num
  have := atomLaw_isProb hc hsum ![-1, 0, 2]
  have e1 : ∫ x, x ∂(atomLaw ![1 / 3, 1 / 2, 1 / 6] ![-1, 0, 2]) = 0 := by
    rw [atomLaw_integral hc]; simp [Fin.sum_univ_succ]; norm_num
  have e2 : ∫ x, x ^ 2 ∂(atomLaw ![1 / 3, 1 / 2, 1 / 6] ![-1, 0, 2]) = 1 := by
    rw [atomLaw_integral hc]; simp [Fin.sum_univ_succ]; norm_num
  have e3 : ∫ x, x ^ 3 ∂(atomLaw ![1 / 3, 1 / 2, 1 / 6] ![-1, 0, 2]) = 1 := by
    rw [atomLaw_integral hc]; simp [Fin.sum_univ_succ]; norm_num
  have e4 : ∫ x, x ^ 4 ∂(atomLaw ![1 / 3, 1 / 2, 1 / 6] ![-1, 0, 2]) = 3 := by
    rw [atomLaw_integral hc]; simp [Fin.sum_univ_succ]; norm_num
  refine ⟨?_, e3, e4⟩
  exact sq_moment_three_add_one_le _ (atomLaw_integrable _ _ _) e1 e2

/-- The law with masses `1/4, 1/4, 1/2` at `√(2/3), -√(2/3), 0`. -/
private def threePt : Measure ℝ :=
  atomLaw ![1 / 4, 1 / 4, 1 / 2] ![Real.sqrt (2 / 3), -Real.sqrt (2 / 3), 0]

private lemma threePt_weights : ∀ j : Fin 3, 0 ≤ (![1 / 4, 1 / 4, 1 / 2] : Fin 3 → ℝ) j := by
  intro j; fin_cases j <;> norm_num

private lemma threePt_integral (f : ℝ → ℝ) :
    ∫ x, f x ∂threePt =
      1 / 4 * f (Real.sqrt (2 / 3)) + 1 / 4 * f (-Real.sqrt (2 / 3)) + 1 / 2 * f 0 := by
  unfold threePt
  rw [atomLaw_integral threePt_weights]
  simp [Fin.sum_univ_succ]
  ring

private instance threePt_prob : IsProbabilityMeasure threePt :=
  atomLaw_isProb threePt_weights (by simp [Fin.sum_univ_succ]; norm_num) _

/-- The entry laws of size `3` in which every entry follows `threePt`. -/
private def threeLaws : EntryLaws 3 := ⟨fun _ => threePt, fun _ => threePt⟩

private lemma threeLaws_momentCond : threeLaws.MomentCond 2 := by
  have ha2 : Real.sqrt (2 / 3) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt (2 / 3) := Real.sqrt_nonneg _
  have e1 : ∫ x, x ∂threePt = 0 := by rw [threePt_integral]; ring
  have e2 : ∫ x, x ^ 2 ∂threePt = ((3 : ℕ) : ℝ)⁻¹ := by
    rw [threePt_integral (fun x => x ^ 2), neg_sq, ha2]; norm_num
  have e3 : ∫ x, |x| ^ 3 ∂threePt = Real.sqrt (2 / 3) / 3 := by
    rw [threePt_integral (fun x => |x| ^ 3), abs_neg, abs_of_nonneg ha0]
    have : Real.sqrt (2 / 3) ^ 3 = Real.sqrt (2 / 3) * (2 / 3) := by rw [pow_succ, ha2]; ring
    simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero]
    rw [this]; ring
  have e4 : ∫ x, x ^ 4 ∂threePt = 2 / 9 := by
    rw [threePt_integral (fun x => x ^ 4), show (-Real.sqrt (2 / 3)) ^ 4 = Real.sqrt (2 / 3) ^ 4 by
      ring, show Real.sqrt (2 / 3) ^ 4 = (Real.sqrt (2 / 3) ^ 2) ^ 2 by ring, ha2]
    norm_num
  refine ⟨⟨fun _ => threePt_prob, fun _ => threePt_prob⟩, fun _ => atomLaw_integrable _ _ _,
    fun _ => atomLaw_integrable _ _ _, fun _ => e1, fun _ => e1, fun _ => ?_, fun _ => e2,
    fun _ => ?_, fun _ => ?_⟩
  · change ∫ x, x ^ 2 ∂threePt ≤ 2 / ((3 : ℕ) : ℝ)
    rw [e2]; norm_num
  · change ∫ x, |x| ^ 3 ∂threePt ≤ 2 * ((3 : ℕ) : ℝ) ^ (-(3 : ℝ) / 2)
    rw [e3, show ((3 : ℕ) : ℝ) = 3 by norm_num, rpow_neg_three_halves (by norm_num), inv_pow]
    have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hprod : Real.sqrt (2 / 3) * Real.sqrt 3 ≤ 2 := by
      have hsq : (Real.sqrt (2 / 3) * Real.sqrt 3) ^ 2 = 2 := by
        rw [mul_pow, ha2, hs2]; norm_num
      nlinarith [mul_nonneg ha0 hs0.le]
    rw [show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs2]]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    rw [show 2 * (3 * Real.sqrt 3)⁻¹ * 3 = 2 / Real.sqrt 3 by field_simp]
    rw [le_div_iff₀ hs0]
    exact hprod
  · change ∫ x, x ^ 4 ∂threePt ≤ 2 * Real.log ((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) ^ 2
    have := one_lt_log_of_three_le (le_refl 3)
    rw [e4, show ((3 : ℕ) : ℝ) = 3 by norm_num] at *
    rw [le_div_iff₀ (by norm_num)]
    nlinarith

/-- Lemma 5.1 at `N = 3` and `C1 = 2`: every entry follows the three-point law `threePt`
(mass `1/4, 1/4, 1/2` at `±√(2/3), 0`), which satisfies the moment conditions with `C1 = 2`. -/
example : ∃ L' : EntryLaws 3, L'.IsProb ∧
    L'.BoundedSupportAS (Real.sqrt (3 : ℕ) / ((2 * 2 + 4) * 2 * Real.log (3 : ℕ))) ∧
    (∀ p, ∀ k ∈ Finset.Icc 1 4, ∫ x, x ^ k ∂(L'.off p) = ∫ x, x ^ k ∂(threeLaws.off p)) ∧
    (∀ i, ∀ k ∈ Finset.Icc 1 2, ∫ x, x ^ k ∂(L'.diag i) = ∫ x, x ^ k ∂(threeLaws.diag i)) :=
  exists_momentMatched (le_refl 3) threeLaws_momentCond

#print axioms exists_law_four_moments
#print axioms sq_moment_three_add_one_le
#print axioms exists_momentMatched

end WEdgeNS
