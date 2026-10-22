import WEdgeNS.Model.LambdaMax

/-!
# The general entry-law model (Definitions 2.1, 2.4; Theorem 3.6 moments)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- Entry laws of a generalized symmetric Wigner matrix of size `N` (Definition 2.1):
one law per diagonal entry `h_ii` and one per upper entry `h_ij`, `i < j`. -/
structure EntryLaws (N : ℕ) where
  diag : Fin N → Measure ℝ
  off : OffDiag N → Measure ℝ

namespace EntryLaws

variable {N : ℕ}

/-- Joint law of the independent entries: the product of the entry laws on `Entries N`. -/
def law (L : EntryLaws N) : Measure (Entries N) :=
  (Measure.pi L.diag).prod (Measure.pi L.off)

/-- Every entry law is a probability measure. -/
structure IsProb (L : EntryLaws N) : Prop where
  diag : ∀ i, IsProbabilityMeasure (L.diag i)
  off : ∀ p, IsProbabilityMeasure (L.off p)

theorem isProbabilityMeasure_law {L : EntryLaws N} (hL : L.IsProb) :
    IsProbabilityMeasure L.law := by
  have := hL.diag; have := hL.off
  unfold law; infer_instance

/-- Definition 2.1 with (2.1): mean zero, `E h_ij² = N⁻¹` (`i < j`),
`|E h_ii² - N⁻¹| ≤ C0 N⁻¹`. -/
structure IsGenWigner (L : EntryLaws N) (C0 : ℝ) : Prop where
  isProb : L.IsProb
  sq_int_diag : ∀ i, Integrable (fun x : ℝ => x ^ 2) (L.diag i)
  sq_int_off : ∀ p, Integrable (fun x : ℝ => x ^ 2) (L.off p)
  mean_diag : ∀ i, ∫ x, x ∂(L.diag i) = 0
  mean_off : ∀ p, ∫ x, x ∂(L.off p) = 0
  var_off : ∀ p, ∫ x, x ^ 2 ∂(L.off p) = (N : ℝ)⁻¹
  var_diag : ∀ i, |∫ x, x ^ 2 ∂(L.diag i) - (N : ℝ)⁻¹| ≤ C0 * (N : ℝ)⁻¹

/-- Definition 2.4: `|h_ij| ≤ q⁻¹` with probability at least `1 - exp(-N^c)`. -/
def BoundedSupport (L : EntryLaws N) (q c : ℝ) : Prop :=
  (∀ i, L.diag i {x | q⁻¹ < |x|} ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) ^ c))) ∧
  (∀ p, L.off p {x | q⁻¹ < |x|} ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) ^ c)))

/-- Almost-sure form of Definition 2.4: `|h_ij| ≤ q⁻¹` almost surely. -/
def BoundedSupportAS (L : EntryLaws N) (q : ℝ) : Prop :=
  (∀ i, L.diag i {x | q⁻¹ < |x|} = 0) ∧ (∀ p, L.off p {x | q⁻¹ < |x|} = 0)

theorem BoundedSupportAS.boundedSupport {L : EntryLaws N} {q : ℝ}
    (h : L.BoundedSupportAS q) (c : ℝ) : L.BoundedSupport q c :=
  ⟨fun i => by simp [h.1 i], fun p => by simp [h.2 p]⟩

/-- The moment conditions of Theorem 3.6 with constant `C1`. -/
structure MomentCond (L : EntryLaws N) (C1 : ℝ) : Prop where
  isProb : L.IsProb
  sq_int_diag : ∀ i, Integrable (fun x : ℝ => x ^ 2) (L.diag i)
  fourth_int_off : ∀ p, Integrable (fun x : ℝ => x ^ 4) (L.off p)
  mean_diag : ∀ i, ∫ x, x ∂(L.diag i) = 0
  mean_off : ∀ p, ∫ x, x ∂(L.off p) = 0
  var_diag_le : ∀ i, ∫ x, x ^ 2 ∂(L.diag i) ≤ C1 / N
  var_off : ∀ p, ∫ x, x ^ 2 ∂(L.off p) = (N : ℝ)⁻¹
  third_off_le : ∀ p, ∫ x, |x| ^ 3 ∂(L.off p) ≤ C1 * (N : ℝ) ^ (-(3 : ℝ) / 2)
  fourth_off_le : ∀ p, ∫ x, x ^ 4 ∂(L.off p) ≤ C1 * Real.log N / (N : ℝ) ^ 2

/-- Push every entry law forward by `x ↦ c x`. -/
def scale (c : ℝ) (L : EntryLaws N) : EntryLaws N :=
  ⟨fun i => (L.diag i).map (fun x => c * x), fun p => (L.off p).map (fun x => c * x)⟩

/-- Lindeberg interpolation (3.21): entry `e` follows `Lv` if `Φ e ≤ γ`, and `Lw` otherwise. -/
def interp (Φ : Fin N ⊕ OffDiag N → ℕ) (γ : ℕ) (Lv Lw : EntryLaws N) : EntryLaws N :=
  ⟨fun i => if Φ (Sum.inl i) ≤ γ then Lv.diag i else Lw.diag i,
   fun p => if Φ (Sum.inr p) ≤ γ then Lv.off p else Lw.off p⟩

theorem interp_isGenWigner {Φ : Fin N ⊕ OffDiag N → ℕ} {γ : ℕ} {Lv Lw : EntryLaws N}
    {C0 C0' : ℝ} (hv : Lv.IsGenWigner C0) (hw : Lw.IsGenWigner C0') :
    (interp Φ γ Lv Lw).IsGenWigner (max C0 C0') := by
  have hN : 0 ≤ (N : ℝ)⁻¹ := by positivity
  refine ⟨⟨fun i => ?_, fun p => ?_⟩, fun i => ?_, fun p => ?_, fun i => ?_, fun p => ?_,
    fun p => ?_, fun i => ?_⟩ <;> simp only [interp] <;> split_ifs
  all_goals first
    | exact hv.isProb.diag _ | exact hw.isProb.diag _ | exact hv.isProb.off _
    | exact hw.isProb.off _ | exact hv.sq_int_diag _ | exact hw.sq_int_diag _
    | exact hv.sq_int_off _ | exact hw.sq_int_off _ | exact hv.mean_diag _
    | exact hw.mean_diag _ | exact hv.mean_off _ | exact hw.mean_off _
    | exact hv.var_off _ | exact hw.var_off _
    | exact (hv.var_diag _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hN)
    | exact (hw.var_diag _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hN)

theorem interp_boundedSupport {Φ : Fin N ⊕ OffDiag N → ℕ} {γ : ℕ} {Lv Lw : EntryLaws N}
    {q c : ℝ} (hv : Lv.BoundedSupport q c) (hw : Lw.BoundedSupport q c) :
    (interp Φ γ Lv Lw).BoundedSupport q c := by
  refine ⟨fun i => ?_, fun p => ?_⟩ <;> simp only [interp] <;> split_ifs
  exacts [hv.1 i, hw.1 i, hv.2 p, hw.2 p]

end EntryLaws

open EntryLaws

/-- The symmetric matrix whose upper entries are the coordinates of `ω` (no rescaling). -/
def symOfEntries {N : ℕ} (ω : Entries N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if h : i = j then ω.1 i
    else if h' : i < j then ω.2 ⟨(i, j), h'⟩
    else ω.2 ⟨(j, i), lt_of_le_of_ne (not_lt.mp h') (fun e => h e.symm)⟩

theorem symOfEntries_isHermitian {N : ℕ} (ω : Entries N) : (symOfEntries ω).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, symOfEntries]
  by_cases h : j = i
  · subst h; simp
  · by_cases h' : j < i
    · have h1 : ¬ i < j := not_lt.mpr h'.le
      simp [h, Ne.symm h, h', h1]
    · have h1 : i < j := lt_of_le_of_ne (not_lt.mp h') (Ne.symm h)
      simp [h, Ne.symm h, h', h1]

/-- `s ↦ P(N^{2/3}(λ_N - 2) ≤ s)` for the entry laws `L`. -/
def edgeCdfL {N : ℕ} (L : EntryLaws N) (s : ℝ) : ℝ :=
  (L.law {ω | (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2) ≤ s}).toReal

/-! ### Compiled witnesses (`N = 3`) -/

/-- Symmetric two-point law `(δ_a + δ_{-a}) / 2`. -/
private def generalRad (a : ℝ) : Measure ℝ :=
  (2⁻¹ : ENNReal) • (Measure.dirac a + Measure.dirac (-a))

private instance generalRad_prob (a : ℝ) : IsProbabilityMeasure (generalRad a) := by
  refine ⟨?_⟩
  simp only [generalRad, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private lemma generalRad_integral (a : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(generalRad a) = (f a + f (-a)) / 2 := by
  have hi : ∀ b : ℝ, Integrable f (Measure.dirac b) := fun b =>
    integrable_dirac (by simp)
  unfold generalRad
  rw [integral_smul_measure, integral_add_measure (hi a) (hi (-a)), integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

private lemma generalRad_integrable (a : ℝ) (f : ℝ → ℝ) :
    Integrable f (generalRad a) :=
  (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))
    |>.smul_measure (by simp)

private lemma generalRad_tail (a q : ℝ) (h : |a| ≤ q⁻¹) :
    generalRad a {x | q⁻¹ < |x|} = 0 := by
  have h1 : a ∉ {x : ℝ | q⁻¹ < |x|} := by simpa using h
  have h2 : -a ∉ {x : ℝ | q⁻¹ < |x|} := by simpa using h
  have hm : MeasurableSet {x : ℝ | q⁻¹ < |x|} := measurableSet_lt measurable_const measurable_abs
  simp [generalRad, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hm, h1, h2]

/-- Entry laws of size `3`: every diagonal entry is `generalRad d`, every upper entry
is `generalRad o`. -/
private def generalLaws (d o : ℝ) : EntryLaws 3 :=
  ⟨fun _ => generalRad d, fun _ => generalRad o⟩

private lemma generalLaws_isProb (d o : ℝ) : (generalLaws d o).IsProb :=
  ⟨fun _ => generalRad_prob d, fun _ => generalRad_prob o⟩

private lemma generalLaws_isGenWigner (d o C0 : ℝ) (ho : o ^ 2 = ((3 : ℕ) : ℝ)⁻¹)
    (hd : |d ^ 2 - ((3 : ℕ) : ℝ)⁻¹| ≤ C0 * ((3 : ℕ) : ℝ)⁻¹) :
    (generalLaws d o).IsGenWigner C0 := by
  have h2 : ∀ a : ℝ, ∫ x, x ^ 2 ∂(generalRad a) = a ^ 2 := fun a => by
    rw [generalRad_integral a (fun x => x ^ 2)]; ring
  have h1 : ∀ a : ℝ, ∫ x, x ∂(generalRad a) = 0 := fun a => by
    rw [generalRad_integral a (fun x => x)]; ring
  refine ⟨generalLaws_isProb d o, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ => ?_, fun _ => ?_⟩
  · exact generalRad_integrable d (fun x => x ^ 2)
  · exact generalRad_integrable o (fun x => x ^ 2)
  · exact h1 d
  · exact h1 o
  · simp only [generalLaws]; rw [h2, ho]
  · simp only [generalLaws]; rw [h2]; exact hd

private lemma generalLaws_boundedSupportAS (d o q : ℝ) (hd : |d| ≤ q⁻¹) (ho : |o| ≤ q⁻¹) :
    (generalLaws d o).BoundedSupportAS q :=
  ⟨fun _ => generalRad_tail d q hd, fun _ => generalRad_tail o q ho⟩

private lemma sqrt_three_inv_sq : ((Real.sqrt 3)⁻¹) ^ 2 = ((3 : ℕ) : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

private lemma sqrt_two_thirds_sq : (Real.sqrt (2 / 3)) ^ 2 = 2 / 3 :=
  Real.sq_sqrt (by norm_num)

private lemma sqrt_three_inv_abs : |(Real.sqrt 3)⁻¹| ≤ (1 : ℝ)⁻¹ := by
  rw [abs_of_nonneg (by positivity), inv_one]
  rw [inv_le_one₀ (by positivity)]
  have : (1 : ℝ) ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  exact this

private lemma sqrt_two_thirds_abs : |Real.sqrt (2 / 3)| ≤ (1 : ℝ)⁻¹ := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _), inv_one]
  exact Real.sqrt_le_one.mpr (by norm_num)

/-- Witness for `isProbabilityMeasure_law` at `N = 3`. -/
example : IsProbabilityMeasure (generalLaws (Real.sqrt 3)⁻¹ (Real.sqrt 3)⁻¹).law :=
  EntryLaws.isProbabilityMeasure_law (generalLaws_isProb _ _)

/-- Witness for `BoundedSupportAS.boundedSupport` at `N = 3`: amplitudes `3^{-1/2}` off the
diagonal and `(2/3)^{1/2}` on it, `q = 1`, `c = 1`. -/
example : (generalLaws (Real.sqrt (2 / 3)) (Real.sqrt 3)⁻¹).BoundedSupport 1 1 :=
  (generalLaws_boundedSupportAS _ _ 1 sqrt_two_thirds_abs sqrt_three_inv_abs).boundedSupport 1

/-- Witness for `interp_isGenWigner` at `N = 3`: `Lv` has diagonal variance `1/3`
(`C0 = 0`), `Lw` has diagonal variance `2/3` (`C0' = 1`); with `γ = 1` the diagonal entry `0`
follows `Lv` while the diagonal entries `1, 2` and all upper entries follow `Lw`. -/
example :
    (EntryLaws.interp
      (fun e : Fin 3 ⊕ OffDiag 3 =>
        Sum.elim (fun i : Fin 3 => (i : ℕ) + 1)
          (fun p => 4 + (Fintype.equivFin (OffDiag 3) p : ℕ)) e) 1
      (generalLaws (Real.sqrt 3)⁻¹ (Real.sqrt 3)⁻¹)
      (generalLaws (Real.sqrt (2 / 3)) (Real.sqrt 3)⁻¹)).IsGenWigner (max 0 1) :=
  EntryLaws.interp_isGenWigner
    (generalLaws_isGenWigner _ _ 0 sqrt_three_inv_sq (by rw [sqrt_three_inv_sq]; simp))
    (generalLaws_isGenWigner _ _ 1 sqrt_three_inv_sq
      (by rw [sqrt_two_thirds_sq]; norm_num [abs_of_pos]))

/-- Witness for `interp_boundedSupport` at `N = 3`, `q = 1`, `c = 1`. -/
example :
    (EntryLaws.interp
      (fun e : Fin 3 ⊕ OffDiag 3 =>
        Sum.elim (fun i : Fin 3 => (i : ℕ) + 1)
          (fun p => 4 + (Fintype.equivFin (OffDiag 3) p : ℕ)) e) 1
      (generalLaws (Real.sqrt 3)⁻¹ (Real.sqrt 3)⁻¹)
      (generalLaws (Real.sqrt (2 / 3)) (Real.sqrt 3)⁻¹)).BoundedSupport 1 1 :=
  EntryLaws.interp_boundedSupport
    ((generalLaws_boundedSupportAS _ _ 1 sqrt_three_inv_abs sqrt_three_inv_abs).boundedSupport 1)
    ((generalLaws_boundedSupportAS _ _ 1 sqrt_two_thirds_abs sqrt_three_inv_abs).boundedSupport 1)

#print axioms EntryLaws.isProbabilityMeasure_law
#print axioms EntryLaws.BoundedSupportAS.boundedSupport
#print axioms EntryLaws.interp_isGenWigner
#print axioms EntryLaws.interp_boundedSupport
#print axioms symOfEntries_isHermitian

end WEdgeNS
