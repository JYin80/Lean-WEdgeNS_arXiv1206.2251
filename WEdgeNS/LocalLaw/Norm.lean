import WEdgeNS.LocalLaw.Outside
import WEdgeNS.LocalLaw.NormApriori
import WEdgeNS.LocalLaw.Interface
import WEdgeNS.Semicircle.Rigidity

/-!
# The norm bound (Lemma 3.1 (2))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- Private lemmas of earlier files: the quadratic form of an entrywise small matrix, the sign of
-- `φ`, the asymptotics of `N ^ k exp (-b N ^ c)`, the combination of two error terms, the
-- Rademacher instance and its window.
open private dotProduct_mulVec_le_of_abs_le from WEdgeNS.Model.LambdaMax
open private iface_phi_nonneg iface_tendsto_pow_mul_exp iface_real_bound
  from WEdgeNS.LocalLaw.Interface
open private sc_phi_pos sc_rad_instance from WEdgeNS.LocalLaw.SelfConsistent
open private outside_window_rad from WEdgeNS.LocalLaw.Outside

/-- The event (3.4). -/
def normEvent (N : ℕ) (C q : ℝ) : Set (Entries N) :=
  {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤
    2 + phi N ^ C * (1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3))}

/-! ### Eigenvalues and the quadratic form -/

/-- `|⟨u, A u⟩| ≤ M ⟨u, u⟩` for a real symmetric matrix `A` with all eigenvalues in `[-M, M]`. -/
private lemma norm_abs_dotProduct_mulVec_le {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) {M : ℝ} (hM : ∀ α, |hA.eigenvalues α| ≤ M) (u : Fin N → ℝ) :
    |u ⬝ᵥ (A *ᵥ u)| ≤ M * (u ⬝ᵥ u) := by
  obtain ⟨U, hUU, hspec⟩ : ∃ U : Matrix (Fin N) (Fin N) ℝ, U * Uᵀ = 1 ∧
      A = U * diagonal hA.eigenvalues * Uᵀ := by
    refine ⟨(hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ), ?_, ?_⟩
    · have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
      rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
        conjTranspose_eq_transpose_of_trivial] at this
    · have := hA.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at this
      simpa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  have h1 : u ⬝ᵥ (A *ᵥ u) = (Uᵀ *ᵥ u) ⬝ᵥ (diagonal hA.eigenvalues *ᵥ (Uᵀ *ᵥ u)) := by
    conv_lhs => rw [hspec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  have h2 : u ⬝ᵥ u = (Uᵀ *ᵥ u) ⬝ᵥ (Uᵀ *ᵥ u) := by
    conv_rhs => rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hUU, one_mulVec]
  rw [h1, h2, dotProduct, dotProduct, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [mulVec_diagonal, abs_mul, abs_mul]
  have hk := hM k
  have hw : |(Uᵀ *ᵥ u) k| * |(Uᵀ *ᵥ u) k| = (Uᵀ *ᵥ u) k * (Uᵀ *ᵥ u) k := abs_mul_abs_self _
  calc |(Uᵀ *ᵥ u) k| * (|hA.eigenvalues k| * |(Uᵀ *ᵥ u) k|)
      = |hA.eigenvalues k| * ((Uᵀ *ᵥ u) k * (Uᵀ *ᵥ u) k) := by rw [← hw]; ring
    _ ≤ M * ((Uᵀ *ᵥ u) k * (Uᵀ *ᵥ u) k) := mul_le_mul_of_nonneg_right hk (mul_self_nonneg _)

/-- If the entries of `H - H'` are at most `κ` in modulus and all eigenvalues of `H'` lie in
`[-M, M]`, then all eigenvalues of `H` lie in `[-(M + Nκ), M + Nκ]`. -/
private lemma norm_abs_eigenvalues_le {N : ℕ} {H H' : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {κ M : ℝ}
    (hd : ∀ i j, |H i j - H' i j| ≤ κ) (hM : ∀ α, |hH'.eigenvalues α| ≤ M) (α : Fin N) :
    |hH.eigenvalues α| ≤ M + N * κ := by
  have hκ : 0 ≤ κ := (abs_nonneg _).trans (hd α α)
  set u : Fin N → ℝ := ⇑(hH.eigenvectorBasis α) with hu
  have hHu : H *ᵥ u = hH.eigenvalues α • u := hH.mulVec_eigenvectorBasis α
  have huu : u ⬝ᵥ u = 1 := by
    have h := orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal α α
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa using h
  have hsplit : u ⬝ᵥ (H *ᵥ u) = u ⬝ᵥ (H' *ᵥ u) + u ⬝ᵥ ((H - H') *ᵥ u) := by
    rw [sub_mulVec, dotProduct_sub]; ring
  rw [hHu, dotProduct_smul, huu] at hsplit
  have h1 := norm_abs_dotProduct_mulVec_le hH' hM u
  have h2 := dotProduct_mulVec_le_of_abs_le (D := H - H') (fun i j => hd i j) hκ u
  have h3 := dotProduct_mulVec_le_of_abs_le (D := H' - H)
    (fun i j => by rw [Matrix.sub_apply, abs_sub_comm]; exact hd i j) hκ u
  have h4 : u ⬝ᵥ ((H - H') *ᵥ u) + u ⬝ᵥ ((H' - H) *ᵥ u) = 0 := by
    rw [← dotProduct_add, ← add_mulVec, show H - H' + (H' - H) = 0 by abel, zero_mulVec,
      dotProduct_zero]
  rw [huu] at h1 h2 h3
  simp only [smul_eq_mul, mul_one] at hsplit h1 h2 h3
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-! ### The event (3.4) -/

/-- The window of (3.4) shrinks as the support parameter `q` grows. -/
private lemma norm_normEvent_anti (N : ℕ) (C : ℝ) {q q' : ℝ} (hq : 0 < q) (hqq : q ≤ q') :
    normEvent N C q' ⊆ normEvent N C q := by
  have hC : 0 ≤ phi N ^ C := Real.rpow_nonneg (iface_phi_nonneg N) C
  intro ω hω j
  refine (hω j).trans ?_
  have : 1 / q' ^ 2 ≤ 1 / q ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hq 2) (pow_le_pow_left₀ hq.le hqq 2)
  gcongr

/-- If all eigenvalues of `ω` have modulus at most `3` and `ω` satisfies `outsideEvent`, then all
eigenvalues are below the edge `2 + φ^{Co} (q⁻² + N^{-2/3})` of the window of (4.36) of [15]: an
eigenvalue `E` in the window would give `outEta E < |E - E| = 0`. -/
private lemma norm_eigenvalues_le_window {N : ℕ} {ω : Entries N} {K Co q : ℝ}
    (hA : ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3)
    (hB : ω ∈ outsideEvent N K 1 Co q) (α : Fin N) :
    |(symOfEntries_isHermitian ω).eigenvalues α| ≤
      2 + phi N ^ Co * (1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues (symOfEntries_isHermitian ω)
  have h3 : |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3 := by
    rw [hσ α]; exact hA _
  have h := (hB _ hlt.le h3).2.2 α
  rw [sub_self, abs_zero] at h
  have h0 : 0 ≤ outEta N K 1 ((symOfEntries_isHermitian ω).eigenvalues α) := by
    unfold outEta
    exact div_nonneg (Real.rpow_nonneg (iface_phi_nonneg N) _)
      (mul_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _))
  linarith

/-- If all eigenvalues of `ω'` have modulus at most `3`, `ω'` satisfies `outsideEvent` at the
parameter `q / 2`, and `ω` is entrywise within `κ` of `ω'` with `N κ ≤ N^{-2/3}`, then `ω`
satisfies (3.4) with exponent `Cm + 1` and parameter `q`, for `Co ≤ Cm`, `0 ≤ Cm` and `5 ≤ φ`. -/
private lemma norm_transfer {N : ℕ} {ω ω' : Entries N} {K Co Cm q κ : ℝ}
    (hA : ∀ j, |eigAsc (symOfEntries_isHermitian ω') j| ≤ 3)
    (hB : ω' ∈ outsideEvent N K 1 Co (q / 2))
    (hclose : ∀ i j, |symOfEntries ω i j - symOfEntries ω' i j| ≤ κ)
    (hCo : Co ≤ Cm) (hCm : 0 ≤ Cm) (hφ : 5 ≤ phi N) (hq : 0 < q)
    (hκ : (N : ℝ) * κ ≤ (N : ℝ) ^ (-(2 : ℝ) / 3)) :
    ω ∈ normEvent N (Cm + 1) q := by
  intro j
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues (symOfEntries_isHermitian ω)
  have hj : eigAsc (symOfEntries_isHermitian ω) j =
      (symOfEntries_isHermitian ω).eigenvalues (σ.symm j) := by
    rw [hσ]; simp
  rw [hj]
  refine (norm_abs_eigenvalues_le (symOfEntries_isHermitian ω) (symOfEntries_isHermitian ω')
    hclose (fun α => norm_eigenvalues_le_window hA hB α) (σ.symm j)).trans ?_
  have hφ1 : 1 ≤ phi N := by linarith
  have hPm : phi N ^ Co ≤ phi N ^ Cm := Real.rpow_le_rpow_of_exponent_le hφ1 hCo
  have hPm1 : 1 ≤ phi N ^ Cm := Real.one_le_rpow hφ1 hCm
  have hP0 : 0 ≤ phi N ^ Co := Real.rpow_nonneg (iface_phi_nonneg N) _
  have hpow : phi N ^ (Cm + 1) = phi N ^ Cm * phi N := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hs : 1 / (q / 2) ^ 2 = 4 * (1 / q ^ 2) := by field_simp; norm_num
  have hs0 : 0 ≤ 1 / q ^ 2 := by positivity
  have ht0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [hs, hpow]
  set s : ℝ := 1 / q ^ 2
  set t : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3)
  set P : ℝ := phi N ^ Co
  set Pm : ℝ := phi N ^ Cm
  have e1 : P * (4 * s + t) ≤ Pm * (4 * s + t) :=
    mul_le_mul_of_nonneg_right hPm (by positivity)
  have e2 : 0 ≤ Pm * ((phi N - 4) * s) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) hs0)
  have e3 : t ≤ Pm * ((phi N - 1) * t) := by
    have : 1 ≤ Pm * (phi N - 1) := by nlinarith
    nlinarith
  nlinarith [e1, e2, e3]

/-- The three error terms (entrywise truncation, a priori norm bound, eigenvalue exclusion) add up
to a single `N ^ (max 1 Ca' + 1) exp (-c' φ^ζ)` with `c' = min (min 1 co) ca`. -/
private lemma norm_real_bound {N : ℕ} {ζ c co ca : ℝ} {Ca' : ℕ} (hN : 3 ≤ N)
    (h6 : phi N ^ ζ ≤ (N : ℝ) ^ (c / 2)) (h7 : 2 ≤ (N : ℝ) ^ (c / 2))
    (h5 : (N : ℝ) ^ 2 * Real.exp (-(1 / 2) * (N : ℝ) ^ c) < 1 / 2) :
    2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c) +
        ((N : ℝ) ^ Ca' * Real.exp (-ca * phi N ^ ζ) + Real.exp (-co * phi N ^ ζ)) ≤
      (N : ℝ) ^ (max 1 Ca' + 1) * Real.exp (-(min (min 1 co) ca) * phi N ^ ζ) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hE0 : 0 ≤ phi N ^ ζ := Real.rpow_nonneg (iface_phi_nonneg N) ζ
  have hR := iface_real_bound (cs := co) hN h6 h7 h5
  set E' : ℝ := Real.exp (-(min (min 1 co) ca) * phi N ^ ζ) with hE'
  have hE'0 : 0 ≤ E' := (Real.exp_pos _).le
  have hE1 : Real.exp (-(min 1 co) * phi N ^ ζ) ≤ E' :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (min 1 co) ca])
  have hE2 : Real.exp (-ca * phi N ^ ζ) ≤ E' :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (min 1 co) ca])
  have hNm1 : (N : ℝ) ^ 1 ≤ (N : ℝ) ^ (max 1 Ca') :=
    pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  have hNm2 : (N : ℝ) ^ Ca' ≤ (N : ℝ) ^ (max 1 Ca') :=
    pow_le_pow_right₀ (by linarith) (le_max_right _ _)
  have hNm : (N : ℝ) ^ (max 1 Ca' + 1) = (N : ℝ) ^ (max 1 Ca') * N := pow_succ _ _
  have hNm0 : 0 ≤ (N : ℝ) ^ (max 1 Ca') := by positivity
  have h1 : (N : ℝ) ^ 1 * Real.exp (-(min 1 co) * phi N ^ ζ) ≤ (N : ℝ) ^ (max 1 Ca') * E' :=
    mul_le_mul hNm1 hE1 (Real.exp_pos _).le hNm0
  have h2 : (N : ℝ) ^ Ca' * Real.exp (-ca * phi N ^ ζ) ≤ (N : ℝ) ^ (max 1 Ca') * E' :=
    mul_le_mul hNm2 hE2 (Real.exp_pos _).le hNm0
  have h3 : 0 ≤ (N : ℝ) ^ (max 1 Ca') * E' := mul_nonneg hNm0 hE'0
  rw [hNm]
  nlinarith [h3]

/-! ### The theorem -/

/-- Lemma 3.1 (2) with Remark 3.2. -/
theorem norm_le_two_add {ζ C0 c : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) (hc : 0 < c) :
    ∃ C > 0, HighProbOn ζ (fun _ L => L.IsGenWigner C0)
      (fun N L => {ω | ∀ q, L.SupportParam (phi N ^ C) c q → ω ∈ normEvent N C q}) := by
  have hC01 : (0 : ℝ) ≤ max C0 1 := le_max_of_le_right zero_le_one
  obtain ⟨Ca, hCa, ca, hca, Ca', hCa', Na, hNa⟩ := norm_apriori hζ hC01
  obtain ⟨K, hK, hout⟩ := outside_boundedAS hζ hC01
  obtain ⟨Co, hCo, co, hco, No, hNo⟩ := hout 1 one_pos
  obtain ⟨Nt, hNt⟩ := exists_truncation hC0 hc
  have hc2 : 0 < c / 2 := half_pos hc
  have hCm : 0 < max (Ca : ℝ) Co := lt_max_of_lt_right hCo
  have hev := (eventually_ge_atTop (max (max Na No) Nt)).and <|
    (eventually_ge_atTop 16).and <|
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 5).and <|
    ((iface_tendsto_pow_mul_exp hc (by norm_num : (0 : ℝ) < 1 / 4) 2).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).and <|
    ((iface_tendsto_pow_mul_exp hc (by norm_num : (0 : ℝ) < 1 / 2) 2).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and <|
    (phi_rpow_le_rpow ζ hc2).and <|
    (((tendsto_rpow_atTop hc2).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨max (Ca : ℝ) Co + 1, by linarith,
    highProbOn_forall_param (Q := fun N => phi N ^ (max (Ca : ℝ) Co + 1)) hc
      (fun N q q' hq hqq => norm_normEvent_anti N (max (Ca : ℝ) Co + 1) hq hqq) ?_⟩
  refine ⟨min (min 1 co) ca, lt_min (lt_min one_pos hco) hca, max 1 Ca' + 1, by positivity, N0,
    fun N hN L q hG hS => ?_⟩
  obtain ⟨hNN, h16, hlog5, h4, h5, h6, h7⟩ := hN0 N hN
  have hNa' : Na ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNN
  have hNo' : No ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNN
  have hNt' : Nt ≤ N := le_trans (le_max_right _ _) hNN
  have h3 : 3 ≤ N := by omega
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hNpos : (0 : ℝ) < N := by linarith
  have hφ5 : 5 ≤ phi N := hlog5.trans (log_le_phi h16)
  have hφ1 : 1 ≤ phi N := by linarith
  have hφC : 1 ≤ phi N ^ (max (Ca : ℝ) Co + 1) := Real.one_le_rpow hφ1 (by linarith)
  have hq0 : 0 < q := lt_of_lt_of_le one_pos (hφC.trans hS.1)
  have hS1 : L.SupportParam 1 c q := ⟨hφC.trans hS.1, hS.2.1, hS.2.2⟩
  obtain ⟨L', T, hT, hmap, hG', hBS', hbad⟩ := hNt N hNt' L q hG hS1
  have hq2 : phi N ^ max (Ca : ℝ) Co ≤ q / 2 := by
    have hpow : phi N ^ (max (Ca : ℝ) Co + 1) = phi N ^ max (Ca : ℝ) Co * phi N := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have ha : 0 ≤ phi N ^ max (Ca : ℝ) Co := Real.rpow_nonneg (iface_phi_nonneg N) _
    have := hS.1
    nlinarith
  have hqa : phi N ^ Ca ≤ q / 2 := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_of_exponent_le hφ1 (le_max_left _ _)).trans hq2
  have hqo : phi N ^ Co ≤ q / 2 :=
    (Real.rpow_le_rpow_of_exponent_le hφ1 (le_max_right _ _)).trans hq2
  have hbdA := hNa N hNa' L' ⟨hG', q / 2, hqa, hBS'⟩
  have hbdB := hNo N hNo' L' (q / 2) hG' hBS' hqo
  set κ : ℝ := Real.exp (-(N : ℝ) ^ c / 4) with hκdef
  have hκ0 : 0 ≤ κ := (Real.exp_pos _).le
  have hκe : κ = Real.exp (-(1 / 4) * (N : ℝ) ^ c) := by
    rw [hκdef]; congr 1; ring
  have hNκ : (N : ℝ) * κ ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    have h1 : (N : ℝ) ^ 2 * κ < 1 := by rw [hκe]; exact h4
    have h2 : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    refine le_trans ?_ h2
    rw [← one_div, le_div_iff₀ hNpos]
    nlinarith
  have hsub : (normEvent N (max (Ca : ℝ) Co + 1) q)ᶜ ⊆
      {ω | ∃ i j, κ < |symOfEntries ω i j - symOfEntries (T ω) i j|} ∪
        (T ⁻¹' {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}ᶜ ∪
          T ⁻¹' (outsideEvent N K 1 Co (q / 2))ᶜ) := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, not_or,
      not_exists, not_lt, not_not] at hcon
    obtain ⟨hclose, hA, hB⟩ := hcon
    exact hω (norm_transfer hA hB hclose (le_max_right _ _) hCm.le hφ5 hq0 hNκ)
  have hpre : ∀ S : Set (Entries N), L.law (T ⁻¹' S) ≤ L'.law S := fun S => by
    calc L.law (T ⁻¹' S) ≤ (L.law.map T) S := Measure.le_map_apply hT.aemeasurable _
      _ = L'.law S := by rw [hmap]
  have hmeas : L.law (normEvent N (max (Ca : ℝ) Co + 1) q)ᶜ ≤
      ENNReal.ofReal (2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c)) +
        (ENNReal.ofReal ((N : ℝ) ^ Ca' * Real.exp (-ca * phi N ^ ζ)) +
          ENNReal.ofReal (Real.exp (-co * phi N ^ ζ))) := by
    calc L.law (normEvent N (max (Ca : ℝ) Co + 1) q)ᶜ
        ≤ L.law ({ω | ∃ i j, κ < |symOfEntries ω i j - symOfEntries (T ω) i j|} ∪
            (T ⁻¹' {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}ᶜ ∪
              T ⁻¹' (outsideEvent N K 1 Co (q / 2))ᶜ)) := measure_mono hsub
      _ ≤ L.law {ω | ∃ i j, κ < |symOfEntries ω i j - symOfEntries (T ω) i j|} +
            L.law (T ⁻¹' {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}ᶜ ∪
              T ⁻¹' (outsideEvent N K 1 Co (q / 2))ᶜ) := measure_union_le _ _
      _ ≤ L.law {ω | ∃ i j, κ < |symOfEntries ω i j - symOfEntries (T ω) i j|} +
            (L.law (T ⁻¹' {ω | ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 3}ᶜ) +
              L.law (T ⁻¹' (outsideEvent N K 1 Co (q / 2))ᶜ)) :=
          add_le_add le_rfl (measure_union_le _ _)
      _ ≤ _ := add_le_add hbad (add_le_add ((hpre _).trans hbdA) ((hpre _).trans hbdB))
  refine hmeas.trans ?_
  have ha : 0 ≤ 2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c) := by positivity
  have hb : 0 ≤ (N : ℝ) ^ Ca' * Real.exp (-ca * phi N ^ ζ) := by positivity
  have hcc : 0 ≤ Real.exp (-co * phi N ^ ζ) := (Real.exp_pos _).le
  rw [← ENNReal.ofReal_add hb hcc, ← ENNReal.ofReal_add ha (add_nonneg hb hcc)]
  exact ENNReal.ofReal_le_ofReal (norm_real_bound h3 h6 h7 h5)

/-! ### Compiled check -/

/-- Lemma 3.1 (2) for the Rademacher laws with `ζ = 1`, `C0 = 1`, `c = 1/2`: for all large `N`
the laws are generalized Wigner laws, `q = N^{2/5}` is an admissible support parameter, the
window of (3.4) lies strictly between `2` and `3`, and the conclusion of `norm_le_two_add`
applies. -/
example : ∃ C > (0 : ℝ), ∃ c' > (0 : ℝ), ∃ C' : ℕ, ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧
    (radLaws N).SupportParam (phi N ^ C) (1 / 2) ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    2 < 2 + phi N ^ C * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) ∧
    2 + phi N ^ C * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) < 3 ∧
    (radLaws N).law {ω | ∀ q, (radLaws N).SupportParam (phi N ^ C) (1 / 2) q →
        ω ∈ normEvent N C q}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c' * phi N ^ (1 : ℝ))) := by
  obtain ⟨C, hC, c', hc', C', hC', N0, h⟩ :=
    norm_le_two_add (ζ := 1) (C0 := 1) (c := 1 / 2) one_pos zero_le_one (by norm_num)
  refine ⟨C, hC, c', hc', C', ?_⟩
  filter_upwards [sc_rad_instance C 1, eventually_ge_atTop N0, outside_window_rad C,
    eventually_ge_atTop 3] with N hi hN hw h3
  have hφ : 0 < phi N ^ C := Real.rpow_pos_of_pos (sc_phi_pos h3) C
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast h3
    linarith
  have hpos : 0 < 1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3) := by positivity
  exact ⟨hi.1, ⟨hi.2.2.1, hi.2.1.boundedSupport _, hi.2.1.tailVarOff _⟩,
    by linarith [mul_pos hφ hpos], by linarith, h N hN (radLaws N) hi.1⟩

#print axioms normEvent
#print axioms norm_le_two_add

end WEdgeNS
