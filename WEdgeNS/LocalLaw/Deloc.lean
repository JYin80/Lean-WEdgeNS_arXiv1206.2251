import WEdgeNS.LocalLaw.Norm

/-!
# Delocalization of eigenvectors (Lemma 3.1 (3))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- Private lemmas of earlier files: no real number equals a point of the upper half plane; the
-- quadratic form of a symmetric matrix with eigenvalues in `[-M, M]`.
open private eigenvalues_ne_of_im_pos from WEdgeNS.Resolvent.Basic
open private norm_abs_dotProduct_mulVec_le from WEdgeNS.LocalLaw.Norm

/-- The event (3.5), for every unit eigenvector. -/
def delocEvent (N : ℕ) (C : ℝ) : Set (Entries N) :=
  {ω | ∀ (v : Fin N → ℝ) (μ : ℝ), symOfEntries ω *ᵥ v = μ • v → ∑ i, v i ^ 2 = 1 →
    ∀ i, v i ^ 2 ≤ phi N ^ C / N}

/-- Deterministic step of Remark 2.18 and (7.25) of [15]. -/
theorem sq_le_mul_im_resolventC {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {v : Fin N → ℝ} {μ η : ℝ} (hv : H *ᵥ v = μ • v) (hn : ∑ i, v i ^ 2 = 1) (hη : 0 < η)
    (i : Fin N) : v i ^ 2 ≤ η * (resolventC H ⟨μ, η⟩ i i).im := by
  set z : ℂ := ⟨μ, η⟩ with hzdef
  have hz : 0 < z.im := hη
  have h1 := resolventC_mul_eq_one hH (eigenvalues_ne_of_im_pos hH hz)
  have h2 : resolventC H z * (H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ))
      = 1 := mul_eq_one_comm.mp h1
  set G := resolventC H z with hG
  set vc : Fin N → ℂ := fun k => (v k : ℂ) with hvc
  have hHv : (H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ vc =
      ((μ : ℂ) - z) • vc := by
    ext k
    have hk := congrFun hv k
    have hk' : ((H *ᵥ v) k : ℂ) = (μ : ℂ) * (v k : ℂ) := by
      rw [hk]; simp
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul, hvc]
    rw [sub_mul, ← hk']
    simp [Matrix.mulVec, dotProduct]
  have h3 : vc = ((μ : ℂ) - z) • (G *ᵥ vc) := by
    have := congrArg (fun w => G *ᵥ w) hHv
    simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_smul] at this
    exact this
  have hμz : ‖(μ : ℂ) - z‖ = η := by
    have : (μ : ℂ) - z = ((-η : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hzdef]
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos hη]
  have h4 : |v i| ≤ η * ‖(G *ᵥ vc) i‖ := by
    have := congrFun h3 i
    simp only [Pi.smul_apply, smul_eq_mul, hvc] at this
    have h5 := congrArg norm this
    rw [norm_mul, hμz, Complex.norm_real, Real.norm_eq_abs] at h5
    exact h5.le
  have h6 : ‖(G *ᵥ vc) i‖ ≤ ∑ k, ‖G i k‖ * |v k| := by
    simp only [Matrix.mulVec, dotProduct, hvc]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h7 : (∑ k, ‖G i k‖ * |v k|) ^ 2 ≤ (∑ k, ‖G i k‖ ^ 2) * 1 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖G i k‖) (fun k => |v k|)
    simp only [sq_abs, hn] at this
    exact this
  have hward := sum_norm_sq_resolventC hH hz i
  have h8 : v i ^ 2 ≤ η ^ 2 * ((resolventC H z i i).im / z.im) := by
    rw [← hward, ← mul_one (∑ k, ‖G i k‖ ^ 2)] 
    calc v i ^ 2 = |v i| ^ 2 := (sq_abs _).symm
      _ ≤ (η * ‖(G *ᵥ vc) i‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h4 2
      _ = η ^ 2 * ‖(G *ᵥ vc) i‖ ^ 2 := by ring
      _ ≤ η ^ 2 * (∑ k, ‖G i k‖ * |v k|) ^ 2 := by
          gcongr
      _ ≤ η ^ 2 * ((∑ k, ‖G i k‖ ^ 2) * 1) := by gcongr
  have hzi : z.im = η := rfl
  rw [hzi] at h8
  calc v i ^ 2 ≤ η ^ 2 * ((resolventC H z i i).im / η) := h8
    _ = η * (resolventC H z i i).im := by field_simp

/-! ### From (3.3) and (3.4) to (3.5) -/

/-- An eigenvalue of a symmetric matrix whose increasing eigenvalues lie in `[-M, M]` has modulus
at most `M`. -/
private lemma deloc_abs_mu_le {N : ℕ} {ω : Entries N} {M : ℝ}
    (hM : ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ M) {v : Fin N → ℝ} {μ : ℝ}
    (hv : symOfEntries ω *ᵥ v = μ • v) (hn : ∑ i, v i ^ 2 = 1) : |μ| ≤ M := by
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues (symOfEntries_isHermitian ω)
  have hM' : ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ M := fun α => by
    rw [hσ α]; exact hM _
  have h := norm_abs_dotProduct_mulVec_le (symOfEntries_isHermitian ω) hM' v
  have hvv : v ⬝ᵥ v = 1 := by
    rw [← hn]; unfold dotProduct; exact Finset.sum_congr rfl fun i _ => (sq (v i)).symm
  rw [hv, dotProduct_smul, hvv] at h
  simpa using h

/-- Pointwise step: on the events (3.3) at `C1` and (3.4) at `C2`, with `q ≥ φ^C`, every unit
eigenvector satisfies (3.5), once `φ` is large and the powers of `φ` are below the corresponding
powers of `N`. -/
private lemma deloc_pointwise {N : ℕ} {ω : Entries N} {C1 C2 C Cm q : ℝ} (hC1 : 0 < C1)
    (hCC1 : 2 * C1 + 3 ≤ C) (hCC2 : C2 ≤ C) (hCm : 1 ≤ Cm)
    (hmsc : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → ‖msc z‖ ≤ Cm)
    (hφ1 : Cm + 1 ≤ phi N) (hφ2 : Real.sqrt Cm + 2 ≤ phi N) (hN3 : 3 ≤ N)
    (hηN : phi N ^ (2 * C1 + 2) ≤ N) (hC2N : phi N ^ C2 ≤ (N : ℝ) ^ ((2 : ℝ) / 3))
    (hq : phi N ^ C ≤ q) (hL : ω ∈ localLawEvent N C1 q) (hno : ω ∈ normEvent N C2 q) :
    ω ∈ delocEvent N C := by
  intro v μ hv hn i
  have hφ : 1 < phi N := by linarith
  have hφpos : 0 < phi N := by linarith
  have hNpos : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hsq : 0 ≤ Real.sqrt Cm := Real.sqrt_nonneg _
  set φ := phi N with hφdef
  have hφC : 1 ≤ φ ^ C := Real.one_le_rpow hφ.le (by linarith)
  have hφC2 : φ ^ C2 ≤ φ ^ C := Real.rpow_le_rpow_of_exponent_le hφ.le hCC2
  have hq1 : 1 ≤ q := hφC.trans hq
  have hqpos : 0 < q := by linarith
  have hwin : ∀ j, |eigAsc (symOfEntries_isHermitian ω) j| ≤ 4 := by
    intro j
    refine (hno j).trans ?_
    have ha : φ ^ C2 * (1 / q ^ 2) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      calc φ ^ C2 ≤ q := hφC2.trans hq
        _ ≤ q ^ 2 := by nlinarith
    have hb : φ ^ C2 * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 := by
      have h0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hNpos.le _
      calc φ ^ C2 * (N : ℝ) ^ (-(2 : ℝ) / 3)
          ≤ (N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) := by gcongr
        _ = 1 := by rw [← Real.rpow_add hNpos]; norm_num
    rw [mul_add]
    linarith
  have hμ : |μ| ≤ 4 := deloc_abs_mu_le hwin hv hn
  -- the spectral parameter
  set b : ℝ := φ ^ C1 with hbdef
  have hb1 : 1 ≤ b := Real.one_le_rpow hφ.le hC1.le
  have hbpos : 0 < b := by linarith
  have hE : φ ^ (2 * C1 + 2) = (b * φ) ^ 2 := by
    have : φ ^ (2 * C1 + 2) = φ ^ C1 * φ ^ C1 * φ ^ (2 : ℝ) := by
      rw [← Real.rpow_add hφpos, ← Real.rpow_add hφpos]; ring_nf
    rw [this, Real.rpow_two]; ring
  have hbφ : φ ^ (C1 + 1) = b * φ := by
    rw [Real.rpow_add hφpos, Real.rpow_one]
  have hbφ1 : 1 ≤ b * φ := by nlinarith
  have hbφpos : 0 < b * φ := by linarith
  have hqbφ : b * φ ≤ q := by
    rw [← hbφ]
    exact (Real.rpow_le_rpow_of_exponent_le hφ.le (by linarith)).trans hq
  set η : ℝ := (b * φ) ^ 2 / N with hηdef
  have hηpos : 0 < η := by positivity
  have hηle : η ≤ 1 := by
    rw [hηdef, div_le_one hNpos, ← hE]; exact hηN
  have hNη : (N : ℝ) * η = (b * φ) ^ 2 := by rw [hηdef]; field_simp
  have hz : (⟨μ, η⟩ : ℂ) ∈ specDomain N C1 := by
    refine ⟨?_, ?_, ?_⟩
    · change |μ| ≤ 5
      linarith
    · change φ ^ C1 / N < η
      rw [hηdef, ← hbdef]
      refine div_lt_div_of_pos_right ?_ hNpos
      nlinarith
    · change η ≤ 10
      linarith
  have hent := (hL _ hz).2 i i
  simp only [↓reduceIte] at hent
  unfold entryErr at hent
  set z : ℂ := ⟨μ, η⟩ with hzdef
  have hzre : |z.re| ≤ 5 := by change |μ| ≤ 5; linarith
  have hzim : 0 < z.im := hηpos
  have hzim10 : z.im ≤ 10 := by change η ≤ 10; linarith
  have hmz : ‖msc z‖ ≤ Cm := hmsc z hzre hzim hzim10
  -- the three terms of (3.3)
  have t1 : φ ^ C1 * (1 / q) ≤ 1 / φ := by
    rw [← hbdef, mul_one_div, div_le_div_iff₀ hqpos hφpos]
    nlinarith
  have t2 : φ ^ C1 * Real.sqrt ((msc z).im / (N * z.im)) ≤ Real.sqrt Cm / φ := by
    have hzi : z.im = η := rfl
    rw [hzi, hNη, ← hbdef]
    have him : (msc z).im ≤ Cm := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hmz)
    have h1 : Real.sqrt ((msc z).im / (b * φ) ^ 2) ≤ Real.sqrt (Cm / (b * φ) ^ 2) :=
      Real.sqrt_le_sqrt (by gcongr)
    have e : Real.sqrt (Cm / (b * φ) ^ 2) = Real.sqrt Cm / (b * φ) := by
      rw [Real.sqrt_div (by linarith), Real.sqrt_sq hbφpos.le]
    rw [e] at h1
    calc b * Real.sqrt ((msc z).im / (b * φ) ^ 2) ≤ b * (Real.sqrt Cm / (b * φ)) := by gcongr
      _ = Real.sqrt Cm / φ := by field_simp
  have t3 : φ ^ C1 * (1 / (N * z.im)) ≤ 1 / φ := by
    have hzi : z.im = η := rfl
    rw [hzi, hNη, ← hbdef, mul_one_div, div_le_div_iff₀ (by positivity) hφpos]
    nlinarith
  have hGmsc : ‖resolventC (symOfEntries ω) z i i - msc z‖ ≤ 1 := by
    refine hent.trans ?_
    rw [mul_add, mul_add]
    refine (add_le_add (add_le_add t1 t2) t3).trans ?_
    rw [← add_div, ← add_div, div_le_one hφpos]
    linarith
  have hGnorm : ‖resolventC (symOfEntries ω) z i i‖ ≤ Cm + 1 := by
    calc ‖resolventC (symOfEntries ω) z i i‖
        = ‖(resolventC (symOfEntries ω) z i i - msc z) + msc z‖ := by rw [sub_add_cancel]
      _ ≤ ‖resolventC (symOfEntries ω) z i i - msc z‖ + ‖msc z‖ := norm_add_le _ _
      _ ≤ Cm + 1 := by linarith
  have hGim : (resolventC (symOfEntries ω) z i i).im ≤ Cm + 1 :=
    (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hGnorm)
  have hS := sq_le_mul_im_resolventC (symOfEntries_isHermitian ω) hv hn hηpos i
  have hexp : φ ^ (2 * C1 + 2) * φ ≤ φ ^ C := by
    have : φ ^ (2 * C1 + 2) * φ = φ ^ (2 * C1 + 3) := by
      rw [← Real.rpow_add_one hφpos.ne']; ring_nf
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_le hφ.le hCC1
  calc v i ^ 2 ≤ η * (resolventC (symOfEntries ω) z i i).im := hS
    _ ≤ η * φ := by gcongr; linarith
    _ = φ ^ (2 * C1 + 2) * φ / N := by rw [hηdef, hE]; ring
    _ ≤ φ ^ C / N := by gcongr

/-- Lemma 3.1 (3) with Remark 3.2. -/
theorem delocalization {ζ C0 c : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) (hc : 0 < c) :
    ∃ C > 0, HighProbOn ζ (fun _ L => L.IsGenWigner C0)
      (fun N L => {ω | (∃ q, L.SupportParam (phi N ^ C) c q) → ω ∈ delocEvent N C}) := by
  obtain ⟨C1, hC1, h1⟩ := localLaw hζ hC0 hc
  obtain ⟨C2, hC2, h2⟩ := norm_le_two_add hζ hC0 hc
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  have hev := (eventually_ge_atTop 16).and <|
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max (Cm + 1) (Real.sqrt Cm + 2))).and <|
    (phi_rpow_le_rpow (2 * C1 + 2) one_pos).and
      (phi_rpow_le_rpow C2 (by norm_num : (0 : ℝ) < 2 / 3))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨max (2 * C1 + 3) C2, lt_max_of_lt_left (by linarith), ?_⟩
  obtain ⟨cc, hcc, CC, hCC, NN, hNN⟩ := HighProbOn.inter h1 h2
  refine ⟨cc, hcc, CC, hCC, max NN N0, fun N hN L hL => ?_⟩
  refine le_trans (measure_mono (Set.compl_subset_compl.mpr fun ω hω hSP => ?_))
    (hNN N (le_trans (le_max_left _ _) hN) L hL)
  have hN : N0 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨q, hq⟩ := hSP
  obtain ⟨h16, hlog, hηN, hC2N⟩ := hN0 N hN
  have hφK : max (Cm + 1) (Real.sqrt Cm + 2) ≤ phi N := hlog.trans (log_le_phi h16)
  have hφ1 : 1 ≤ phi N := by
    have := le_max_left (Cm + 1) (Real.sqrt Cm + 2)
    linarith
  have hqC : phi N ^ (max (2 * C1 + 3) C2) ≤ q := hq.1
  have hq1 : L.SupportParam (phi N ^ C1) c q :=
    ⟨(Real.rpow_le_rpow_of_exponent_le hφ1 (by
      have := le_max_left (2 * C1 + 3) C2
      linarith)).trans hqC, hq.2.1, hq.2.2⟩
  have hq2 : L.SupportParam (phi N ^ C2) c q :=
    ⟨(Real.rpow_le_rpow_of_exponent_le hφ1 (le_max_right _ _)).trans hqC, hq.2.1, hq.2.2⟩
  rw [Real.rpow_one] at hηN
  exact deloc_pointwise hC1 (le_max_left _ _) (le_max_right _ _) hCm
    (fun z h1 h2 h3 => (hmsc z h1 h2 h3).1.2) (le_trans (le_max_left _ _) hφK)
    (le_trans (le_max_right _ _) hφK) (by omega) hηN hC2N hqC (hω.1 q hq1) (hω.2 q hq2)

/-! ### Compiled check -/

/-- The deterministic bound at `N = 2`, for the symmetric non-diagonal matrix
`H = 2 u uᵀ - 1` with unit vector `u = (3/5, 4/5)`, the unit eigenvector `u` with eigenvalue `1`,
and `η = 1`. -/
example : ((![3 / 5, 4 / 5] : Fin 2 → ℝ) 0) ^ 2 ≤
    1 * (resolventC (!![-7 / 25, 24 / 25; 24 / 25, 7 / 25] : Matrix (Fin 2) (Fin 2) ℝ)
      ⟨1, 1⟩ 0 0).im := by
  refine sq_le_mul_im_resolventC (v := ![3 / 5, 4 / 5]) (μ := 1) ?_ ?_ ?_ ?_ 0
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · exact one_pos

#print axioms delocEvent
#print axioms sq_le_mul_im_resolventC
#print axioms delocalization

end WEdgeNS
