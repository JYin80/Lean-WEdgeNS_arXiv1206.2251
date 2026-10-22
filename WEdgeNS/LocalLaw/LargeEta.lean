import WEdgeNS.LocalLaw.Control

/-!
# The local law at large `η`
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- The large deviation events, the minor decompositions and the parameter lemmas of the control
-- estimates, which are internal to that file.
open private ctlMinor ctlBrkBil ctlForm ctlBadBil ctlBrkLin ctlLinForm ctlBadLin ctlBrkQuad
  ctlOffForm ctlBadQuad ctlEnum ctl_pair_le ctl_lin_le ctl_quad_le ctl_form_eq ctl_zFluct_eq
  ctl_sum_sum_enum ctl_card_compl_le ctl_card_compl_pair ctl_card_compl_single ctl_ae_entries
  ctl_ae_diag_entries ctl_union_bound ctl_pairs_sum_le ctl_exp_mono_C ctl_lamO_le ctl_lamD_le
  ctl_lamO_nonneg ctl_lamD_nonneg ctl_diag_ne_zero ctl_symm ctl_one_le_phi ctl_phi_pos ctl_rpow_sq
  ctl_rpow_mono from WEdgeNS.LocalLaw.Control

/-! ### Deterministic bounds for `2 ≤ η` -/

section Deterministic

variable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {z : ℂ}

/-- Every entry of a resolvent is at most `1/η ≤ 1/2`. -/
private lemma lge_norm_resolventC_le (hH : H.IsHermitian) (hz : 2 ≤ z.im) (a b : Fin N) :
    ‖resolventC H z a b‖ ≤ 1 / 2 :=
  (norm_resolventC_apply_le hH (by linarith) a b).trans
    (one_div_le_one_div_of_le (by norm_num) hz)

/-- Ward's identity (3.27) of [15] bounds each row sum of squares by `1/η² ≤ 1/4`. -/
private lemma lge_sum_sq_le (hH : H.IsHermitian) (hz : 2 ≤ z.im) (a : Fin N) :
    ∑ b, ‖resolventC H z a b‖ ^ 2 ≤ 1 / 4 := by
  have h0 : 0 < z.im := by linarith
  rw [sum_norm_sq_resolventC hH h0 a]
  have him : (resolventC H z a a).im ≤ 1 / z.im :=
    ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (norm_resolventC_apply_le hH h0 a a)
  calc (resolventC H z a a).im / z.im ≤ (1 / z.im) / z.im := by gcongr
    _ = 1 / z.im ^ 2 := by field_simp
    _ ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num)
        nlinarith

/-- The Hilbert–Schmidt sum of a resolvent minor over its complement is at most `N/4`
(by (3.27) of [15]). -/
private lemma lge_sum_sq_minor_le (hH : H.IsHermitian) (hz : 2 ≤ z.im) (T : Finset (Fin N)) :
    ∑ k : Fin (Tᶜ.card), ∑ l : Fin (Tᶜ.card),
      ‖resolventC (zeroRC T H) z (ctlEnum T k) (ctlEnum T l)‖ ^ 2 ≤ (N : ℝ) / 4 := by
  rw [ctl_sum_sum_enum T (fun a b => ‖resolventC (zeroRC T H) z a b‖ ^ 2)]
  calc ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, ‖resolventC (zeroRC T H) z a b‖ ^ 2
      ≤ ∑ _a ∈ Tᶜ, (1 / 4 : ℝ) := Finset.sum_le_sum fun a _ =>
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by positivity)).trans (lge_sum_sq_le (zeroRC_isHermitian hH T) hz a)
    _ = (Tᶜ.card : ℝ) * (1 / 4) := by simp
    _ ≤ (N : ℝ) / 4 := by
        have : (Tᶜ.card : ℝ) ≤ N := by exact_mod_cast ctl_card_compl_le T
        linarith

/-- The bracket of the bilinear large deviation bound for entries and Hilbert–Schmidt sum of a
resolvent minor at `η ≥ 2`. -/
private lemma lge_brkBil_le {n : ℕ} (B : Fin n → Fin n → ℂ) {q : ℝ} (hq : 1 ≤ q) (hN : 0 < N)
    (hB1 : ∀ k l, ‖B k l‖ ≤ 1 / 2) (hB2 : ∑ k, ∑ l, ‖B k l‖ ^ 2 ≤ (N : ℝ) / 4) :
    ctlBrkBil N q B ≤ 1 / q + 1 / (2 * Real.sqrt N) := by
  have hq0 : 0 < q := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  unfold ctlBrkBil
  have h1 : (⨆ i, ‖B i i‖) / q ^ 2 ≤ (1 / 2) / q ^ 2 :=
    div_le_div_of_nonneg_right (Real.iSup_le (fun i => hB1 i i) (by norm_num)) (by positivity)
  have h2 : (⨆ i, ⨆ j, if i = j then (0 : ℝ) else ‖B i j‖) / q ≤ (1 / 2) / q :=
    div_le_div_of_nonneg_right (Real.iSup_le (fun i => Real.iSup_le (fun j => by
      split_ifs
      · norm_num
      · exact hB1 i j) (by norm_num)) (by norm_num)) hq0.le
  have h3 : Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2) ≤ 1 / (2 * Real.sqrt N) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ‖B i j‖ ^ 2 ≤ ((N : ℝ) ^ 2)⁻¹ * ((N : ℝ) / 4) := by gcongr
      _ = (1 / (2 * Real.sqrt N)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hNr.le]
        field_simp
        ring
  have h4 : (1 / 2) / q ^ 2 ≤ (1 / 2) / q := by
    apply div_le_div_of_nonneg_left (by norm_num) hq0
    nlinarith
  have h5 : (1 / 2 : ℝ) / q + (1 / 2) / q = 1 / q := by ring
  linarith

/-- The bracket of the linear large deviation bound for the diagonal of a resolvent minor. -/
private lemma lge_brkLin_le {n : ℕ} (B : Fin n → Fin n → ℂ) {q : ℝ} (hq : 1 ≤ q) (hN : 0 < N)
    (hB1 : ∀ k l, ‖B k l‖ ≤ 1 / 2) (hB2 : ∑ k, ∑ l, ‖B k l‖ ^ 2 ≤ (N : ℝ) / 4) :
    ctlBrkLin N q (fun k => B k k) ≤ 1 / q := by
  have hq0 : 0 < q := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold ctlBrkLin
  have h1 : (⨆ k, ‖B k k‖) / q ^ 2 ≤ (1 / 2) / q ^ 2 :=
    div_le_div_of_nonneg_right (Real.iSup_le (fun i => hB1 i i) (by norm_num)) (by positivity)
  have hdiag : ∑ k, ‖B k k‖ ^ 2 ≤ (N : ℝ) / 4 := by
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) hB2
    exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2) (fun l _ => by positivity)
      (Finset.mem_univ k)
  have h3 : Real.sqrt (((q ^ 2)⁻¹ * (N : ℝ)⁻¹) * ∑ k, ‖B k k‖ ^ 2) ≤ 1 / (2 * q) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc ((q ^ 2)⁻¹ * (N : ℝ)⁻¹) * ∑ k, ‖B k k‖ ^ 2
        ≤ ((q ^ 2)⁻¹ * (N : ℝ)⁻¹) * ((N : ℝ) / 4) := by gcongr
      _ = (1 / (2 * q)) ^ 2 := by
        field_simp
        ring
  have h4 : (1 / 2) / q ^ 2 ≤ (1 / 2) / q := by
    apply div_le_div_of_nonneg_left (by norm_num) hq0
    nlinarith
  have h5 : (1 / 2 : ℝ) / q + 1 / (2 * q) = 1 / q := by
    field_simp
    ring
  linarith

/-- The bracket of the quadratic large deviation bound for the off-diagonal of a resolvent
minor. -/
private lemma lge_brkQuad_le {n : ℕ} (B : Fin n → Fin n → ℂ) {q : ℝ} (hq : 1 ≤ q) (hN : 0 < N)
    (hB1 : ∀ k l, ‖B k l‖ ≤ 1 / 2) (hB2 : ∑ k, ∑ l, ‖B k l‖ ^ 2 ≤ (N : ℝ) / 4) :
    ctlBrkQuad N q B ≤ 1 / (2 * q) + 1 / (2 * Real.sqrt N) := by
  have hq0 : 0 < q := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  unfold ctlBrkQuad
  have h2 : (⨆ i, ⨆ j, if i = j then (0 : ℝ) else ‖B i j‖) / q ≤ (1 / 2) / q :=
    div_le_div_of_nonneg_right (Real.iSup_le (fun i => Real.iSup_le (fun j => by
      split_ifs
      · norm_num
      · exact hB1 i j) (by norm_num)) (by norm_num)) hq0.le
  have h3 : Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then (0 : ℝ) else ‖B i j‖ ^ 2) ≤
      1 / (2 * Real.sqrt N) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hle : ∑ i, ∑ j, (if i = j then (0 : ℝ) else ‖B i j‖ ^ 2) ≤ ∑ i, ∑ j, ‖B i j‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        split_ifs
        · positivity
        · exact le_rfl
    calc ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, (if i = j then (0 : ℝ) else ‖B i j‖ ^ 2)
        ≤ ((N : ℝ) ^ 2)⁻¹ * ((N : ℝ) / 4) := by gcongr; exact hle.trans hB2
      _ = (1 / (2 * Real.sqrt N)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hNr.le]
        field_simp
        ring
  have h5 : (1 / 2 : ℝ) / q = 1 / (2 * q) := by
    field_simp
  linarith

/-- `|A_i| ≤ 1/(Nη)` ((3.24) of [15]) by Ward's identity. -/
private lemma lge_norm_aCorr_le (hH : H.IsHermitian) (hz : 2 ≤ z.im) (hN : 0 < N) (i : Fin N) :
    ‖aCorr H z i‖ ≤ 1 / (2 * N) := by
  have h0 : 0 < z.im := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold aCorr
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ j, resolventC H z i j * resolventC H z j i / resolventC H z i i‖ ≤ 1 / 2 := by
    by_cases hg : resolventC H z i i = 0
    · simp [hg]
    · have hgpos : 0 < ‖resolventC H z i i‖ := norm_pos_iff.mpr hg
      rw [← Finset.sum_div, norm_div]
      rw [div_le_iff₀ hgpos]
      have hw := sum_norm_sq_resolventC hH h0 i
      have him : (resolventC H z i i).im ≤ ‖resolventC H z i i‖ :=
        (le_abs_self _).trans (Complex.abs_im_le_norm _)
      calc ‖∑ j, resolventC H z i j * resolventC H z j i‖
          ≤ ∑ j, ‖resolventC H z i j * resolventC H z j i‖ := norm_sum_le _ _
        _ = ∑ j, ‖resolventC H z i j‖ ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [ctl_symm hH h0 j i, norm_mul, sq]
        _ = (resolventC H z i i).im / z.im := hw
        _ ≤ ‖resolventC H z i i‖ / 2 := by
            calc (resolventC H z i i).im / z.im ≤ ‖resolventC H z i i‖ / z.im := by gcongr
              _ ≤ ‖resolventC H z i i‖ / 2 := by
                  apply div_le_div_of_nonneg_left hgpos.le (by norm_num) hz
        _ = 1 / 2 * ‖resolventC H z i i‖ := by ring
  calc (N : ℝ)⁻¹ * ‖∑ j, resolventC H z i j * resolventC H z j i / resolventC H z i i‖
      ≤ (N : ℝ)⁻¹ * (1 / 2) := by gcongr
    _ = 1 / (2 * N) := by field_simp

/-- `|m_sc| ≤ 1/2` for `η ≥ 2`. -/
private lemma lge_norm_msc_le (hz : 2 ≤ z.im) : ‖msc z‖ ≤ 1 / 2 := by
  have h0 : 0 < z.im := by linarith
  obtain ⟨h1, -⟩ := norm_msc_eq_inv_and_lt_one h0
  have hmi := im_msc_pos h0
  have hge : (2 : ℝ) ≤ ‖msc z + z‖ := by
    have := Complex.abs_im_le_norm (msc z + z)
    rw [Complex.add_im, abs_of_pos (by linarith)] at this
    linarith
  rw [h1]
  calc ‖msc z + z‖⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hge
    _ = 1 / 2 := by norm_num

/-- `m_sc (z + m_sc) = -1`. -/
private lemma lge_msc_mul_add (hz : 0 < z.im) : msc z * (z + msc z) = -1 := by
  have hu : z + msc z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.add_im] at this
    have hmi := im_msc_pos hz
    simp at this
    linarith
  have h := msc_add_inv_eq_zero hz
  have h1 : (z + msc z)⁻¹ * (z + msc z) = 1 := inv_mul_cancel₀ hu
  linear_combination (z + msc z) * h - h1

/-- The average of the diagonal entries differs from `m_sc` by at most `Λ_d`. -/
private lemma lge_norm_stieltjesM_sub_le (hN : 0 < N) :
    ‖stieltjesM H z - msc z‖ ≤ lamD H z := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : stieltjesM H z - msc z = (N : ℂ)⁻¹ * ∑ j, (resolventC H z j j - msc z) := by
    unfold stieltjesM
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Matrix.trace]
    simp only [Matrix.diag]
    field_simp
  rw [hm, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ j, (resolventC H z j j - msc z)‖ ≤ N * lamD H z := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖resolventC H z j j - msc z‖ ≤ ∑ _j : Fin N, lamD H z :=
          Finset.sum_le_sum fun j _ => by
            exact le_ciSup (f := fun i => ‖resolventC H z i i - msc z‖)
              (Set.finite_range _).bddAbove j
      _ = N * lamD H z := by simp
  calc (N : ℝ)⁻¹ * ‖∑ j, (resolventC H z j j - msc z)‖ ≤ (N : ℝ)⁻¹ * (N * lamD H z) := by gcongr
    _ = lamD H z := by field_simp

/-- Stability of (3.23) of [15] for `η ≥ 2`: `Λ_d ≤ max_i |Υ_i| / 3`. -/
private lemma lge_lamD_le (hH : H.IsHermitian) (hz : 2 ≤ z.im) (hN : 0 < N) {U : ℝ}
    (hU : ∀ i, ‖upsilon H z i‖ ≤ U) : lamD H z ≤ U / 3 := by
  have h0 : 0 < z.im := by linarith
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU ⟨0, hN⟩)
  have hΛ0 := ctl_lamD_nonneg H z
  have hΛ := lge_norm_stieltjesM_sub_le (H := H) (z := z) hN
  have hmsc := lge_norm_msc_le hz
  have hm := lge_msc_mul_add h0
  have hdiff : ∀ i, ‖resolventC H z i i - msc z‖ ≤ 1 / 4 * (lamD H z + U) := by
    intro i
    have hi := inv_resolventC_diag_eq hH h0 i
    have hg := ctl_diag_ne_zero hH h0 i
    set g := resolventC H z i i with hgdef
    set w := (stieltjesM H z - msc z) - upsilon H z i with hw
    have e1 : g * (-(z + msc z) - w) = 1 := by
      have : g⁻¹ = -(z + msc z) - w := by rw [hi]; ring
      rw [← this]
      exact mul_inv_cancel₀ hg
    have key : g - msc z = g * msc z * w := by
      linear_combination (msc z) * e1 + g * hm
    rw [key, norm_mul, norm_mul]
    have hgn : ‖g‖ ≤ 1 / 2 := lge_norm_resolventC_le hH hz i i
    have hwn : ‖w‖ ≤ lamD H z + U := by
      refine (norm_sub_le _ _).trans ?_
      exact add_le_add hΛ (hU i)
    have hn1 : 0 ≤ ‖g‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖msc z‖ := norm_nonneg _
    have hn3 : 0 ≤ ‖w‖ := norm_nonneg _
    calc ‖g‖ * ‖msc z‖ * ‖w‖ ≤ (1 / 2) * (1 / 2) * (lamD H z + U) := by gcongr
      _ = 1 / 4 * (lamD H z + U) := by ring
  have := ctl_lamD_le (by positivity) hdiff
  linarith

/-- A coarse bound on `Λ_d + Λ_o` for `η ≥ 2`, valid when the entries are bounded by `q⁻¹` and no
large deviation event occurs: `Λ_d + Λ_o ≤ 2 s²/q + s²/√N`. -/
private lemma lge_crude {ω : Entries N} (hN : 0 < N) (hz : 2 ≤ z.im) {q s : ℝ} (hq1 : 1 ≤ q)
    (hs1 : 1 ≤ s)
    (hoff : ∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹)
    (hdiag : ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹)
    (hbil : ∀ i j : Fin N, i ≠ j → ω ∉ ctlBadBil {i, j} q s z i j)
    (hlin : ∀ i : Fin N, ω ∉ ctlBadLin {i} q s z i)
    (hquad : ∀ i : Fin N, ω ∉ ctlBadQuad {i} q s z i) :
    lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤
      2 * (s ^ 2 / q) + s ^ 2 / Real.sqrt N := by
  have hH : (symOfEntries ω).IsHermitian := symOfEntries_isHermitian ω
  have h0 : 0 < z.im := by linarith
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hrsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNr.le
  have hr1 : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN
  set r := Real.sqrt N with hr
  have hB1 : ∀ (T : Finset (Fin N)) (k l : Fin (Tᶜ.card)), ‖ctlMinor T z ω k l‖ ≤ 1 / 2 :=
    fun T k l => lge_norm_resolventC_le (zeroRC_isHermitian hH T) hz _ _
  have hB2 : ∀ T : Finset (Fin N),
      ∑ k : Fin (Tᶜ.card), ∑ l : Fin (Tᶜ.card), ‖ctlMinor T z ω k l‖ ^ 2 ≤ (N : ℝ) / 4 :=
    fun T => lge_sum_sq_minor_le hH hz T
  -- elementary comparisons
  have e1 : 1 / q ≤ s ^ 2 / q := div_le_div_of_nonneg_right (by nlinarith) hq0.le
  have e2 : s / q ≤ s ^ 2 / q := div_le_div_of_nonneg_right (by nlinarith) hq0.le
  have e3 : s ^ 2 / (2 * q) = (s ^ 2 / q) / 2 := by field_simp
  have e4 : s ^ 2 / (2 * r) = (s ^ 2 / r) / 2 := by field_simp
  have e5 : 1 / (2 * (N : ℝ)) ≤ (s ^ 2 / r) / 2 := by
    rw [← hrsq]
    have h1 : 1 / (2 * r ^ 2) ≤ 1 / (2 * r) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 : 1 / (2 * r) ≤ (s ^ 2 / r) / 2 := by
      rw [show 1 / (2 * r) = (1 / r) / 2 by field_simp]
      have : 1 / r ≤ s ^ 2 / r := div_le_div_of_nonneg_right (by nlinarith) hr0.le
      linarith
    exact h1.trans h2
  have hq' : (0 : ℝ) ≤ s ^ 2 / q := by positivity
  have hr' : (0 : ℝ) ≤ s ^ 2 / r := by positivity
  -- the fluctuation terms
  have hZ : ∀ i, ‖zFluct (symOfEntries ω) z i‖ ≤
      s / q + s ^ 2 / (2 * q) + s ^ 2 / (2 * r) := by
    intro i
    rw [ctl_zFluct_eq]
    refine (norm_add_le _ _).trans ?_
    have hl : ‖ctlLinForm {i} z i ω‖ ≤ s * (1 / q) :=
      (not_lt.mp (hlin i)).trans (by
        gcongr
        exact lge_brkLin_le (ctlMinor {i} z ω) hq1 hN (hB1 _) (hB2 _))
    have hqd : ‖ctlOffForm {i} z i ω‖ ≤ s ^ 2 * (1 / (2 * q) + 1 / (2 * r)) :=
      (not_lt.mp (hquad i)).trans (by
        gcongr
        exact lge_brkQuad_le (ctlMinor {i} z ω) hq1 hN (hB1 _) (hB2 _))
    calc _ ≤ s * (1 / q) + s ^ 2 * (1 / (2 * q) + 1 / (2 * r)) := add_le_add hl hqd
      _ = s / q + s ^ 2 / (2 * q) + s ^ 2 / (2 * r) := by ring
  -- the off-diagonal entries
  have hO : lamO (symOfEntries ω) z ≤ (s ^ 2 / q) / 2 + (s ^ 2 / r) / 8 := by
    refine ctl_lamO_le (by positivity) (fun i j hij => ?_)
    rw [resolventC_offDiag_eq hH h0 hij, ← ctl_form_eq, norm_mul, norm_mul, norm_neg]
    have hS : ‖ctlForm {i, j} z i j ω‖ ≤ s ^ 2 * (1 / q + 1 / (2 * r)) :=
      (not_lt.mp (hbil i j hij)).trans (by
        gcongr
        exact lge_brkBil_le (ctlMinor {i, j} z ω) hq1 hN (hB1 _) (hB2 _))
    have hh : ‖((symOfEntries ω i j : ℝ) : ℂ)‖ ≤ 1 / q := by
      rw [Complex.norm_real, Real.norm_eq_abs, ← one_div] at *
      exact hoff i j hij
    have hg1 : ‖resolventC (symOfEntries ω) z i i‖ ≤ 1 / 2 := lge_norm_resolventC_le hH hz i i
    have hg2 : ‖resolventC (zeroRC {i} (symOfEntries ω)) z j j‖ ≤ 1 / 2 :=
      lge_norm_resolventC_le (zeroRC_isHermitian hH {i}) hz j j
    have hd : ‖((symOfEntries ω i j : ℝ) : ℂ) - ctlForm {i, j} z i j ω‖ ≤
        1 / q + s ^ 2 * (1 / q + 1 / (2 * r)) :=
      (norm_sub_le _ _).trans (add_le_add hh hS)
    have hn1 := norm_nonneg (resolventC (symOfEntries ω) z i i)
    have hn2 := norm_nonneg (resolventC (zeroRC {i} (symOfEntries ω)) z j j)
    calc ‖resolventC (symOfEntries ω) z i i‖ *
          ‖resolventC (zeroRC {i} (symOfEntries ω)) z j j‖ *
          ‖((symOfEntries ω i j : ℝ) : ℂ) - ctlForm {i, j} z i j ω‖
        ≤ (1 / 2) * (1 / 2) * (1 / q + s ^ 2 * (1 / q + 1 / (2 * r))) := by gcongr
      _ ≤ (s ^ 2 / q) / 2 + (s ^ 2 / r) / 8 := by
        have : s ^ 2 * (1 / q + 1 / (2 * r)) = s ^ 2 / q + (s ^ 2 / r) / 2 := by
          field_simp
        rw [this]
        linarith
  -- the diagonal terms
  have hU : ∀ i, ‖upsilon (symOfEntries ω) z i‖ ≤ 5 / 2 * (s ^ 2 / q) + s ^ 2 / r := by
    intro i
    have hhd : ‖((symOfEntries ω i i : ℝ) : ℂ)‖ ≤ 1 / q := by
      rw [Complex.norm_real, Real.norm_eq_abs, ← one_div] at *
      exact hdiag i
    have hA := lge_norm_aCorr_le hH hz hN i
    have hZi := hZ i
    unfold upsilon
    have h6 : ‖((symOfEntries ω i i : ℝ) : ℂ) - zFluct (symOfEntries ω) z i +
        aCorr (symOfEntries ω) z i‖ ≤ ‖((symOfEntries ω i i : ℝ) : ℂ)‖ +
          ‖zFluct (symOfEntries ω) z i‖ + ‖aCorr (symOfEntries ω) z i‖ := by
      refine (norm_add_le _ _).trans ?_
      have := norm_sub_le ((symOfEntries ω i i : ℝ) : ℂ) (zFluct (symOfEntries ω) z i)
      linarith
    rw [e3, e4] at hZi
    linarith
  have hD := lge_lamD_le hH hz hN hU
  linarith

/-- On `Ω(z)` at `η ≥ 2`, the bounds for `Λ_o` and `Z_i` give the bound for `Λ_d + Λ_o`. -/
private lemma lge_final {ω : Entries N} (hN : 0 < N) (hz : 2 ≤ z.im) {q s C1 C2 : ℝ}
    (hq1 : 1 ≤ q) (hs1 : 1 ≤ s) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hdiag : ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹)
    (hΩ : lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹)
    (hΛ : lamO (symOfEntries ω) z ≤ C1 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z))
    (hZ : (⨆ i, ‖zFluct (symOfEntries ω) z i‖) ≤
      C2 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z)) :
    lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤
      (C1 + C2 + 1) * (s / q + s ^ 2 / Real.sqrt N) := by
  have hH : (symOfEntries ω).IsHermitian := symOfEntries_isHermitian ω
  have h0 : 0 < z.im := by linarith
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hrsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNr.le
  have hr1 : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN
  set r := Real.sqrt N with hr
  have hO0 := ctl_lamO_nonneg (symOfEntries ω) z
  have hD0 := ctl_lamD_nonneg (symOfEntries ω) z
  have hsinv : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hDle : lamD (symOfEntries ω) z ≤ 1 := by linarith
  -- `Ψ ≤ N^{-1/2}`
  have hΨ : psiCtrl (symOfEntries ω) z ≤ 1 / r := by
    unfold psiCtrl
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hav : lamAvg (symOfEntries ω) z ≤ 1 :=
      (lge_norm_stieltjesM_sub_le hN).trans hDle
    have him : (msc z).im ≤ 1 / 2 :=
      ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (lge_norm_msc_le hz)
    have hnum : lamAvg (symOfEntries ω) z + (msc z).im ≤ 3 / 2 := by linarith
    have hnum0 : 0 ≤ lamAvg (symOfEntries ω) z + (msc z).im := by
      have : 0 ≤ lamAvg (symOfEntries ω) z := norm_nonneg _
      have := im_msc_pos h0
      linarith
    calc (lamAvg (symOfEntries ω) z + (msc z).im) / (N * z.im)
        ≤ (3 / 2) / (N * 2) := by
          apply div_le_div₀ (by norm_num) hnum (by positivity) (by nlinarith)
      _ ≤ (1 / r) ^ 2 := by
          rw [div_pow, ← hrsq]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg r]
  have hΨ0 : 0 ≤ psiCtrl (symOfEntries ω) z := Real.sqrt_nonneg _
  set X := s / q + s ^ 2 / r with hX
  have hX0 : 0 ≤ X := by positivity
  have e1 : 1 / q ≤ s / q := div_le_div_of_nonneg_right hs1 hq0.le
  have e2 : s ^ 2 * psiCtrl (symOfEntries ω) z ≤ s ^ 2 / r := by
    rw [div_eq_mul_one_div]
    gcongr
  have e3 : 1 / (2 * (N : ℝ)) ≤ s ^ 2 / r := by
    rw [← hrsq]
    have h1 : 1 / (2 * r ^ 2) ≤ 1 / r :=
      one_div_le_one_div_of_le hr0 (by nlinarith)
    have h2 : 1 / r ≤ s ^ 2 / r := div_le_div_of_nonneg_right (by nlinarith) hr0.le
    exact h1.trans h2
  have hΛX : lamO (symOfEntries ω) z ≤ C1 * X := by
    refine hΛ.trans ?_
    gcongr
    linarith
  have hZX : ∀ i, ‖zFluct (symOfEntries ω) z i‖ ≤ C2 * X := fun i =>
    (le_ciSup (f := fun i => ‖zFluct (symOfEntries ω) z i‖) (Set.finite_range _).bddAbove i).trans
      (hZ.trans (by gcongr; linarith))
  have hU : ∀ i, ‖upsilon (symOfEntries ω) z i‖ ≤ (1 + C2) * X := by
    intro i
    have hhd : ‖((symOfEntries ω i i : ℝ) : ℂ)‖ ≤ 1 / q := by
      rw [Complex.norm_real, Real.norm_eq_abs, ← one_div] at *
      exact hdiag i
    have hA := lge_norm_aCorr_le hH hz hN i
    have hZi := hZX i
    unfold upsilon
    have h6 : ‖((symOfEntries ω i i : ℝ) : ℂ) - zFluct (symOfEntries ω) z i +
        aCorr (symOfEntries ω) z i‖ ≤ ‖((symOfEntries ω i i : ℝ) : ℂ)‖ +
          ‖zFluct (symOfEntries ω) z i‖ + ‖aCorr (symOfEntries ω) z i‖ := by
      refine (norm_add_le _ _).trans ?_
      have := norm_sub_le ((symOfEntries ω i i : ℝ) : ℂ) (zFluct (symOfEntries ω) z i)
      linarith
    nlinarith
  have hD := lge_lamD_le hH hz hN hU
  nlinarith


/-! ### The large deviation events -/

/-- The union over all indices of the large deviation events for the bilinear forms of (3.34), the
linear forms of (3.19) and the quadratic forms of (3.22) of [15]. -/
private def lgeBadLD (N : ℕ) (q s : ℝ) (z : ℂ) : Set (Entries N) :=
  (⋃ p ∈ (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2),
      ctlBadBil {p.1, p.2} q s z p.1 p.2) ∪
    ⋃ i ∈ (Finset.univ : Finset (Fin N)), (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i)

/-- The union of the large deviation events has probability at most `e^{-s/(2C)}`. -/
private lemma lge_LD_prob :
    ∃ CC > 0, ∀ {N : ℕ} {L : EntryLaws N} {C0 q : ℝ}, L.IsGenWigner C0 → L.BoundedSupportAS q →
      3 ≤ N → 1 ≤ q → ∀ {z : ℂ}, 0 < z.im → ∀ s : ℝ, 0 < s →
      2 * CC * (Real.log (3 * (N : ℝ) ^ 2) + |Real.log CC|) ≤ s →
      L.law (lgeBadLD N q s z) ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * CC)) * s)) := by
  obtain ⟨CP, hCP, hpair⟩ := ctl_pair_le
  obtain ⟨CL, hCL, hlin⟩ := ctl_lin_le
  obtain ⟨CQ, hCQ, hquad⟩ := ctl_quad_le
  refine ⟨CP + CL + CQ, by positivity, ?_⟩
  intro N L C0 q hL hq hN3 hq1 z hz s hs0 hunion
  have hCC : 0 < CP + CL + CQ := by positivity
  set CC := CP + CL + CQ with hCCdef
  have hNpos : 0 < N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hy0 : 0 ≤ CC * Real.exp (-s / CC) := by positivity
  set P : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 ≠ p.2 with hP
  have hbil : ∀ p ∈ P, L.law (ctlBadBil {p.1, p.2} q s z p.1 p.2) ≤
      ENNReal.ofReal (CC * Real.exp (-s / CC)) := by
    intro p hp
    have hp' : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hcard : 0 < (({p.1, p.2} : Finset (Fin N))ᶜ).card := by
      rw [ctl_card_compl_pair hp']
      omega
    exact (hpair hL hq hq1 hz {p.1, p.2} (by simp) (by simp) hp' hcard s hs0).trans
      (ENNReal.ofReal_le_ofReal (ctl_exp_mono_C hCP (by linarith) hs0.le))
  have hone : ∀ i : Fin N, L.law (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i) ≤
      ENNReal.ofReal (2 * (CC * Real.exp (-s / CC))) := by
    intro i
    have hcard : 0 < (({i} : Finset (Fin N))ᶜ).card := by
      rw [ctl_card_compl_single]
      omega
    have h1 : L.law (ctlBadLin {i} q s z i) ≤ ENNReal.ofReal (CC * Real.exp (-s / CC)) :=
      (hlin hL hq hq1 (by omega) hz {i} (Finset.mem_singleton_self i) hcard s hs0).trans
        (ENNReal.ofReal_le_ofReal (ctl_exp_mono_C hCL (by linarith) hs0.le))
    have h2 : L.law (ctlBadQuad {i} q s z i) ≤ ENNReal.ofReal (CC * Real.exp (-s / CC)) :=
      (hquad hL hq hq1 hz {i} (Finset.mem_singleton_self i) s hs0).trans
        (ENNReal.ofReal_le_ofReal (ctl_exp_mono_C hCQ (by linarith) hs0.le))
    calc L.law (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i)
        ≤ L.law (ctlBadLin {i} q s z i) + L.law (ctlBadQuad {i} q s z i) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (CC * Real.exp (-s / CC)) + ENNReal.ofReal (CC * Real.exp (-s / CC)) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (2 * (CC * Real.exp (-s / CC))) := by
          rw [← ENNReal.ofReal_add hy0 hy0]
          ring_nf
  have hA : L.law (⋃ p ∈ P, ctlBadBil {p.1, p.2} q s z p.1 p.2) ≤
      ENNReal.ofReal ((N : ℝ) ^ 2 * (CC * Real.exp (-s / CC))) :=
    calc L.law (⋃ p ∈ P, ctlBadBil {p.1, p.2} q s z p.1 p.2)
        ≤ ∑ p ∈ P, L.law (ctlBadBil {p.1, p.2} q s z p.1 p.2) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ P, ENNReal.ofReal (CC * Real.exp (-s / CC)) := Finset.sum_le_sum hbil
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * (CC * Real.exp (-s / CC))) := ctl_pairs_sum_le N hy0
  have hB : L.law (⋃ i ∈ (Finset.univ : Finset (Fin N)),
      (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i)) ≤
      ENNReal.ofReal ((N : ℝ) * (2 * (CC * Real.exp (-s / CC)))) :=
    calc L.law (⋃ i ∈ (Finset.univ : Finset (Fin N)),
          (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i))
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)),
            L.law (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin N)), ENNReal.ofReal (2 * (CC * Real.exp (-s / CC))) :=
          Finset.sum_le_sum fun i _ => hone i
      _ = ENNReal.ofReal ((N : ℝ) * (2 * (CC * Real.exp (-s / CC)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hM : (1 : ℝ) ≤ 3 * (N : ℝ) ^ 2 := by nlinarith
  have hfin : (N : ℝ) ^ 2 * (CC * Real.exp (-s / CC)) + (N : ℝ) * (2 * (CC * Real.exp (-s / CC))) ≤
      Real.exp (-(1 / (2 * CC)) * s) := by
    have hu := ctl_union_bound hCC hM hunion
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hNN hy0]
  calc L.law (lgeBadLD N q s z)
      ≤ L.law (⋃ p ∈ P, ctlBadBil {p.1, p.2} q s z p.1 p.2) +
        L.law (⋃ i ∈ (Finset.univ : Finset (Fin N)),
          (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * (CC * Real.exp (-s / CC))) +
        ENNReal.ofReal ((N : ℝ) * (2 * (CC * Real.exp (-s / CC)))) := add_le_add hA hB
    _ = ENNReal.ofReal ((N : ℝ) ^ 2 * (CC * Real.exp (-s / CC)) +
        (N : ℝ) * (2 * (CC * Real.exp (-s / CC)))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * CC)) * s)) := ENNReal.ofReal_le_ofReal hfin

/-! ### The deterministic inclusion -/

/-- Off the large deviation events and the two exceptional sets of the level estimates, `Λ_d + Λ_o`
is at most `C (s/q + s²/√N)`. -/
private lemma lge_good {ω : Entries N} (hN : 0 < N) (hz : 2 ≤ z.im) {q s C1 C2 : ℝ}
    (hq1 : 1 ≤ q) (hs1 : 1 ≤ s) (hC1 : 0 < C1) (hC2 : 0 < C2) (hq4 : 4 * s ^ 3 ≤ q)
    (hr4 : 2 * s ^ 3 ≤ Real.sqrt N)
    (hoff : ∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹)
    (hdiag : ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹)
    (hLD : ω ∉ lgeBadLD N q s z)
    (hE1 : ¬ (lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
      C1 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z))
    (hE2 : ¬ (lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
      C2 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < ⨆ i, ‖zFluct (symOfEntries ω) z i‖)) :
    lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤
      (C1 + C2 + 1) * (s / q + s ^ 2 / Real.sqrt N) := by
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < Real.sqrt N := lt_of_lt_of_le (by positivity) hr4
  have hLD' : ω ∉ (⋃ p ∈ (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2),
      ctlBadBil {p.1, p.2} q s z p.1 p.2) ∧
      ω ∉ ⋃ i ∈ (Finset.univ : Finset (Fin N)),
        (ctlBadLin {i} q s z i ∪ ctlBadQuad {i} q s z i) := by
    unfold lgeBadLD at hLD
    rw [Set.mem_union, not_or] at hLD
    exact hLD
  have hbil : ∀ i j : Fin N, i ≠ j → ω ∉ ctlBadBil {i, j} q s z i j := fun i j hij h =>
    hLD'.1 (Set.mem_iUnion₂.2 ⟨(i, j), by simp [hij], h⟩)
  have hlin : ∀ i : Fin N, ω ∉ ctlBadLin {i} q s z i := fun i h =>
    hLD'.2 (Set.mem_iUnion₂.2 ⟨i, Finset.mem_univ i, Or.inl h⟩)
  have hquad : ∀ i : Fin N, ω ∉ ctlBadQuad {i} q s z i := fun i h =>
    hLD'.2 (Set.mem_iUnion₂.2 ⟨i, Finset.mem_univ i, Or.inr h⟩)
  have hcrude := lge_crude hN hz hq1 hs1 hoff hdiag hbil hlin hquad
  have hΩ : lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ := by
    refine hcrude.trans ?_
    have k1 : s ^ 2 / q ≤ 1 / (4 * s) := by
      rw [div_le_div_iff₀ hq0 (by positivity)]
      nlinarith
    have k2 : s ^ 2 / Real.sqrt N ≤ 1 / (2 * s) := by
      rw [div_le_div_iff₀ hr0 (by positivity)]
      nlinarith
    have k3 : 2 * (1 / (4 * s)) + 1 / (2 * s) = s⁻¹ := by
      field_simp
      ring
    linarith
  have hΛ : lamO (symOfEntries ω) z ≤ C1 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
    not_lt.mp fun hlt => hE1 ⟨hΩ, hlt⟩
  have hZ : (⨆ i, ‖zFluct (symOfEntries ω) z i‖) ≤
      C2 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) :=
    not_lt.mp fun hlt => hE2 ⟨hΩ, hlt⟩
  exact lge_final hN hz hq1 hs1 hC1 hC2 hdiag hΩ hΛ hZ

end Deterministic

/-! ### Parameters -/

/-- The conditions on `N` used for the parameters `s = φ^ζ`, `q ≥ φ^K`. -/
private lemma lge_eventually {ζ : ℝ} (hζ : 0 < ζ) (K1 K2 B : ℝ) (N1 N2 : ℕ) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ B * (Real.log N + 1) ≤ phi N ^ ζ ∧ 4 ≤ phi N ∧
      phi N ^ K1 ≤ N ∧ phi N ^ K2 ≤ N ∧ phi N ^ (3 * ζ + 1) ≤ Real.sqrt N ∧ N1 ≤ N ∧ N2 ≤ N := by
  filter_upwards [eventually_mul_log_add_one_le_phi_rpow hζ B,
    eventually_mul_log_add_one_le_phi_rpow (a := 1) one_pos 4, phi_rpow_le_rpow K1 one_pos,
    phi_rpow_le_rpow K2 one_pos,
    phi_rpow_le_rpow (3 * ζ + 1) (c := 1 / 2) (by norm_num), eventually_ge_atTop N1,
    eventually_ge_atTop N2] with N hB h4 hK1 hK2 h3 hN1 hN2
  refine ⟨hB.1, hB.2, ?_, by simpa using hK1, by simpa using hK2, ?_, hN1, hN2⟩
  · have := h4.2
    rw [Real.rpow_one] at this
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have h4' : (4 : ℝ) ≤ 4 * (Real.log N + 1) := by linarith
    exact h4'.trans this
  · rw [Real.sqrt_eq_rpow]
    exact h3

/-- The parameter inequalities `q ≥ 4 s³` and `√N ≥ 2 s³` for `s = φ^ζ`. -/
private lemma lge_param_arith {N : ℕ} {ζ q : ℝ} (hζ : 0 < ζ) (hN3 : 3 ≤ N) (hφ4 : 4 ≤ phi N)
    (hq : phi N ^ (3 * ζ + 1) ≤ q) (hr : phi N ^ (3 * ζ + 1) ≤ Real.sqrt N) :
    1 ≤ phi N ^ ζ ∧ 4 * (phi N ^ ζ) ^ 3 ≤ q ∧ 2 * (phi N ^ ζ) ^ 3 ≤ Real.sqrt N := by
  have hφ0 : 0 < phi N := ctl_phi_pos hN3
  have hs1 : 1 ≤ phi N ^ ζ := Real.one_le_rpow (ctl_one_le_phi hN3) hζ.le
  have hs3 : (phi N ^ ζ) ^ 3 = phi N ^ (3 * ζ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hφ0.le]
    congr 1
    push_cast
    ring
  have hφ3' : phi N ^ (3 * ζ + 1) = phi N ^ (3 * ζ) * phi N := by
    rw [Real.rpow_add hφ0, Real.rpow_one]
  have hs3pos : 0 < (phi N ^ ζ) ^ 3 := by positivity
  have hmain3 : 4 * (phi N ^ ζ) ^ 3 ≤ phi N ^ (3 * ζ + 1) := by
    rw [hφ3', ← hs3]
    nlinarith [mul_nonneg hs3pos.le (sub_nonneg.2 hφ4)]
  exact ⟨hs1, hmain3.trans hq, by linarith⟩

/-- Membership of `z` in `specDomain` for `2 ≤ η ≤ 10` once `φ^K ≤ N`. -/
private lemma lge_specDomain {N : ℕ} (hN : 0 < N) {K : ℝ} {z : ℂ} (hre : |z.re| ≤ 5)
    (him : 2 ≤ z.im) (hzle : z.im ≤ 10) (hK : phi N ^ K ≤ N) : z ∈ specDomain N K := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨hre, ?_, hzle⟩
  rw [div_lt_iff₀ hNr]
  nlinarith

/-- The probabilities of the finitely many events add up. -/
private lemma lge_exp_sum {a b c s : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : 4 / min (min a b) c ≤ s) :
    ENNReal.ofReal (Real.exp (-a * s)) + ENNReal.ofReal (Real.exp (-b * s)) +
      ENNReal.ofReal (Real.exp (-c * s)) ≤
      ENNReal.ofReal (Real.exp (-(min (min a b) c / 4) * s)) := by
  have hm0 : 0 < min (min a b) c := lt_min (lt_min ha hb) hc
  set m := min (min a b) c with hm
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have h2m : 2 / m ≤ s := le_trans (div_le_div_of_nonneg_right (by norm_num) hm0.le) hs
  have h4m : 2 / (m / 2) ≤ s := by
    rw [show 2 / (m / 2) = 4 / m by field_simp; norm_num]
    exact hs
  have hxa : Real.exp (-a * s) ≤ Real.exp (-m * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left (min a b) c, min_le_left a b]
  have hxb : Real.exp (-b * s) ≤ Real.exp (-m * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left (min a b) c, min_le_right a b]
  have hxc : Real.exp (-c * s) ≤ Real.exp (-m * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right (min a b) c]
  have h12 := add_le_exp_neg_half_mul_of_le_exp hm0 h2m hxa hxb
  have hm' : Real.exp (-m * s) ≤ Real.exp (-(m / 2) * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h123 := add_le_exp_neg_half_mul_of_le_exp (half_pos hm0) h4m h12 (hxc.trans hm')
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal (h123.trans (le_of_eq ?_))
  congr 2
  ring

/-- The measure of a set covered by four sets. -/
private lemma lge_law_le {N : ℕ} {L : EntryLaws N} {S A B C D : Set (Entries N)}
    (h : S ⊆ A ∪ B ∪ C ∪ D) : L.law S ≤ L.law A + L.law B + L.law C + L.law D :=
  (measure_mono h).trans <| (measure_union_le _ _).trans <| add_le_add
    ((measure_union_le _ _).trans <| add_le_add (measure_union_le _ _) le_rfl) le_rfl

/-- Initial estimate for `2 ≤ η ≤ 10` (Lemma 3.16 of [15], extended to `η ≤ 10`). -/
theorem initial_large_eta {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ) (z : ℂ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ K ≤ q → |z.re| ≤ 5 → 2 ≤ z.im →
      z.im ≤ 10 →
      L.law {ω | C * (phi N ^ ζ / q + phi N ^ (2 * ζ) / Real.sqrt N) <
        lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ≤
        ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  obtain ⟨K1, hK1, C1, hC1, c1, hc1, N1, h1⟩ := lamO_le_on_omega_level hζ hC0
  obtain ⟨K2, hK2, C2, hC2, c2, hc2, N2, h2⟩ := norm_zFluct_le_on_omega hζ hC0
  obtain ⟨CC, hCC, hLD⟩ := lge_LD_prob
  set c' : ℝ := min (min (1 / (2 * CC)) c1) c2 with hc'
  have hc'0 : 0 < c' := lt_min (lt_min (by positivity) hc1) hc2
  set Kr : ℝ := max (max K1 K2) (3 * ζ + 1) with hKr
  have hKr0 : 0 < Kr := lt_max_of_lt_right (by linarith)
  set B : ℝ := 4 * CC + 2 * CC * (Real.log 3 + |Real.log CC|) + 4 / c' with hB
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (lge_eventually hζ K1 K2 B N1 N2)
  refine ⟨⌈Kr⌉₊, Nat.ceil_pos.mpr hKr0, C1 + C2 + 1, by positivity, c' / 4, by positivity, N0, ?_⟩
  intro N hN L q z hL hq hqK hre him hzle
  obtain ⟨hN3, hBs, hφ4, hφK1, hφK2, hφ3, hN1, hN2⟩ := hN0 N hN
  have hNpos : 0 < N := by omega
  have hφ0 : 0 < phi N := ctl_phi_pos hN3
  rw [← ctl_rpow_sq hφ0 ζ]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = phi N ^ ζ := ⟨_, rfl⟩
  rw [← hs]
  have hqKr : phi N ^ Kr ≤ q := by
    have h1' : phi N ^ Kr ≤ phi N ^ ((⌈Kr⌉₊ : ℕ) : ℝ) := ctl_rpow_mono hN3 (Nat.le_ceil Kr)
    rw [Real.rpow_natCast] at h1'
    exact h1'.trans hqK
  have hqK1 : phi N ^ K1 ≤ q :=
    (ctl_rpow_mono hN3 (le_trans (le_max_left _ _) (le_max_left _ _))).trans hqKr
  have hqK2 : phi N ^ K2 ≤ q :=
    (ctl_rpow_mono hN3 (le_trans (le_max_right _ _) (le_max_left _ _))).trans hqKr
  have hqK3 : phi N ^ (3 * ζ + 1) ≤ q :=
    (ctl_rpow_mono hN3 (le_max_right _ _)).trans hqKr
  obtain ⟨hs1', hq4', hr4'⟩ := lge_param_arith hζ hN3 hφ4 hqK3 hφ3
  rw [← hs] at hs1' hq4' hr4'
  have hs1 : 1 ≤ s := hs1'
  have hs0 : 0 < s := by linarith
  have hq4 : 4 * s ^ 3 ≤ q := hq4'
  have hr4 : 2 * s ^ 3 ≤ Real.sqrt N := hr4'
  have hq1 : 1 ≤ q := by nlinarith [one_le_pow₀ hs1 (n := 3)]
  have him0 : 0 < z.im := by linarith
  have hz1 : z ∈ specDomain N K1 := lge_specDomain hNpos hre him hzle hφK1
  have hz2 : z ∈ specDomain N K2 := lge_specDomain hNpos hre him hzle hφK2
  have hsK : s ≤ phi N ^ (ζ + 3) := by
    rw [hs]
    exact ctl_rpow_mono hN3 (by linarith)
  -- thresholds for the exponential bounds
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hBs' : B * (Real.log N + 1) ≤ s := by rw [hs]; exact hBs
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hCpos : 0 ≤ 2 * CC * (Real.log 3 + |Real.log CC|) := by positivity
  have hcpos : 0 ≤ 4 / c' := by positivity
  have hB1 : 4 * CC ≤ B := by linarith
  have hB2 : 2 * CC * (Real.log 3 + |Real.log CC|) ≤ B := by linarith
  have hB3 : 4 / c' ≤ B := by linarith
  have hunion : 2 * CC * (Real.log (3 * (N : ℝ) ^ 2) + |Real.log CC|) ≤ s := by
    have e : Real.log (3 * (N : ℝ) ^ 2) = Real.log 3 + 2 * Real.log N := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    rw [e]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.2 hB1)]
  have hs4c : 4 / c' ≤ s := by
    nlinarith [mul_nonneg hlog0 (show 0 ≤ B by linarith)]
  -- the three probability bounds
  have hP0 := hLD hL hq hN3 hq1 him0 s hs0 hunion
  have hP1 := h1 N hN1 L q s z hL hq hqK1 hz1 hs.ge hsK
  have hP2 := h2 N hN2 L q s z hL hq hqK2 hz2 hs.ge hsK
  have hnull : L.law {ω | ¬ ((∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹) ∧
      ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹)} = 0 :=
    ae_iff.mp ((ctl_ae_entries hL.isProb hq).and (ctl_ae_diag_entries hL.isProb hq))
  have hsub : {ω | (C1 + C2 + 1) * (s / q + s ^ 2 / Real.sqrt N) <
      lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ⊆
      lgeBadLD N q s z ∪
      {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C1 * (1 / q + s ^ 2 * psiCtrl (symOfEntries ω) z) < lamO (symOfEntries ω) z} ∪
      {ω | lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ ∧
        C2 * (s / q + s ^ 2 * psiCtrl (symOfEntries ω) z) <
          ⨆ i, ‖zFluct (symOfEntries ω) z i‖} ∪
      {ω | ¬ ((∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹) ∧
        ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹)} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨⟨hn0, hn1⟩, hn2⟩, hn3⟩ := hcon
    have hn3' : (∀ i j : Fin N, i ≠ j → |symOfEntries ω i j| ≤ q⁻¹) ∧
        ∀ i : Fin N, |symOfEntries ω i i| ≤ q⁻¹ := not_not.mp hn3
    have := lge_good hNpos him hq1 hs1 hC1 hC2 hq4 hr4 hn3'.1 hn3'.2 hn0 hn1 hn2
    exact absurd hω (not_lt.mpr this)
  calc L.law {ω | (C1 + C2 + 1) * (s / q + s ^ 2 / Real.sqrt N) <
        lamD (symOfEntries ω) z + lamO (symOfEntries ω) z}
      ≤ _ := lge_law_le hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * CC)) * s)) + ENNReal.ofReal (Real.exp (-c1 * s)) +
        ENNReal.ofReal (Real.exp (-c2 * s)) + 0 := by
      rw [← hnull]
      exact add_le_add (add_le_add (add_le_add hP0 hP1) hP2) le_rfl
    _ ≤ ENNReal.ofReal (Real.exp (-(c' / 4) * s)) := by
      rw [add_zero]
      exact lge_exp_sum (by positivity) hc1 hc2 hs4c

/-- For all large `N` the hypotheses of `initial_large_eta` hold together for the Rademacher entry
laws (off-diagonal entries `±N^{-1/2}`, diagonal entries `±(2/N)^{1/2}`), `q = N^{2/5}`, `C0 = 1`
and `z = 2i`, and the estimate holds for them. -/
example {ζ : ℝ} (hζ : 0 < ζ) : ∃ K > (0 : ℕ), ∃ C > 0, ∃ c > 0, ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ K ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧ |(⟨0, 2⟩ : ℂ).re| ≤ 5 ∧ 2 ≤ (⟨0, 2⟩ : ℂ).im ∧
    (⟨0, 2⟩ : ℂ).im ≤ 10 ∧
    (radLaws N).law {ω | C * (phi N ^ ζ / (N : ℝ) ^ (2 / 5 : ℝ) +
        phi N ^ (2 * ζ) / Real.sqrt N) <
      lamD (symOfEntries ω) ⟨0, 2⟩ + lamO (symOfEntries ω) ⟨0, 2⟩} ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  obtain ⟨K, hK, C, hC, c, hc, N0, h⟩ := initial_large_eta hζ (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [phi_rpow_le_rpow (K : ℝ) (c := 2 / 5) (by norm_num),
    eventually_ge_atTop (max N0 32)] with N h1 h2
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) h2
  have hN32 : 32 ≤ N := le_trans (le_max_right _ _) h2
  have hGW : (radLaws N).IsGenWigner 1 := radLaws_isGenWigner (by omega)
  have hBS := radLaws_boundedSupportAS hN32
  have hK' : phi N ^ K ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact h1
  have hre : |(⟨0, 2⟩ : ℂ).re| ≤ 5 := by norm_num
  have him : 2 ≤ (⟨0, 2⟩ : ℂ).im := le_refl _
  have him' : (⟨0, 2⟩ : ℂ).im ≤ 10 := by norm_num
  exact ⟨hGW, hBS, hK', hre, him, him',
    h N hN0 (radLaws N) _ ⟨0, 2⟩ hGW hBS hK' hre him him'⟩

#print axioms initial_large_eta


end WEdgeNS
