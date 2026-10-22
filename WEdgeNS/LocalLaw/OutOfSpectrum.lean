import WEdgeNS.LocalLaw.Outside
import WEdgeNS.LocalLaw.Truncation

/-!
# Resolvent bounds outside the spectrum (Lemma 3.1 (5))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- The window grid and the `η`-comparison lemmas of the outside estimates, the bound `1 ≤ φ`, and
-- the Rademacher instance of the self-consistent estimates.
open private outsideGrid outsideGridE outsideGridE_abs outsideGrid_card outside_grid
  outside_eta_diff outside_eta_facts from WEdgeNS.LocalLaw.Outside
open private sc_one_le_phi sc_rad_instance from WEdgeNS.LocalLaw.SelfConsistent

/-! ### Perturbation of the resolvent by a small change of the entries

Throughout, `H` is the matrix of the entries `ω` and `Ĥ` is the matrix of the truncated entries
`T ω` (Definition 2.4, truncation at level `q⁻¹`), whose entries differ from those of `H` by at most
`κt`. -/

/-- The complex matrix `H - z`. -/
private def oosShift {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)

private lemma oos_shift_mul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : oosShift H z * resolventC H z = 1 :=
  resolventC_mul_eq_one hH fun α h => by
    have := congrArg Complex.im h
    rw [Complex.ofReal_im] at this
    linarith

private lemma oos_mul_shift {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : resolventC H z * oosShift H z = 1 :=
  mul_eq_one_comm.mp (oos_shift_mul hH hz)

/-- The second resolvent identity `G - G' = G (H' - H) G'`. -/
private lemma oos_resolvent_sub {N : ℕ} {H H' : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    resolventC H z - resolventC H' z =
      resolventC H z * (H'.map (fun x : ℝ => (x : ℂ)) - H.map (fun x : ℝ => (x : ℂ))) *
        resolventC H' z := by
  have h1 := oos_mul_shift hH hz
  have h2 := oos_shift_mul hH' hz
  have e : H'.map (fun x : ℝ => (x : ℂ)) - H.map (fun x : ℝ => (x : ℂ)) =
      oosShift H' z - oosShift H z := by
    unfold oosShift; abel
  rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (resolventC H z) (oosShift H' z),
    h2, h1]
  simp

/-- Entrywise perturbation of the resolvent: `|G_ij - G'_ij| ≤ N² κ / η²` when the entries of
`H` and `H'` differ by at most `κ`. -/
private lemma oos_norm_resolvent_sub_le {N : ℕ} {H H' : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {κ : ℝ} (hd : ∀ i j, |H i j - H' i j| ≤ κ)
    {z : ℂ} (hz : 0 < z.im) (i j : Fin N) :
    ‖resolventC H z i j - resolventC H' z i j‖ ≤ (N : ℝ) ^ 2 * κ / z.im ^ 2 := by
  have hent : resolventC H z i j - resolventC H' z i j =
      ∑ l, ∑ k, resolventC H z i k * ((H' k l - H k l : ℝ) : ℂ) * resolventC H' z l j := by
    have := congrFun (congrFun (oos_resolvent_sub hH hH' hz) i) j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply] at this
    rw [this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  have hη2 : 0 < z.im ^ 2 := by positivity
  have hterm : ∀ k l, ‖resolventC H z i k * ((H' k l - H k l : ℝ) : ℂ) * resolventC H' z l j‖ ≤
      κ / z.im ^ 2 := by
    intro k l
    have h1 := norm_resolventC_apply_le hH hz i k
    have h2 := norm_resolventC_apply_le hH' hz l j
    have h3 := hd k l
    have hκ : 0 ≤ κ := (abs_nonneg _).trans h3
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    calc ‖resolventC H z i k‖ * |H k l - H' k l| * ‖resolventC H' z l j‖
        ≤ (1 / z.im) * κ * (1 / z.im) := by gcongr
      _ = κ / z.im ^ 2 := by field_simp
  rw [hent]
  calc ‖∑ l, ∑ k, resolventC H z i k * ((H' k l - H k l : ℝ) : ℂ) * resolventC H' z l j‖
      ≤ ∑ l, ‖∑ k, resolventC H z i k * ((H' k l - H k l : ℝ) : ℂ) * resolventC H' z l j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ l, ∑ k, ‖resolventC H z i k * ((H' k l - H k l : ℝ) : ℂ) * resolventC H' z l j‖ :=
        Finset.sum_le_sum fun l _ => norm_sum_le _ _
    _ ≤ ∑ _l : Fin N, ∑ _k : Fin N, κ / z.im ^ 2 :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => hterm k l
    _ = (N : ℝ) ^ 2 * κ / z.im ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The same bound for the Stieltjes transform `m = N⁻¹ Tr G`. -/
private lemma oos_norm_stieltjes_sub_le {N : ℕ} (hN : 0 < N) {H H' : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {κ : ℝ} (hd : ∀ i j, |H i j - H' i j| ≤ κ)
    {z : ℂ} (hz : 0 < z.im) :
    ‖stieltjesM H z - stieltjesM H' z‖ ≤ (N : ℝ) ^ 2 * κ / z.im ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h : stieltjesM H z - stieltjesM H' z =
      (N : ℂ)⁻¹ * ∑ i, (resolventC H z i i - resolventC H' z i i) := by
    unfold stieltjesM
    rw [Finset.sum_sub_distrib, ← mul_sub]
    rfl
  rw [h, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ i, (resolventC H z i i - resolventC H' z i i)‖ ≤
      N * ((N : ℝ) ^ 2 * κ / z.im ^ 2) := by
    calc ‖∑ i, (resolventC H z i i - resolventC H' z i i)‖
        ≤ ∑ i, ‖resolventC H z i i - resolventC H' z i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, (N : ℝ) ^ 2 * κ / z.im ^ 2 :=
          Finset.sum_le_sum fun i _ => oos_norm_resolvent_sub_le hH hH' hd hz i i
      _ = N * ((N : ℝ) ^ 2 * κ / z.im ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (N : ℝ)⁻¹ * ‖∑ i, (resolventC H z i i - resolventC H' z i i)‖
      ≤ (N : ℝ)⁻¹ * (N * ((N : ℝ) ^ 2 * κ / z.im ^ 2)) := by gcongr
    _ = (N : ℝ) ^ 2 * κ / z.im ^ 2 := by field_simp

/-! ### The window of (3.7) -/

/-- On the window `2 + T R ≤ |E| ≤ 3` with `(A V²)² ≤ T`, `ρ² = R` and `ρ³ N = 1`:
`κ = |E| - 2 ∈ (0, 1]`, `ρ ≤ √κ / (A V²)` and `A³ V³ ≤ N κ √κ`. -/
private lemma oos_window {N : ℕ} {A V T R ρ E : ℝ} (hN : (0 : ℝ) < N) (hA : 1 ≤ A) (hV : 1 ≤ V)
    (hρ : 0 < ρ) (hρR : ρ ^ 2 = R) (hρN : ρ ^ 3 * N = 1) (hT : (A * V ^ 2) ^ 2 ≤ T)
    (hwin : 2 + T * R ≤ |E|) (hE3 : |E| ≤ 3) :
    kappa E = |E| - 2 ∧ 0 < Real.sqrt (kappa E) ∧ Real.sqrt (kappa E) ≤ 1 ∧
      ρ ≤ Real.sqrt (kappa E) / (A * V ^ 2) ∧
      A ^ 3 * V ^ 3 ≤ N * kappa E * Real.sqrt (kappa E) := by
  have hA0 : 0 < A := by linarith
  have hV0 : 0 < V := by linarith
  have hAV : 0 < A * V ^ 2 := by positivity
  have hAV2 : 0 < (A * V ^ 2) ^ 2 := by positivity
  have hR0 : 0 < R := by rw [← hρR]; positivity
  have hTR : (A * V ^ 2) ^ 2 * R ≤ T * R := mul_le_mul_of_nonneg_right hT hR0.le
  have hTR0 : 0 < (A * V ^ 2) ^ 2 * R := by positivity
  have hκ : kappa E = |E| - 2 := by
    unfold kappa
    exact abs_of_nonneg (by linarith)
  have hκ0 : 0 < kappa E := by rw [hκ]; linarith
  have hκ1 : kappa E ≤ 1 := by rw [hκ]; linarith
  have hX0 : 0 < Real.sqrt (kappa E) := Real.sqrt_pos.mpr hκ0
  have hX2 : Real.sqrt (kappa E) ^ 2 = kappa E := Real.sq_sqrt hκ0.le
  have hX1 : Real.sqrt (kappa E) ≤ 1 := Real.sqrt_le_one.mpr hκ1
  have hρX : ρ * (A * V ^ 2) ≤ Real.sqrt (kappa E) := by
    rw [Real.le_sqrt' (by positivity)]
    calc (ρ * (A * V ^ 2)) ^ 2 = (A * V ^ 2) ^ 2 * R := by rw [← hρR]; ring
      _ ≤ T * R := hTR
      _ ≤ kappa E := by rw [hκ]; linarith
  refine ⟨hκ, hX0, hX1, ?_, ?_⟩
  · rw [le_div_iff₀ hAV]; exact hρX
  · set X := Real.sqrt (kappa E) with hX
    have h3 : (ρ * (A * V ^ 2)) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by positivity) hρX 3
    have e : N * kappa E * X = N * X ^ 3 := by rw [← hX2]; ring
    rw [e]
    have e2 : (N : ℝ) * (ρ * (A * V ^ 2)) ^ 3 = A ^ 3 * V ^ 6 := by
      have : (N : ℝ) * (ρ * (A * V ^ 2)) ^ 3 = (ρ ^ 3 * N) * (A ^ 3 * V ^ 6) := by ring
      rw [this, hρN, one_mul]
    have h6 : A ^ 3 * V ^ 3 ≤ A ^ 3 * V ^ 6 := by
      have : V ^ 3 ≤ V ^ 6 := pow_le_pow_right₀ hV (by norm_num)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc A ^ 3 * V ^ 3 ≤ A ^ 3 * V ^ 6 := h6
      _ = N * (ρ * (A * V ^ 2)) ^ 3 := e2.symm
      _ ≤ N * X ^ 3 := mul_le_mul_of_nonneg_left h3 hN.le

/-! ### The off-diagonal bound at one point of the window -/

/-- The arithmetic of the third bound of (3.8): with `η = A U⁶ / (N X)`, `Λ ≤ X / (A U¹²)`,
`Im m_sc ≤ C_m η / X`, `C_m A² U¹⁸ ≤ N X³`, `Λ_o ≤ C_o (q⁻¹ + Z² Ψ)` where
`Ψ² = (Λ + Im m_sc) / (N η)`, `C_o q⁻¹ ≤ X / (8 A U⁸)` and `16 C_o Z² ≤ U`, one gets
`Λ_o ≤ X / (4 A U⁸)`. -/
private lemma oos_arith3 {N X A U Z η Cm Co I Λ lam q' : ℝ} (hN : 0 < N) (hX0 : 0 < X)
    (hA : 1 ≤ A) (hU : 1 ≤ U) (hCm : 1 ≤ Cm) (hCo : 0 ≤ Co)
    (hη : η = A * U ^ 6 / (N * X)) (hΛ : Λ ≤ X / (A * U ^ 12))
    (hI : I ≤ Cm * (η / X)) (hNk : Cm * A ^ 2 * U ^ 18 ≤ N * X ^ 3)
    (hlam : lam ≤ Co * (1 / q' + Z ^ 2 * Real.sqrt ((Λ + I) / (N * η))))
    (hq : Co * (1 / q') ≤ X / (8 * (A * U ^ 8))) (hZ : 16 * Co * Z ^ 2 ≤ U) :
    lam ≤ X / (4 * (A * U ^ 8)) := by
  have hA0 : 0 < A := by linarith
  have hU0 : 0 < U := by linarith
  have hAU : 0 < A * U ^ 12 := by positivity
  have hNη : N * η = A * U ^ 6 / X := by rw [hη]; field_simp
  have hNη0 : 0 < N * η := by rw [hNη]; positivity
  -- `Im m_sc ≤ X / (A U¹²)`
  have hI' : I ≤ X / (A * U ^ 12) := by
    refine hI.trans ?_
    have e : Cm * (η / X) = Cm * (A * U ^ 6) / (N * X ^ 2) := by rw [hη]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) hAU]
    calc Cm * (A * U ^ 6) * (A * U ^ 12) = Cm * A ^ 2 * U ^ 18 := by ring
      _ ≤ N * X ^ 3 := hNk
      _ = X * (N * X ^ 2) := by ring
  have hsum : Λ + I ≤ 2 * (X / (A * U ^ 12)) := by linarith
  -- `Ψ ≤ 2 X / (A U⁹)`
  have hΨ : Real.sqrt ((Λ + I) / (N * η)) ≤ 2 * X / (A * U ^ 9) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hNη0, hNη]
    have e : (2 * X / (A * U ^ 9)) ^ 2 * (A * U ^ 6 / X) = 4 * (X / (A * U ^ 12)) := by
      field_simp
      norm_num
    rw [e]
    calc Λ + I ≤ 2 * (X / (A * U ^ 12)) := hsum
      _ ≤ 4 * (X / (A * U ^ 12)) := by
          have : 0 ≤ X / (A * U ^ 12) := by positivity
          linarith
  have hterm : Co * (Z ^ 2 * (2 * X / (A * U ^ 9))) ≤ X / (8 * (A * U ^ 8)) := by
    have e : Co * (Z ^ 2 * (2 * X / (A * U ^ 9))) = (Co * Z ^ 2) * (2 * X / (A * U ^ 9)) := by ring
    rw [e]
    have h1 : Co * Z ^ 2 ≤ U / 16 := by linarith
    have h2 : 0 ≤ 2 * X / (A * U ^ 9) := by positivity
    calc (Co * Z ^ 2) * (2 * X / (A * U ^ 9)) ≤ (U / 16) * (2 * X / (A * U ^ 9)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = X / (8 * (A * U ^ 8)) := by field_simp; ring
  calc lam ≤ Co * (1 / q' + Z ^ 2 * Real.sqrt ((Λ + I) / (N * η))) := hlam
    _ = Co * (1 / q') + Co * (Z ^ 2 * Real.sqrt ((Λ + I) / (N * η))) := by ring
    _ ≤ X / (8 * (A * U ^ 8)) + Co * (Z ^ 2 * (2 * X / (A * U ^ 9))) := by
        refine add_le_add hq (mul_le_mul_of_nonneg_left ?_ hCo)
        exact mul_le_mul_of_nonneg_left hΨ (by positivity)
    _ ≤ X / (8 * (A * U ^ 8)) + X / (8 * (A * U ^ 8)) := add_le_add le_rfl hterm
    _ = X / (4 * (A * U ^ 8)) := by field_simp; ring

/-! ### Asymptotic bounds -/

/-- `N^k exp(-b N^c) → 0`. -/
private lemma oos_tendsto_rpow_mul_exp {c b k : ℝ} (hc : 0 < c) (hb : 0 < b) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-b * (N : ℝ) ^ c)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / c) b hb
  have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  refine (h1.comp h2).congr fun N => ?_
  simp only [Function.comp_apply]
  congr 1
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  field_simp

/-- The truncation error `N⁴ exp(-N^c/4)` is eventually below `N^{-1/3}/4`. -/
private lemma oos_eventually_trunc {c : ℝ} (hc : 0 < c) : ∀ᶠ N : ℕ in atTop,
    4 * ((N : ℝ) ^ 4 * Real.exp (-(N : ℝ) ^ c / 4)) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) := by
  filter_upwards [(oos_tendsto_rpow_mul_exp (k := 13 / 3) hc (b := 1 / 4)
    (by norm_num)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_ge_atTop 1] with N h hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have e1 : (N : ℝ) ^ (13 / 3 : ℝ) = (N : ℝ) ^ 4 * (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (13 / 3 : ℝ) = ((4 : ℕ) : ℝ) + 1 / 3 by norm_num, Real.rpow_add hN0,
      Real.rpow_natCast]
  have e2 : (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hN0]; norm_num
  have e3 : Real.exp (-(1 / 4) * (N : ℝ) ^ c) = Real.exp (-(N : ℝ) ^ c / 4) := by
    congr 1; ring
  rw [e1, e3] at h
  set a := (N : ℝ) ^ 4 * Real.exp (-(N : ℝ) ^ c / 4) with ha
  set s := (N : ℝ) ^ (1 / 3 : ℝ) with hs
  set ρ := (N : ℝ) ^ (-(1 : ℝ) / 3) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hN0 _
  have h' : a * s < 1 / 4 := by
    have : (N : ℝ) ^ 4 * s * Real.exp (-(N : ℝ) ^ c / 4) = a * s := by rw [ha]; ring
    linarith
  calc 4 * a = 4 * (a * (s * ρ)) := by rw [e2]; ring
    _ = 4 * (a * s) * ρ := by ring
    _ ≤ 1 * ρ := by nlinarith
    _ = ρ := one_mul ρ

/-- The truncation error, two events of probability `≤ e^{-m s}` and a union over `M` grid
points add up to `N⁴ e^{-m s}`. -/
private lemma oos_real_bound {N : ℕ} {c m s e1 e2 e3 M : ℝ} (hN : 7 ≤ N) (hm1 : m ≤ 1)
    (hs0 : 0 ≤ s) (he3 : 0 ≤ e3) (h1 : e1 ≤ Real.exp (-m * s)) (h2 : e2 ≤ Real.exp (-m * s))
    (h3 : e3 ≤ Real.exp (-m * s)) (hM0 : 0 ≤ M) (hM : M ≤ 2 * ((N : ℝ) ^ 3 + 1))
    (hst : s ≤ (N : ℝ) ^ (c / 2)) (ht2 : 2 ≤ (N : ℝ) ^ (c / 2))
    (hN2 : 2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c / 2) ≤ 1) :
    2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c) + e1 + e2 + M * e3 ≤
      (N : ℝ) ^ 4 * Real.exp (-m * s) := by
  have hN7 : (7 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set t : ℝ := (N : ℝ) ^ (c / 2) with ht
  have hNc : (N : ℝ) ^ c = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1; push_cast; ring
  set x := Real.exp (-m * s) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hexp : Real.exp (-(N : ℝ) ^ c) ≤ Real.exp (-(N : ℝ) ^ c / 2) * x := by
    rw [hx, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hNc]
    have h1 : m * s ≤ s := by nlinarith
    have h2 : s ≤ t ^ 2 / 2 := by nlinarith
    linarith
  have hE : 2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c) ≤ x := by
    calc 2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c)
        ≤ 2 * (N : ℝ) ^ 2 * (Real.exp (-(N : ℝ) ^ c / 2) * x) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c / 2)) * x := by ring
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right hN2 hx0.le
      _ = x := one_mul x
  have hN3 : 1 ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hMx : M * e3 ≤ (2 * ((N : ℝ) ^ 3 + 1)) * x := mul_le_mul hM h3 he3 (by positivity)
  have h4 : (N : ℝ) ^ 4 = (N : ℝ) * (N : ℝ) ^ 3 := by ring
  have h5 : 2 * (N : ℝ) ^ 3 + 5 ≤ (N : ℝ) ^ 4 := by rw [h4]; nlinarith
  nlinarith

/-! ### The window and the points of the grid -/

/-- The left end `2 + φ^C N^{-2/3}` of the window of (3.7). -/
private def oosWin (N : ℕ) (C : ℝ) : ℝ := 2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)

/-- `ρ = N^{-1/3}` satisfies `ρ² = N^{-2/3}` and `ρ³ N = 1`. -/
private lemma oos_rho {N : ℕ} (hN : (0 : ℝ) < N) :
    0 < (N : ℝ) ^ (-(1 : ℝ) / 3) ∧ ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 = (N : ℝ) ^ (-(2 : ℝ) / 3) ∧
      ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 * N = 1 := by
  refine ⟨Real.rpow_pos_of_pos hN _, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
  · have : ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 = (N : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_neg_one]; norm_num
    rw [this]; field_simp

/-- The facts on one point `z = E + iη` of the window `2 + φ^C N^{-2/3} ≤ |E| ≤ 3` of (3.7), for
`C ≥ 2K + 4a`: with `A = φ^K`, `V = φ^a` and `X = √κ`, one has `κ = |E| - 2 ∈ (0, 1]`,
`N^{-1/3} ≤ X / (A V²)`, `A³ V³ ≤ N κ X`, `η = A V / (N X) ∈ [N⁻¹, κ]`, `A V ≤ N X³`, and
`z ∈ S(K')` for every `K' ≤ K`. -/
private lemma oos_pt {N : ℕ} {K a C E : ℝ} (hN : 256 ≤ N) (hP : 8 ≤ phi N) (hK : 1 ≤ K)
    (ha : 0 < a) (hC : 2 * K + 4 * a ≤ C) (h1 : oosWin N C ≤ |E|) (h2 : |E| ≤ 3) :
    kappa E = |E| - 2 ∧ 0 < Real.sqrt (kappa E) ∧ Real.sqrt (kappa E) ≤ 1 ∧
      (N : ℝ) ^ (-(1 : ℝ) / 3) ≤ Real.sqrt (kappa E) / (phi N ^ K * (phi N ^ a) ^ 2) ∧
      (phi N ^ K) ^ 3 * (phi N ^ a) ^ 3 ≤ N * kappa E * Real.sqrt (kappa E) ∧
      outEta N K a E = phi N ^ K * phi N ^ a / (N * Real.sqrt (kappa E)) ∧
      0 < outEta N K a E ∧ outEta N K a E ≤ kappa E ∧ (N : ℝ)⁻¹ ≤ outEta N K a E ∧
      phi N ^ K * phi N ^ a ≤ N * Real.sqrt (kappa E) ^ 2 * Real.sqrt (kappa E) ∧
      ∀ K', K' ≤ K → phi N ^ K' / N < outEta N K a E ∧
        (⟨E, outEta N K a E⟩ : ℂ) ∈ specDomain N K' := by
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP0 : 0 < phi N := by linarith
  have hP1 : 1 ≤ phi N := by linarith
  obtain ⟨hρ0, hρR, hρN⟩ := oos_rho hN0r
  have hA1 : 1 ≤ phi N ^ K := Real.one_le_rpow hP1 (by linarith)
  have hV1 : 1 < phi N ^ a := Real.one_lt_rpow (by linarith) ha
  have hAV2 : (phi N ^ K * (phi N ^ a) ^ 2) ^ 2 ≤ phi N ^ C := by
    have hpow : ∀ (x : ℝ) (k : ℕ), phi N ^ ((k : ℝ) * x) = (phi N ^ x) ^ k := by
      intro x k; rw [mul_comm, Real.rpow_mul hP0.le, Real.rpow_natCast]
    have e : (phi N ^ K * (phi N ^ a) ^ 2) ^ 2 = phi N ^ (2 * K + 4 * a) := by
      rw [Real.rpow_add hP0, show (2 : ℝ) * K = ((2 : ℕ) : ℝ) * K by norm_num, hpow,
        show (4 : ℝ) * a = ((4 : ℕ) : ℝ) * a by norm_num, hpow]
      ring
    rw [e]; exact Real.rpow_le_rpow_of_exponent_le hP1 hC
  obtain ⟨hκ, hX0, hX1, hρX, hNk⟩ := oos_window hN0r hA1 hV1.le hρ0 hρR hρN hAV2 h1 h2
  have heta : outEta N K a E = phi N ^ K * phi N ^ a / (N * Real.sqrt (kappa E)) := by
    unfold outEta; rw [Real.rpow_add hP0]
  have hηf : ∀ K', K' ≤ K → _ := fun K' hK' =>
    outside_eta_facts hN0r hA1 hV1 hX0 hX1 (Real.sq_sqrt (abs_nonneg _)).symm hNk
      (Y := phi N ^ K') (Real.rpow_le_rpow_of_exponent_le hP1 hK')
  obtain ⟨hη0, hηκ, hηN, -, hAV⟩ := hηf K le_rfl
  have hη0' : 0 < outEta N K a E := by rw [heta]; exact hη0
  have hηκ' : outEta N K a E ≤ kappa E := by rw [heta]; exact hηκ
  have hηN' : (N : ℝ)⁻¹ ≤ outEta N K a E := by rw [heta]; exact hηN
  refine ⟨hκ, hX0, hX1, hρX, hNk, heta, hη0', hηκ', hηN', hAV, fun K' hK' => ?_⟩
  obtain ⟨-, -, -, hlt, -⟩ := hηf K' hK'
  have hlt' : phi N ^ K' / N < outEta N K a E := by rw [heta]; exact hlt
  refine ⟨hlt', ?_, hlt', ?_⟩
  · change |E| ≤ 5; linarith
  · change outEta N K a E ≤ 10
    linarith

/-- `φ^a = U⁶` and `φ^{a/3} = U²` for `U = φ^{a/6}`. -/
private lemma oos_pow_rel {N : ℕ} (hP0 : 0 < phi N) (a : ℝ) :
    phi N ^ a = (phi N ^ (a / 6)) ^ 6 ∧ phi N ^ (a / 3) = (phi N ^ (a / 6)) ^ 2 := by
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; congr 1; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; congr 1; push_cast; ring

/-- The right sides of (3.8) at `E`: `(φ^a N η)⁻¹ = X / (A V²)` and
`(φ^{a/3} N η)⁻¹ = X / (A U⁸)` with `U = φ^{a/6}`. -/
private lemma oos_targets {N : ℕ} {K a E : ℝ} (hN0r : (0 : ℝ) < N) (hP0 : 0 < phi N)
    (hX0 : 0 < Real.sqrt (kappa E))
    (heta : outEta N K a E = phi N ^ K * phi N ^ a / (N * Real.sqrt (kappa E))) :
    (phi N ^ a * N * outEta N K a E)⁻¹ =
        Real.sqrt (kappa E) / (phi N ^ K * (phi N ^ a) ^ 2) ∧
      (phi N ^ (a / 3) * N * outEta N K a E)⁻¹ =
        Real.sqrt (kappa E) / (phi N ^ K * (phi N ^ (a / 6)) ^ 8) := by
  obtain ⟨hV, hW⟩ := oos_pow_rel hP0 a
  have hA0 : 0 < phi N ^ K := Real.rpow_pos_of_pos hP0 _
  have hU0 : 0 < phi N ^ (a / 6) := Real.rpow_pos_of_pos hP0 _
  have hV0 : 0 < phi N ^ a := Real.rpow_pos_of_pos hP0 _
  constructor
  · rw [heta]
    field_simp
  · rw [heta, hW]
    rw [hV]
    field_simp

/-- Parts 1 and 2 of (3.8) for `Ĥ`, at one eighth of the target, from the outside estimate
at the exponents `(Ks, aS)` with `Ks + aS = K + a` and `aS ≥ a + 1`. -/
private lemma oos_part12 {N : ℕ} {Ks K a aS C Cs q E : ℝ} {ω' : Entries N} (hN : 256 ≤ N)
    (hP : 8 ≤ phi N) (hK : 1 ≤ K) (ha : 0 < a) (hC : 2 * K + 4 * a ≤ C)
    (haS : Ks + aS = K + a) (haS' : a + 1 ≤ aS) (hCs : Cs + 1 ≤ C) (hq0 : 0 < q)
    (hq : 1 / q ≤ (N : ℝ) ^ (-(1 : ℝ) / 3)) (hout : ω' ∈ outsideEvent N Ks aS Cs (q / 2))
    (h1 : oosWin N C ≤ |E|) (h2 : |E| ≤ 3) :
    ‖stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ ≤
        (phi N ^ a * N * outEta N K a E)⁻¹ / 8 ∧
      (stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩).im ≤
        (phi N ^ a * N * outEta N K a E)⁻¹ / 8 := by
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP0 : 0 < phi N := by linarith
  have hP1 : 1 ≤ phi N := by linarith
  obtain ⟨hρ0, hρR, hρN⟩ := oos_rho hN0r
  obtain ⟨-, -, -, -, -, heta, hη0, -⟩ := oos_pt hN hP hK ha hC h1 h2
  have hηS : outEta N Ks aS E = outEta N K a E := by
    unfold outEta; rw [haS]
  -- the window of the outside estimate lies inside the window of (3.7)
  have hwinS : 2 + phi N ^ Cs * (1 / (q / 2) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) ≤ |E| := by
    have e1 : 1 / (q / 2) ^ 2 = 4 * (1 / q) ^ 2 := by rw [div_pow]; field_simp; norm_num
    have e2 : (1 / q) ^ 2 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      rw [← hρR]; exact pow_le_pow_left₀ (by positivity) hq 2
    have hPC5 : 5 * phi N ^ Cs ≤ phi N ^ C := by
      have h1 : phi N ^ (Cs + 1) ≤ phi N ^ C := Real.rpow_le_rpow_of_exponent_le hP1 hCs
      have h2 : phi N ^ (Cs + 1) = phi N ^ Cs * phi N := by
        rw [Real.rpow_add hP0, Real.rpow_one]
      have h3 : 0 < phi N ^ Cs := Real.rpow_pos_of_pos hP0 _
      have h4 := mul_le_mul_of_nonneg_left hP h3.le
      linarith
    have hR0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hN0r.le _
    have h5 : phi N ^ Cs * (1 / (q / 2) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) ≤
        phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      calc phi N ^ Cs * (1 / (q / 2) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3))
          ≤ phi N ^ Cs * (5 * (N : ℝ) ^ (-(2 : ℝ) / 3)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hP0.le _)
            rw [e1]; linarith
        _ = (5 * phi N ^ Cs) * (N : ℝ) ^ (-(2 : ℝ) / 3) := by ring
        _ ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := mul_le_mul_of_nonneg_right hPC5 hR0
    have : oosWin N C = 2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := rfl
    linarith
  obtain ⟨h1', h2', -⟩ := hout E hwinS h2
  rw [hηS] at h1' h2'
  have hTT : (phi N ^ aS * N * outEta N K a E)⁻¹ ≤ (phi N ^ a * N * outEta N K a E)⁻¹ / 8 := by
    have hpa : 8 * phi N ^ a ≤ phi N ^ aS := by
      calc 8 * phi N ^ a ≤ phi N * phi N ^ a :=
            mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hP0.le _)
        _ = phi N ^ (a + 1) := by rw [Real.rpow_add hP0, Real.rpow_one, mul_comm]
        _ ≤ phi N ^ aS := Real.rpow_le_rpow_of_exponent_le hP1 haS'
    have hpos : 0 < 8 * phi N ^ a * N * outEta N K a E := by
      have := Real.rpow_pos_of_pos hP0 a
      positivity
    calc (phi N ^ aS * N * outEta N K a E)⁻¹ ≤ (8 * phi N ^ a * N * outEta N K a E)⁻¹ :=
          inv_anti₀ hpos (by gcongr)
      _ = (phi N ^ a * N * outEta N K a E)⁻¹ / 8 := by field_simp
  exact ⟨h1'.trans hTT, h2'.trans hTT⟩

/-- The off-diagonal bound of (3.8) for `Ĥ` at a quarter of the target, at one point of the window:
(3.32) of [15] gives `Λ_o ≤ C_o (q'⁻¹ + φ^{2ζ} Ψ)` with `Ψ² = (Λ + Im m_sc) / (N η)`; the first
part of (3.8) for `Ĥ` and the bound of `Im m_sc` on the window then bound `Ψ`. -/
private lemma oos_grid_point {N : ℕ} {ζ Ks K a aS C Cs Cm Co q E : ℝ} {ω' : Entries N}
    (hN : 256 ≤ N) (hP : 8 ≤ phi N) (hCm : 1 ≤ Cm) (hCmP : Cm ≤ phi N) (hCo : 0 ≤ Co)
    (hK : 1 ≤ K) (ha : 0 < a) (hC : 2 * K + 4 * a ≤ C) (haS : Ks + aS = K + a)
    (haS' : a + 1 ≤ aS) (hCs : Cs + 1 ≤ C) (hq0 : 0 < q)
    (hq : 1 / q ≤ (N : ℝ) ^ (-(1 : ℝ) / 3))
    (hCoq : Co * (1 / (q / 2)) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) / 8)
    (hUZ : 16 * Co * (phi N ^ ζ) ^ 2 ≤ phi N ^ (a / 6))
    (hI3 : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → z.im ≤ kappa z.re → 2 ≤ |z.re| →
      (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im)))
    (hout : ω' ∈ outsideEvent N Ks aS Cs (q / 2)) (h1 : oosWin N C ≤ |E|) (h2 : |E| ≤ 3)
    (hBo : ¬ (Co * (1 / (q / 2) + phi N ^ (2 * ζ) * psiCtrl (symOfEntries ω') ⟨E, outEta N K a E⟩) <
      lamO (symOfEntries ω') ⟨E, outEta N K a E⟩)) :
    ∀ i j, i ≠ j → ‖resolventC (symOfEntries ω') ⟨E, outEta N K a E⟩ i j‖ ≤
      (phi N ^ (a / 3) * N * outEta N K a E)⁻¹ / 4 := by
  intro i j hij
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP0 : 0 < phi N := by linarith
  have hP1 : 1 ≤ phi N := by linarith
  obtain ⟨hρ0, hρR, hρN⟩ := oos_rho hN0r
  obtain ⟨hκ, hX0, hX1, hρX, hNk, heta, hη0, hηκ, hηN, hAV, -⟩ := oos_pt hN hP hK ha hC h1 h2
  obtain ⟨hp1, -⟩ := oos_part12 hN hP hK ha hC haS haS' hCs hq0 hq hout h1 h2
  obtain ⟨hT1, hT3⟩ := oos_targets hN0r hP0 hX0 heta
  obtain ⟨hV, hW⟩ := oos_pow_rel hP0 a
  have hGij := norm_resolventC_off_le_lamO (H := symOfEntries ω') (z := ⟨E, outEta N K a E⟩) hij
  have hA1 : 1 ≤ phi N ^ K := Real.one_le_rpow hP1 (by linarith)
  have hAP : phi N ≤ phi N ^ K := by
    conv_lhs => rw [← Real.rpow_one (phi N)]
    exact Real.rpow_le_rpow_of_exponent_le hP1 hK
  have hU1 : 1 ≤ phi N ^ (a / 6) := Real.one_le_rpow hP1 (by linarith)
  have hZ2 : phi N ^ (2 * ζ) = (phi N ^ ζ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; congr 1; push_cast; ring
  set X := Real.sqrt (kappa E) with hX
  set A := phi N ^ K with hA
  set U := phi N ^ (a / 6) with hU
  set η := outEta N K a E with hη
  -- `η ≤ 1`, `2 ≤ |E|`
  have hη1 : η ≤ 1 := by rw [hη]; linarith
  have hE2 : 2 ≤ |E| := by linarith [abs_nonneg (|E| - 2), show kappa E = |(|E| - 2)| from rfl]
  have hη' : η = A * U ^ 6 / (N * X) := by rw [heta, hV]
  have hΛ : lamAvg (symOfEntries ω') ⟨E, η⟩ ≤ X / (A * U ^ 12) := by
    have e : (phi N ^ a * N * η)⁻¹ = X / (A * U ^ 12) := by
      rw [hT1, hV]; congr 1; ring
    have h0 : 0 ≤ X / (A * U ^ 12) := by positivity
    unfold lamAvg
    have := hp1
    rw [e] at this
    linarith
  have hsqrt : X ≤ Real.sqrt (kappa E + η) := Real.sqrt_le_sqrt (by linarith)
  have hI : (msc ⟨E, η⟩).im ≤ Cm * (η / X) := by
    have h := hI3 ⟨E, η⟩ (by change |E| ≤ 5; linarith) hη0 (by change η ≤ 10; linarith)
      hηκ hE2
    have h3 : η / Real.sqrt (kappa E + η) ≤ η / X :=
      div_le_div_of_nonneg_left hη0.le hX0 hsqrt
    exact h.trans (mul_le_mul_of_nonneg_left h3 (by linarith))
  have hNk' : Cm * A ^ 2 * U ^ 18 ≤ N * X ^ 3 := by
    have e : (N : ℝ) * kappa E * X = N * X ^ 3 := by
      rw [show kappa E = X ^ 2 from (Real.sq_sqrt (abs_nonneg _)).symm]; ring
    have e2 : (phi N ^ a) ^ 3 = U ^ 18 := by rw [hV]; ring
    have h4 : Cm * A ^ 2 * U ^ 18 ≤ A * A ^ 2 * U ^ 18 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCmP.trans hAP) (sq_nonneg A))
        (pow_nonneg (by linarith) 18)
    calc Cm * A ^ 2 * U ^ 18 ≤ A * A ^ 2 * U ^ 18 := h4
      _ = A ^ 3 * (phi N ^ a) ^ 3 := by rw [e2]; ring
      _ ≤ N * kappa E * X := hNk
      _ = N * X ^ 3 := e
  have hρU : (N : ℝ) ^ (-(1 : ℝ) / 3) ≤ X / (A * U ^ 8) := by
    refine hρX.trans ?_
    have e : (phi N ^ a) ^ 2 = U ^ 12 := by rw [hV]; ring
    rw [e]
    refine div_le_div_of_nonneg_left hX0.le (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU1 (by norm_num)) (by linarith)
  have hq' : Co * (1 / (q / 2)) ≤ X / (8 * (A * U ^ 8)) := by
    have e : X / (8 * (A * U ^ 8)) = X / (A * U ^ 8) / 8 := by field_simp
    rw [e]
    linarith
  have hlam : lamO (symOfEntries ω') ⟨E, η⟩ ≤ Co * (1 / (q / 2) +
      (phi N ^ ζ) ^ 2 * Real.sqrt ((lamAvg (symOfEntries ω') ⟨E, η⟩ + (msc ⟨E, η⟩).im) /
        (N * η))) := by
    have := not_lt.mp hBo
    rw [hZ2] at this
    exact this
  have key := oos_arith3 hN0r hX0 hA1 hU1 hCm hCo hη' hΛ hI hNk' hlam hq' hUZ
  rw [hT3]
  refine hGij.trans (key.trans (le_of_eq ?_))
  field_simp

/-- Both right sides of (3.8) at `E` are at least `N^{-1/3}`. -/
private lemma oos_rho_le {N : ℕ} {K a C E : ℝ} (hN : 256 ≤ N) (hP : 8 ≤ phi N) (hK : 1 ≤ K)
    (ha : 0 < a) (hC : 2 * K + 4 * a ≤ C) (h1 : oosWin N C ≤ |E|) (h2 : |E| ≤ 3) :
    (N : ℝ) ^ (-(1 : ℝ) / 3) ≤ (phi N ^ a * N * outEta N K a E)⁻¹ ∧
      (N : ℝ) ^ (-(1 : ℝ) / 3) ≤ (phi N ^ (a / 3) * N * outEta N K a E)⁻¹ := by
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP0 : 0 < phi N := by linarith
  have hP1 : 1 ≤ phi N := by linarith
  obtain ⟨-, hX0, -, hρX, -, heta, -⟩ := oos_pt hN hP hK ha hC h1 h2
  obtain ⟨hT1, hT3⟩ := oos_targets hN0r hP0 hX0 heta
  obtain ⟨hV, -⟩ := oos_pow_rel hP0 a
  have hA1 : 1 ≤ phi N ^ K := Real.one_le_rpow hP1 (by linarith)
  have hU1 : 1 ≤ phi N ^ (a / 6) := Real.one_le_rpow hP1 (by linarith)
  refine ⟨by rw [hT1]; exact hρX, ?_⟩
  rw [hT3]
  refine hρX.trans ?_
  have e : (phi N ^ a) ^ 2 = (phi N ^ (a / 6)) ^ 12 := by rw [hV]; ring
  rw [e]
  refine div_le_div_of_nonneg_left hX0.le (by positivity) ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU1 (by norm_num)) (by linarith)

/-- The effect of changing the entries by at most `κt` on `m` and on the entries of `G`, at a
point with `Im z ≥ N⁻¹`. -/
private lemma oos_pert {N : ℕ} {H H' : Matrix (Fin N) (Fin N) ℝ} (hN : 0 < N)
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {κt : ℝ} (hκt : 0 ≤ κt)
    (hd : ∀ i j, |H i j - H' i j| ≤ κt) {z : ℂ} (hz : (N : ℝ)⁻¹ ≤ z.im) :
    ‖stieltjesM H z - stieltjesM H' z‖ ≤ (N : ℝ) ^ 4 * κt ∧
      ∀ i j, ‖resolventC H z i j - resolventC H' z i j‖ ≤ (N : ℝ) ^ 4 * κt := by
  have hN0r : (0 : ℝ) < N := by exact_mod_cast hN
  have hz0 : 0 < z.im := lt_of_lt_of_le (inv_pos.mpr hN0r) hz
  have hNη1 : 1 ≤ (N : ℝ) * z.im := by
    calc (1 : ℝ) = N * (N : ℝ)⁻¹ := (mul_inv_cancel₀ hN0r.ne').symm
      _ ≤ N * z.im := mul_le_mul_of_nonneg_left hz hN0r.le
  have hbound : (N : ℝ) ^ 2 * κt / z.im ^ 2 ≤ (N : ℝ) ^ 4 * κt := by
    rw [div_le_iff₀ (by positivity)]
    have h : 1 ≤ ((N : ℝ) * z.im) ^ 2 := one_le_pow₀ hNη1
    have h0 : 0 ≤ (N : ℝ) ^ 2 * κt := mul_nonneg (sq_nonneg _) hκt
    calc (N : ℝ) ^ 2 * κt = (N : ℝ) ^ 2 * κt * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) ^ 2 * κt * (((N : ℝ) * z.im) ^ 2) := mul_le_mul_of_nonneg_left h h0
      _ = (N : ℝ) ^ 4 * κt * z.im ^ 2 := by ring
  exact ⟨(oos_norm_stieltjes_sub_le hN hH hH' hd hz0).trans hbound,
    fun i j => (oos_norm_resolvent_sub_le hH hH' hd hz0 i j).trans hbound⟩

/-- `2 N⁻¹ ≤ N^{-1/3} / 4` for `N ≥ 256`, with `N⁻¹ = (N^{-1/3})³`. -/
private lemma oos_small {N : ℕ} (hN : 256 ≤ N) :
    2 * ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) / 4 := by
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN256 : (256 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hρ0, -, hρN⟩ := oos_rho hN0r
  have hρ5 : (N : ℝ) ^ (-(1 : ℝ) / 3) ≤ 1 / 5 := by
    by_contra h
    push Not at h
    have h1 : (1 / 5 : ℝ) ^ 3 < ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 :=
      pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    have h2 : ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 * 256 ≤ 1 :=
      calc ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 * 256 ≤ ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 * N :=
            mul_le_mul_of_nonneg_left hN256 (by positivity)
        _ = 1 := hρN
    norm_num at h1
    linarith
  have h2 : ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 ≤ (1 / 5) ^ 2 := pow_le_pow_left₀ hρ0.le hρ5 2
  calc 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3
      = (N : ℝ) ^ (-(1 : ℝ) / 3) * (2 * ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2) := by ring
    _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) * (1 / 4) :=
        mul_le_mul_of_nonneg_left (by norm_num at h2 ⊢; linarith) hρ0.le
    _ = (N : ℝ) ^ (-(1 : ℝ) / 3) / 4 := by ring

/-- Transfer of the first two bounds of (3.8) from `Ĥ` at one eighth to `H`. -/
private lemma oos_transfer12 {N : ℕ} {K a C κt E : ℝ} {ω ω' : Entries N} (hN : 256 ≤ N)
    (hP : 8 ≤ phi N) (hK : 1 ≤ K) (ha : 0 < a) (hC : 2 * K + 4 * a ≤ C) (hκt : 0 ≤ κt)
    (hd : ∀ i j, |symOfEntries ω i j - symOfEntries ω' i j| ≤ κt)
    (hκ : 4 * ((N : ℝ) ^ 4 * κt) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3))
    (hbE : oosWin N C ≤ |E|) (hE3 : |E| ≤ 3)
    (h1' : ‖stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ ≤
      (phi N ^ a * N * outEta N K a E)⁻¹ / 8)
    (h2' : (stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩).im ≤
      (phi N ^ a * N * outEta N K a E)⁻¹ / 8) :
    ‖stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ ≤
        (phi N ^ a * N * outEta N K a E)⁻¹ ∧
      (stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩).im ≤
        (phi N ^ a * N * outEta N K a E)⁻¹ := by
  have hH := symOfEntries_isHermitian ω
  have hH' := symOfEntries_isHermitian ω'
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hρ0, -, -⟩ := oos_rho hN0r
  obtain ⟨-, -, -, -, -, -, -, -, hηNE, -⟩ := oos_pt hN hP hK ha hC hbE hE3
  obtain ⟨hρT1, -⟩ := oos_rho_le hN hP hK ha hC hbE hE3
  obtain ⟨hmE, -⟩ := oos_pert (by omega : 0 < N) hH hH' hκt hd (z := ⟨E, outEta N K a E⟩) hηNE
  have hε : (N : ℝ) ^ 4 * κt ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) / 4 := by linarith
  refine ⟨?_, ?_⟩
  · calc ‖stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖
        ≤ ‖stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩ -
            stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩‖ +
          ‖stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (phi N ^ a * N * outEta N K a E)⁻¹ := by linarith
  · have h := Complex.im_le_norm (stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩ -
      stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩)
    rw [Complex.sub_im] at h
    linarith

/-- Transfer of the third bound of (3.8) from the points of the grid, where `Ĥ` has it at one
quarter of the target, to every point of the window. -/
private lemma oos_transfer3 {N : ℕ} {K a C κt E : ℝ} {ω ω' : Entries N} (hN : 256 ≤ N)
    (hP : 8 ≤ phi N) (hK : 1 ≤ K) (ha : 0 < a) (hC : 2 * K + 4 * a ≤ C) (hκt : 0 ≤ κt)
    (hd : ∀ i j, |symOfEntries ω i j - symOfEntries ω' i j| ≤ κt)
    (hκ : 4 * ((N : ℝ) ^ 4 * κt) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3))
    (hbE : oosWin N C ≤ |E|) (hE3 : |E| ≤ 3)
    (h3 : ∀ p ∈ outsideGrid N (oosWin N C), oosWin N C ≤ |outsideGridE N (oosWin N C) p| →
      |outsideGridE N (oosWin N C) p| ≤ 3 → ∀ i j, i ≠ j →
        ‖resolventC (symOfEntries ω') ⟨outsideGridE N (oosWin N C) p,
            outEta N K a (outsideGridE N (oosWin N C) p)⟩ i j‖ ≤
          (phi N ^ (a / 3) * N * outEta N K a (outsideGridE N (oosWin N C) p))⁻¹ / 4) :
    ∀ i j, i ≠ j → ‖resolventC (symOfEntries ω) ⟨E, outEta N K a E⟩ i j‖ ≤
      (phi N ^ (a / 3) * N * outEta N K a E)⁻¹ := by
  intro i j hij
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP0 : 0 < phi N := by linarith
  have hH := symOfEntries_isHermitian ω
  have hH' := symOfEntries_isHermitian ω'
  have hR0 : 0 ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
    mul_nonneg (Real.rpow_nonneg hP0.le _) (Real.rpow_nonneg hN0r.le _)
  have hb2 : 2 ≤ oosWin N C := by unfold oosWin; linarith
  obtain ⟨hρ0, -, hρN⟩ := oos_rho hN0r
  have hsmall := oos_small hN
  obtain ⟨hκE, hX0E, hX1E, hρXE, hNkE, hηE, hη0E, hηκE, hηNE, hAVE, -⟩ :=
    oos_pt hN hP hK ha hC hbE hE3
  obtain ⟨-, hρT3⟩ := oos_rho_le hN hP hK ha hC hbE hE3
  obtain ⟨p, hp, hpb, hp3, hpE, hpE', hdE⟩ := outside_grid (by omega : 1 ≤ N) hb2 hbE hE3
  have hg := h3 p hp hpb hp3 i j hij
  generalize outsideGridE N (oosWin N C) p = Ep at hpb hp3 hpE hpE' hdE hg
  obtain ⟨hκp, hX0p, hX1p, hρXp, hNkp, hηp, hη0p, hηκp, hηNp, hAVp, -⟩ :=
    oos_pt hN hP hK ha hC hpb hp3
  obtain ⟨-, hT3p⟩ := oos_targets hN0r hP0 hX0p hηp
  obtain ⟨-, hT3E⟩ := oos_targets hN0r hP0 hX0E hηE
  obtain ⟨-, hGp⟩ := oos_pert (by omega : 0 < N) hH hH' hκt hd
    (z := ⟨Ep, outEta N K a Ep⟩) hηNp
  have hXle : Real.sqrt (kappa Ep) ≤ Real.sqrt (kappa E) :=
    Real.sqrt_le_sqrt (by rw [hκp, hκE]; linarith)
  have hT3le : (phi N ^ (a / 3) * N * outEta N K a Ep)⁻¹ ≤
      (phi N ^ (a / 3) * N * outEta N K a E)⁻¹ := by
    rw [hT3p, hT3E]
    refine div_le_div_of_nonneg_right hXle ?_
    have hP1 : 1 ≤ phi N := by linarith
    have hA1 : 1 ≤ phi N ^ K := Real.one_le_rpow hP1 (by linarith)
    have hU1 : 1 ≤ phi N ^ (a / 6) := Real.one_le_rpow hP1 (by linarith)
    positivity
  -- the distance between the two points
  have hAVpos : 0 < phi N ^ K * phi N ^ a :=
    mul_pos (Real.rpow_pos_of_pos hP0 K) (Real.rpow_pos_of_pos hP0 a)
  have hdiff := outside_eta_diff hN0r (a := phi N ^ K * phi N ^ a)
    (x := Real.sqrt (kappa Ep)) (y := Real.sqrt (kappa E)) (δ := ((N : ℝ) ^ 3)⁻¹) hAVpos hX0p
    hXle (by
      rw [Real.sq_sqrt (show 0 ≤ kappa E from abs_nonneg _),
        Real.sq_sqrt (show 0 ≤ kappa Ep from abs_nonneg _), hκE, hκp]
      linarith) hAVp
  have hdη : |outEta N K a E - outEta N K a Ep| ≤ ((N : ℝ) ^ 3)⁻¹ := by
    rw [hηE, hηp, abs_sub_comm, abs_of_nonneg hdiff.1]
    exact hdiff.2
  have hzw : ‖(⟨E, outEta N K a E⟩ : ℂ) - ⟨Ep, outEta N K a Ep⟩‖ ≤ 2 * ((N : ℝ) ^ 3)⁻¹ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    linarith
  have hlip := norm_resolventC_apply_sub_le hH (z := ⟨E, outEta N K a E⟩)
    (w := ⟨Ep, outEta N K a Ep⟩) hη0E hη0p i j
  have hL : ‖(⟨E, outEta N K a E⟩ : ℂ) - ⟨Ep, outEta N K a Ep⟩‖ /
      ((⟨E, outEta N K a E⟩ : ℂ).im * (⟨Ep, outEta N K a Ep⟩ : ℂ).im) ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3) / 4 := by
    have hden : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤
        (⟨E, outEta N K a E⟩ : ℂ).im * (⟨Ep, outEta N K a Ep⟩ : ℂ).im :=
      mul_le_mul hηNE hηNp (by positivity) hη0E.le
    calc _ ≤ 2 * ((N : ℝ) ^ 3)⁻¹ / ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) :=
          div_le_div₀ (by positivity) hzw (by positivity) hden
      _ = 2 * ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 := by
          have : ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 = (N : ℝ)⁻¹ := eq_inv_of_mul_eq_one_left hρN
          rw [this]; field_simp
      _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) / 4 := hsmall
  have hε : (N : ℝ) ^ 4 * κt ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) / 4 := by linarith
  have h1 := norm_le_norm_add_norm_sub'
    (resolventC (symOfEntries ω) ⟨E, outEta N K a E⟩ i j)
    (resolventC (symOfEntries ω) ⟨Ep, outEta N K a Ep⟩ i j)
  have h2 := norm_le_norm_add_norm_sub'
    (resolventC (symOfEntries ω) ⟨Ep, outEta N K a Ep⟩ i j)
    (resolventC (symOfEntries ω') ⟨Ep, outEta N K a Ep⟩ i j)
  have h6 := hGp i j
  linarith

/-- Transfer of (3.8) from `Ĥ` to `H` on the window of (3.7): the first two bounds of (3.8)
for `Ĥ` at one eighth, and the third at one quarter of the target at the points of the grid,
give all three bounds for `H` when the entries differ by at most `κt` with `4 N⁴ κt ≤ N^{-1/3}`. -/
private lemma oos_transfer {N : ℕ} {K a C κt : ℝ} {ω ω' : Entries N} (hN : 256 ≤ N)
    (hP : 8 ≤ phi N) (hK : 1 ≤ K) (ha : 0 < a) (hC : 2 * K + 4 * a ≤ C) (hκt : 0 ≤ κt)
    (hd : ∀ i j, |symOfEntries ω i j - symOfEntries ω' i j| ≤ κt)
    (hκ : 4 * ((N : ℝ) ^ 4 * κt) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3))
    (h12 : ∀ E : ℝ, oosWin N C ≤ |E| → |E| ≤ 3 →
      ‖stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ ≤
          (phi N ^ a * N * outEta N K a E)⁻¹ / 8 ∧
        (stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩).im ≤
          (phi N ^ a * N * outEta N K a E)⁻¹ / 8)
    (h3 : ∀ p ∈ outsideGrid N (oosWin N C), oosWin N C ≤ |outsideGridE N (oosWin N C) p| →
      |outsideGridE N (oosWin N C) p| ≤ 3 → ∀ i j, i ≠ j →
        ‖resolventC (symOfEntries ω') ⟨outsideGridE N (oosWin N C) p,
            outEta N K a (outsideGridE N (oosWin N C) p)⟩ i j‖ ≤
          (phi N ^ (a / 3) * N * outEta N K a (outsideGridE N (oosWin N C) p))⁻¹ / 4) :
    ∀ E : ℝ, oosWin N C ≤ E → E ≤ 3 →
      ‖stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ ≤
          (phi N ^ a * N * outEta N K a E)⁻¹ ∧
        (stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩).im ≤
          (phi N ^ a * N * outEta N K a E)⁻¹ ∧
        ∀ i j, i ≠ j → ‖resolventC (symOfEntries ω) ⟨E, outEta N K a E⟩ i j‖ ≤
          (phi N ^ (a / 3) * N * outEta N K a E)⁻¹ := by
  intro E hE1 hE3
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP0 : 0 < phi N := by linarith
  have hR0 : 0 ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
    mul_nonneg (Real.rpow_nonneg hP0.le _) (Real.rpow_nonneg hN0r.le _)
  have hE0 : 0 ≤ E := by
    have : oosWin N C = 2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := rfl
    linarith
  have hEa : |E| = E := abs_of_nonneg hE0
  have hbE : oosWin N C ≤ |E| := by rw [hEa]; exact hE1
  have hE3' : |E| ≤ 3 := by rw [hEa]; exact hE3
  obtain ⟨h1', h2'⟩ := h12 E hbE hE3'
  obtain ⟨hA, hB⟩ := oos_transfer12 hN hP hK ha hC hκt hd hκ hbE hE3' h1' h2'
  exact ⟨hA, hB, oos_transfer3 hN hP hK ha hC hκt hd hκ hbE hE3' h3⟩

/-! ### The exceptional events and their probabilities -/

/-- The points `±(b + k N⁻³)` of the grid lie in the window `b ≤ |E| ≤ 3`. -/
private lemma oos_grid_win {N : ℕ} {b : ℝ} (hb0 : 0 ≤ b) {p : ℕ × Bool}
    (hp : p ∈ outsideGrid N b) : b ≤ |outsideGridE N b p| ∧ |outsideGridE N b p| ≤ 3 := by
  have habs : |outsideGridE N b p| = b + p.1 * ((N : ℝ) ^ 3)⁻¹ := outsideGridE_abs hb0 p
  rw [outsideGrid, Finset.mem_filter] at hp
  rw [habs]
  refine ⟨?_, hp.2⟩
  have : 0 ≤ (p.1 : ℝ) * ((N : ℝ) ^ 3)⁻¹ := by positivity
  linarith

/-- The event that (3.32) of [15] fails at `z = E + iη_E` on `Ω(z)`. -/
private def oosBo (N : ℕ) (ζ K a Co q E : ℝ) : Set (Entries N) :=
  {ω | lamD (symOfEntries ω) ⟨E, outEta N K a E⟩ + lamO (symOfEntries ω) ⟨E, outEta N K a E⟩ ≤
      (phi N ^ ζ)⁻¹ ∧
    Co * (1 / (q / 2) + phi N ^ (2 * ζ) * psiCtrl (symOfEntries ω) ⟨E, outEta N K a E⟩) <
      lamO (symOfEntries ω) ⟨E, outEta N K a E⟩}

/-- The bounds on `q` used for the third part of (3.8): `q ≥ N^{φs}` with `φs > 1/3` and
`16 C_o ≤ N^{φs - 1/3}` give `q⁻¹ ≤ N^{-1/3}` and `C_o (q/2)⁻¹ ≤ N^{-1/3} / 8`. -/
private lemma oos_q_facts {N : ℕ} {φs Co q : ℝ} (hN : 1 ≤ N) (hqN : (N : ℝ) ^ φs ≤ q)
    (hφs : 1 / 3 ≤ φs) (hCoq : 16 * Co ≤ (N : ℝ) ^ (φs - 1 / 3)) :
    0 < q ∧ 1 / q ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) ∧
      Co * (1 / (q / 2)) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) / 8 := by
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq0 : 0 < q := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0r _) hqN
  refine ⟨hq0, ?_, ?_⟩
  · have h1 : (N : ℝ) ^ (1 / 3 : ℝ) ≤ q :=
      (Real.rpow_le_rpow_of_exponent_le hN1r hφs).trans hqN
    have e : (N : ℝ) ^ (-(1 : ℝ) / 3) = ((N : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hN0r.le]; congr 1; ring
    rw [e, one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0r _) h1
  · obtain ⟨hρ0, -, -⟩ := oos_rho hN0r
    have h1 : 16 * Co ≤ q * (N : ℝ) ^ (-(1 : ℝ) / 3) := by
      have e : (N : ℝ) ^ (φs - 1 / 3) = (N : ℝ) ^ φs * (N : ℝ) ^ (-(1 : ℝ) / 3) := by
        rw [← Real.rpow_add hN0r]; congr 1; ring
      calc 16 * Co ≤ (N : ℝ) ^ (φs - 1 / 3) := hCoq
        _ = (N : ℝ) ^ φs * (N : ℝ) ^ (-(1 : ℝ) / 3) := e
        _ ≤ q * (N : ℝ) ^ (-(1 : ℝ) / 3) := mul_le_mul_of_nonneg_right hqN hρ0.le
    have e2 : Co * (1 / (q / 2)) = 2 * Co / q := by field_simp
    rw [e2, div_le_iff₀ hq0]
    calc 2 * Co = (16 * Co) / 8 := by ring
      _ ≤ (q * (N : ℝ) ^ (-(1 : ℝ) / 3)) / 8 := by linarith
      _ = (N : ℝ) ^ (-(1 : ℝ) / 3) / 8 * q := by ring

/-- `16 C_o ≤ φ^{a/6 - 2ζ}` gives `16 C_o (φ^ζ)² ≤ φ^{a/6}`. -/
private lemma oos_UZ {N : ℕ} {ζ a Co : ℝ} (hP0 : 0 < phi N)
    (h : 16 * Co ≤ phi N ^ (a / 6 - 2 * ζ)) : 16 * Co * (phi N ^ ζ) ^ 2 ≤ phi N ^ (a / 6) := by
  have hZ2 : phi N ^ (2 * ζ) = (phi N ^ ζ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; congr 1; push_cast; ring
  have e : phi N ^ (a / 6) = phi N ^ (a / 6 - 2 * ζ) * (phi N ^ ζ) ^ 2 := by
    rw [← hZ2, ← Real.rpow_add hP0]; congr 1; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- If `Ĥ` avoids the exceptional events then the hypotheses of the transfer hold. -/
private lemma oos_good {N : ℕ} {ζ Ks Kw K a aS C Cs Cm Co q : ℝ} {ω' : Entries N}
    (hN : 256 ≤ N) (hP : 8 ≤ phi N) (hCm : 1 ≤ Cm) (hCmP : Cm ≤ phi N) (hCo : 0 ≤ Co)
    (hK : 1 ≤ K) (hKw : Kw ≤ K) (ha : 0 < a) (hC : 2 * K + 4 * a ≤ C) (haS : Ks + aS = K + a)
    (haS' : a + 1 ≤ aS) (hCs : Cs + 1 ≤ C) (hq0 : 0 < q)
    (hq : 1 / q ≤ (N : ℝ) ^ (-(1 : ℝ) / 3))
    (hCoq : Co * (1 / (q / 2)) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) / 8)
    (hUZ : 16 * Co * (phi N ^ ζ) ^ 2 ≤ phi N ^ (a / 6))
    (hI3 : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → z.im ≤ kappa z.re → 2 ≤ |z.re| →
      (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im)))
    (hout : ω' ∈ outsideEvent N Ks aS Cs (q / 2))
    (hΩ : ω' ∉ {ω | ∃ z ∈ specDomain N Kw,
      (phi N ^ ζ)⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z})
    (hBo : ∀ p ∈ outsideGrid N (oosWin N C),
      ω' ∉ oosBo N ζ K a Co q (outsideGridE N (oosWin N C) p)) :
    (∀ E : ℝ, oosWin N C ≤ |E| → |E| ≤ 3 →
      ‖stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ ≤
          (phi N ^ a * N * outEta N K a E)⁻¹ / 8 ∧
        (stieltjesM (symOfEntries ω') ⟨E, outEta N K a E⟩).im ≤
          (phi N ^ a * N * outEta N K a E)⁻¹ / 8) ∧
    (∀ p ∈ outsideGrid N (oosWin N C), oosWin N C ≤ |outsideGridE N (oosWin N C) p| →
      |outsideGridE N (oosWin N C) p| ≤ 3 → ∀ i j, i ≠ j →
        ‖resolventC (symOfEntries ω') ⟨outsideGridE N (oosWin N C) p,
            outEta N K a (outsideGridE N (oosWin N C) p)⟩ i j‖ ≤
          (phi N ^ (a / 3) * N * outEta N K a (outsideGridE N (oosWin N C) p))⁻¹ / 4) := by
  refine ⟨fun E h1 h2 => oos_part12 hN hP hK ha hC haS haS' hCs hq0 hq hout h1 h2,
    fun p hp hpb hp3 => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdom⟩ := oos_pt hN hP hK ha hC hpb hp3
  have hz := (hdom Kw hKw).2
  have hΩz : lamD (symOfEntries ω') ⟨outsideGridE N (oosWin N C) p,
      outEta N K a (outsideGridE N (oosWin N C) p)⟩ + lamO (symOfEntries ω')
      ⟨outsideGridE N (oosWin N C) p, outEta N K a (outsideGridE N (oosWin N C) p)⟩ ≤
      (phi N ^ ζ)⁻¹ := not_lt.mp fun h => hΩ ⟨_, hz, h⟩
  have hbo := fun h => hBo p hp ⟨hΩz, h⟩
  exact oos_grid_point hN hP hCm hCmP hCo hK ha hC haS haS' hCs hq0 hq hCoq hUZ hI3 hout hpb hp3
    hbo

/-- The union bound: `Aᶜ` lies in the bad set of the truncation, or its image under `T` lies in one
of finitely many events for the law of `Ĥ`. -/
private lemma oos_measure_union {α ι : Type*} [MeasurableSpace α] {μ μ' : Measure α} {T : α → α}
    (hT : Measurable T) (hmap : μ.map T = μ') {A Bad B1 Bw : Set α} {Bo : ι → Set α}
    (G : Finset ι) {e0 e1 e2 e3 : ℝ} (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (hsub : Aᶜ ⊆ Bad ∪ T ⁻¹' (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p)) (h0 : μ Bad ≤ ENNReal.ofReal e0)
    (h1 : μ' B1 ≤ ENNReal.ofReal e1) (h2 : μ' Bw ≤ ENNReal.ofReal e2)
    (h3 : ∀ p ∈ G, μ' (Bo p) ≤ ENNReal.ofReal e3) :
    μ Aᶜ ≤ ENNReal.ofReal (e0 + e1 + e2 + G.card * e3) := by
  have hpre : μ (T ⁻¹' (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p)) ≤ μ' (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p) := by
    calc μ (T ⁻¹' (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p)) ≤ (μ.map T) (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p) :=
          Measure.le_map_apply hT.aemeasurable _
      _ = μ' (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p) := by rw [hmap]
  have hsum : ∑ p ∈ G, μ' (Bo p) ≤ ENNReal.ofReal (G.card * e3) := by
    calc ∑ p ∈ G, μ' (Bo p) ≤ ∑ _p ∈ G, ENNReal.ofReal e3 := Finset.sum_le_sum h3
      _ = ENNReal.ofReal (G.card * e3) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  calc μ Aᶜ ≤ μ (Bad ∪ T ⁻¹' (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p)) := measure_mono hsub
    _ ≤ μ Bad + μ (T ⁻¹' (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p)) := measure_union_le _ _
    _ ≤ μ Bad + μ' (B1 ∪ Bw ∪ ⋃ p ∈ G, Bo p) := by gcongr
    _ ≤ μ Bad + (μ' B1 + μ' Bw + ∑ p ∈ G, μ' (Bo p)) :=
        add_le_add le_rfl ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le G _)))
    _ ≤ ENNReal.ofReal e0 + (ENNReal.ofReal e1 + ENNReal.ofReal e2 +
          ENNReal.ofReal (G.card * e3)) :=
        add_le_add h0 (add_le_add (add_le_add h1 h2) hsum)
    _ = ENNReal.ofReal (e0 + e1 + e2 + G.card * e3) := by
        have p3 : 0 ≤ (G.card : ℝ) * e3 := mul_nonneg (Nat.cast_nonneg _) he3
        rw [ENNReal.ofReal_add (add_nonneg (add_nonneg he0 he1) he2) p3,
          ENNReal.ofReal_add (add_nonneg he0 he1) he2, ENNReal.ofReal_add he0 he1]
        ring

/-- The event (3.8) on the window of (3.7). -/
def outEvent (N : ℕ) (K a C : ℝ) : Set (Entries N) :=
  {ω | ∀ E : ℝ, 2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ E → E ≤ 3 →
    ‖stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ ≤
        (phi N ^ a * N * outEta N K a E)⁻¹ ∧
      (stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩).im ≤
        (phi N ^ a * N * outEta N K a E)⁻¹ ∧
      ∀ i j, i ≠ j → ‖resolventC (symOfEntries ω) ⟨E, outEta N K a E⟩ i j‖ ≤
        (phi N ^ (a / 3) * N * outEta N K a E)⁻¹}

/-- Lemma 3.1 (5) with Remark 3.2, with an offset `K` (quantified before `a`) and `a > 12ζ`. -/
theorem outOfSpectrum {ζ C0 c φs : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) (hc : 0 < c)
    (hφs : 1 / 3 < φs) :
    ∃ K > 0, ∀ a > 12 * ζ, ∃ C > 0, HighProbOn ζ (fun _ L => L.IsGenWigner C0)
      (fun N L => {ω | (∃ q, L.SupportParam ((N : ℝ) ^ φs) c q) → ω ∈ outEvent N K a C}) := by
  classical
  have hC0' : 0 ≤ max C0 1 := le_max_of_le_right zero_le_one
  obtain ⟨Ks, hKs, hS⟩ := outside_boundedAS hζ hC0'
  obtain ⟨Kw, hKw, cw, hcw, Nw, hW⟩ := weakLocalLaw_omega hζ hC0'
  obtain ⟨Ko, hKo, Co, hCo, co, hco, No, hO⟩ := lamO_le_on_omega hζ hC0'
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  obtain ⟨Nt, hNt⟩ := exists_truncation hC0 hc
  have hφs0 : 0 < φs := by linarith
  set K : ℝ := Ks + Kw + Ko + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  refine ⟨K, by linarith, fun a ha => ?_⟩
  have ha0 : 0 < a := by linarith
  have ha6 : 0 < a / 6 - 2 * ζ := by linarith
  set aS : ℝ := a + (K - Ks) with haS
  have hKKs : 1 ≤ K - Ks := by rw [hK]; linarith
  obtain ⟨Cs, hCs, cs, hcs, Ns, hSs⟩ := hS aS (by linarith)
  set C : ℝ := max (Cs + 1) (2 * K + 4 * a) + 1 with hC
  have hCs1 : Cs + 1 ≤ C := by rw [hC]; linarith [le_max_left (Cs + 1) (2 * K + 4 * a)]
  have hCK : 2 * K + 4 * a ≤ C := by rw [hC]; linarith [le_max_right (Cs + 1) (2 * K + 4 * a)]
  refine ⟨C, by linarith, ?_⟩
  set M : ℝ := max Cs (max Kw Ko) with hM
  set m : ℝ := min (min cs cw) (min co 1) with hm
  have hm0 : 0 < m := lt_min (lt_min hcs hcw) (lt_min hco one_pos)
  have hev : ∀ᶠ N : ℕ in atTop,
      (256 ≤ N ∧ max Nw (max Ns (max No Nt)) ≤ N) ∧
      max 8 Cm ≤ phi N ∧
      16 * Co ≤ phi N ^ (a / 6 - 2 * ζ) ∧
      16 * Co ≤ (N : ℝ) ^ (φs - 1 / 3) ∧
      (phi N ^ M ≤ (N : ℝ) ^ (φs / 2) ∧ 2 ≤ (N : ℝ) ^ (φs / 2)) ∧
      4 * ((N : ℝ) ^ 4 * Real.exp (-(N : ℝ) ^ c / 4)) ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) ∧
      (phi N ^ ζ ≤ (N : ℝ) ^ (c / 2) ∧ 2 ≤ (N : ℝ) ^ (c / 2) ∧
        2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c / 2) ≤ 1) := by
    have h1 := (eventually_ge_atTop 256).and
      (eventually_ge_atTop (max Nw (max Ns (max No Nt))))
    have h2 := eventually_mul_log_add_one_le_phi_rpow one_pos (max 8 Cm)
    have h3 := eventually_mul_log_add_one_le_phi_rpow ha6 (16 * Co)
    have h4 := ((tendsto_rpow_atTop (by linarith : 0 < φs - 1 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (16 * Co)
    have h5 := (phi_rpow_le_rpow M (c := φs / 2) (by linarith)).and
      (((tendsto_rpow_atTop (by linarith : 0 < φs / 2)).comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop 2)
    have h6 := oos_eventually_trunc hc
    have h7 := (phi_rpow_le_rpow ζ (c := c / 2) (by linarith)).and
      ((((tendsto_rpow_atTop (by linarith : 0 < c / 2)).comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop 2).and
      ((oos_tendsto_rpow_mul_exp (k := 2) hc (b := 1 / 2) (by norm_num)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))))
    filter_upwards [h1, h2, h3, h4, h5, h6, h7] with N h1 h2 h3 h4 h5 h6 h7
    have hl : 1 ≤ Real.log N + 1 := by linarith [Real.log_natCast_nonneg N]
    refine ⟨h1, ?_, ?_, ?_, h5, h6, h7.1, h7.2.1, ?_⟩
    · have := h2.2
      rw [Real.rpow_one] at this
      have h0 : 0 ≤ max 8 Cm := le_trans (by norm_num) (le_max_left 8 Cm)
      exact (le_mul_of_one_le_right h0 hl).trans this
    · have := h3.2
      have h0 : 0 ≤ 16 * Co := by positivity
      exact (le_mul_of_one_le_right h0 hl).trans this
    · exact h4
    · have := h7.2.2
      rw [Real.rpow_two] at this
      have e : Real.exp (-(1 / 2) * (N : ℝ) ^ c) = Real.exp (-(N : ℝ) ^ c / 2) := by
        congr 1; ring
      rw [e] at this
      linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  refine ⟨m, hm0, 4, by norm_num, N0, fun N hN L hL => ?_⟩
  obtain ⟨⟨h256, hNmax⟩, hP8', hUZ, hCoq, ⟨hPM, hN2φ⟩, hεN, hst, hN2c, hexpN⟩ := hN0 N hN
  have hNw : Nw ≤ N := (le_max_left _ _).trans hNmax
  have hNs : Ns ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hNmax
  have hNo : No ≤ N :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hNmax
  have hNt' : Nt ≤ N :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hNmax
  have hN3 : 3 ≤ N := by omega
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  by_cases hq : ∃ q, L.SupportParam ((N : ℝ) ^ φs) c q
  swap
  · have : {ω : Entries N | (∃ q, L.SupportParam ((N : ℝ) ^ φs) c q) →
        ω ∈ outEvent N K a C}ᶜ = ∅ := by
      ext ω; simp [hq]
    rw [this, measure_empty]
    exact zero_le
  obtain ⟨q, hqS⟩ := hq
  suffices hmain : L.law (outEvent N K a C)ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ 4 * Real.exp (-m * phi N ^ ζ)) by
    have hsub : {ω : Entries N | (∃ q, L.SupportParam ((N : ℝ) ^ φs) c q) →
        ω ∈ outEvent N K a C}ᶜ ⊆ (outEvent N K a C)ᶜ := fun ω hω hB => hω fun _ => hB
    refine le_trans (measure_mono hsub) (hmain.trans (le_of_eq ?_))
    norm_num
  have hP0 : 0 < phi N := by
    have := (le_max_left (8 : ℝ) Cm).trans hP8'
    linarith
  have hP1 : 1 ≤ phi N := sc_one_le_phi hN3
  have hP8 : 8 ≤ phi N := (le_max_left _ _).trans hP8'
  have hCmP : Cm ≤ phi N := (le_max_right _ _).trans hP8'
  -- the truncation
  have hq1 : (1 : ℝ) ≤ (N : ℝ) ^ φs := Real.one_le_rpow hN1r hφs0.le
  have hqN : (N : ℝ) ^ φs ≤ q := hqS.1
  have hS1 : L.SupportParam 1 c q := ⟨hq1.trans hqS.1, hqS.2.1, hqS.2.2⟩
  obtain ⟨L', T, hT, hmap, hG', hBS', hbad⟩ := hNt N hNt' L q hL hS1
  have hq2 : phi N ^ M ≤ q / 2 := by
    have h1 : (N : ℝ) ^ (φs / 2) * 2 ≤ (N : ℝ) ^ (φs / 2) * (N : ℝ) ^ (φs / 2) :=
      mul_le_mul_of_nonneg_left hN2φ (Real.rpow_nonneg hN0r.le _)
    have h2 : (N : ℝ) ^ (φs / 2) * (N : ℝ) ^ (φs / 2) = (N : ℝ) ^ φs := by
      rw [← Real.rpow_add hN0r]; congr 1; ring
    linarith
  have hCsM : Cs ≤ M := le_max_left _ _
  have hKwM : Kw ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hKoM : Ko ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hqCs : phi N ^ Cs ≤ q / 2 := (Real.rpow_le_rpow_of_exponent_le hP1 hCsM).trans hq2
  have hqKw : phi N ^ Kw ≤ q / 2 := (Real.rpow_le_rpow_of_exponent_le hP1 hKwM).trans hq2
  have hqKo : phi N ^ Ko ≤ q / 2 := (Real.rpow_le_rpow_of_exponent_le hP1 hKoM).trans hq2
  obtain ⟨hq0, hqρ, hCoρ⟩ := oos_q_facts (by omega) hqN hφs.le hCoq
  have hUZ' := oos_UZ hP0 hUZ
  have hI3 : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → z.im ≤ kappa z.re → 2 ≤ |z.re| →
      (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im)) :=
    fun z h1 h2 h3 h4 h5 => ((hmsc z h1 h2 h3).2.2.1 h4 h5).2
  have hCCs : Cs + 1 ≤ C := hCs1
  have haS1 : Ks + aS = K + a := by rw [haS]; ring
  have haS2 : a + 1 ≤ aS := by rw [haS]; linarith
  have hKw' : Kw ≤ K := by rw [hK]; linarith
  have hKo' : Ko ≤ K := by rw [hK]; linarith
  have hb0 : 0 ≤ oosWin N C := by
    have h1 : 0 ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
      mul_nonneg (Real.rpow_nonneg hP0.le _) (Real.rpow_nonneg hN0r.le _)
    unfold oosWin; linarith
  have hκt0 : 0 ≤ Real.exp (-(N : ℝ) ^ c / 4) := (Real.exp_pos _).le
  -- the exceptional events
  have hsub : (outEvent N K a C)ᶜ ⊆
      {ω | ∃ i j, Real.exp (-(N : ℝ) ^ c / 4) < |symOfEntries ω i j - symOfEntries (T ω) i j|} ∪
        T ⁻¹' ((outsideEvent N Ks aS Cs (q / 2))ᶜ ∪
          {ω | ∃ z ∈ specDomain N Kw,
            (phi N ^ ζ)⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ∪
          ⋃ p ∈ outsideGrid N (oosWin N C),
            oosBo N ζ K a Co q (outsideGridE N (oosWin N C) p)) := by
    intro ω hω
    by_contra hcon
    apply hω
    have hclose : ∀ i j, |symOfEntries ω i j - symOfEntries (T ω) i j| ≤
        Real.exp (-(N : ℝ) ^ c / 4) := by
      intro i j
      by_contra h
      exact hcon (Or.inl ⟨i, j, not_le.mp h⟩)
    have hout : T ω ∈ outsideEvent N Ks aS Cs (q / 2) := by
      by_contra h
      exact hcon (Or.inr (Or.inl (Or.inl h)))
    have hΩ : T ω ∉ {ω | ∃ z ∈ specDomain N Kw,
        (phi N ^ ζ)⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} :=
      fun h => hcon (Or.inr (Or.inl (Or.inr h)))
    have hBo : ∀ p ∈ outsideGrid N (oosWin N C),
        T ω ∉ oosBo N ζ K a Co q (outsideGridE N (oosWin N C) p) :=
      fun p hp h => hcon (Or.inr (Or.inr (Set.mem_biUnion hp h)))
    obtain ⟨h12, h3⟩ := oos_good h256 hP8 hCm hCmP hCo.le hK1 hKw' ha0 hCK haS1 haS2 hCCs hq0 hqρ
      hCoρ hUZ' hI3 hout hΩ hBo
    exact oos_transfer h256 hP8 hK1 ha0 hCK hκt0 hclose hεN h12 h3
  -- the probabilities
  have hPB1 : L'.law (outsideEvent N Ks aS Cs (q / 2))ᶜ ≤
      ENNReal.ofReal (Real.exp (-cs * phi N ^ ζ)) := hSs N hNs L' (q / 2) hG' hBS' hqCs
  have hPBw : L'.law {ω | ∃ z ∈ specDomain N Kw,
      (phi N ^ ζ)⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} ≤
      ENNReal.ofReal (Real.exp (-cw * phi N ^ ζ)) := hW N hNw L' (q / 2) hG' hBS' hqKw
  have hPBo : ∀ p ∈ outsideGrid N (oosWin N C),
      L'.law (oosBo N ζ K a Co q (outsideGridE N (oosWin N C) p)) ≤
        ENNReal.ofReal (Real.exp (-co * phi N ^ ζ)) := by
    intro p hp
    obtain ⟨hpb, hp3⟩ := oos_grid_win hb0 hp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hdom⟩ := oos_pt h256 hP8 hK1 ha0 hCK hpb hp3
    exact hO N hNo L' (q / 2) _ hG' hBS' hqKo (hdom Ko hKo').2
  have hmu := oos_measure_union hT hmap (outsideGrid N (oosWin N C)) (by positivity)
    (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hsub hbad hPB1 hPBw hPBo
  refine hmu.trans (ENNReal.ofReal_le_ofReal ?_)
  have hexp : ∀ c' : ℝ, m ≤ c' → Real.exp (-c' * phi N ^ ζ) ≤ Real.exp (-m * phi N ^ ζ) := by
    intro c' hc'
    apply Real.exp_le_exp.mpr
    have hs0 : 0 ≤ phi N ^ ζ := Real.rpow_nonneg hP0.le ζ
    have h := mul_le_mul_of_nonneg_right hc' hs0
    linarith
  exact oos_real_bound (by omega) ((min_le_right _ _).trans (min_le_right _ _))
    (Real.rpow_nonneg hP0.le ζ) (Real.exp_pos _).le
    (hexp cs ((min_le_left _ _).trans (min_le_left _ _)))
    (hexp cw ((min_le_left _ _).trans (min_le_right _ _)))
    (hexp co ((min_le_right _ _).trans (min_le_left _ _))) (Nat.cast_nonneg _)
    (outsideGrid_card N _) hst hN2c hexpN

/-! ### Compiled checks -/

/-- The window `2 + φ^C N^{-2/3} ≤ E` contains `E = 5/2` for all large `N`. -/
private lemma oos_window_inst (C : ℝ) : ∀ᶠ N : ℕ in atTop,
    2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 5 / 2 := by
  filter_upwards [phi_rpow_le_rpow C (by norm_num : (0 : ℝ) < 1 / 6), eventually_ge_atTop 16]
    with N h6 h16
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hsq : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 4 := by
    rw [Real.rpow_neg hN0.le, inv_le_comm₀ (Real.rpow_pos_of_pos hN0 _) (by norm_num)]
    have h4 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (1 / 4 : ℝ)⁻¹ = (16 : ℝ) ^ (1 / 2 : ℝ) := by rw [h4]; norm_num
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hN16 (by norm_num)
  have h1 : phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 / 4 :=
    calc phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)
        ≤ (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hN0.le _)
      _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ 1 / 4 := hsq
  linarith

/-- Lemma 3.1 (5) for the Rademacher laws with `C0 = 1`, `c = 1/2`, `φs = 2/5`, `ζ = 1` and
`a = 13 > 12ζ`: for all large `N` the laws are generalized Wigner laws, the support parameter
`q = N^{2/5}` is admissible, the window of (3.7) contains `E = 5/2`, the third bound of (3.8) at
`E = 5/2` is below `1`, and the probability bound of the theorem applies to the event (3.8). -/
example : ∃ K > (0 : ℝ), ∃ C > (0 : ℝ), ∃ c' > (0 : ℝ), ∃ C' : ℕ, 0 < C' ∧ ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧
    (∃ q, (radLaws N).SupportParam ((N : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) q) ∧
    2 + phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 5 / 2 ∧
    0 < outEta N K 13 (5 / 2) ∧ (phi N ^ ((13 : ℝ) / 3) * N * outEta N K 13 (5 / 2))⁻¹ < 1 ∧
    (radLaws N).law (outEvent N K 13 C)ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c' * phi N ^ (1 : ℝ))) := by
  obtain ⟨K, hK, h⟩ := outOfSpectrum (ζ := 1) (C0 := 1) (c := 1 / 2) (φs := 2 / 5) one_pos
    zero_le_one (by norm_num) (by norm_num)
  obtain ⟨C, hC, c', hc', C', hC', N0, hN0⟩ := h 13 (by norm_num)
  refine ⟨K, hK, C, hC, c', hc', C', hC', ?_⟩
  filter_upwards [sc_rad_instance 0 1, eventually_ge_atTop N0, oos_window_inst C,
    eventually_ge_atTop 3] with N hi hN hw h3
  have hφ1 : 1 ≤ phi N := sc_one_le_phi h3
  have hq : ∃ q, (radLaws N).SupportParam ((N : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) q :=
    ⟨(N : ℝ) ^ (2 / 5 : ℝ), le_rfl, hi.2.1.boundedSupport (1 / 2), hi.2.1.tailVarOff (1 / 2)⟩
  have hκ : kappa (5 / 2) = 1 / 2 := by unfold kappa; norm_num [abs_of_pos]
  have hsq0 : 0 < Real.sqrt (kappa (5 / 2)) := by rw [hκ]; positivity
  have hsq1 : Real.sqrt (kappa (5 / 2)) < 1 := by
    rw [hκ, Real.sqrt_lt' one_pos]; norm_num
  have hη : 0 < outEta N K 13 (5 / 2) := by unfold outEta; positivity
  refine ⟨hi.1, hq, hw, hη, ?_, ?_⟩
  · have e : phi N ^ ((13 : ℝ) / 3) * N * outEta N K 13 (5 / 2) =
        phi N ^ ((13 : ℝ) / 3) * phi N ^ (K + 13) / Real.sqrt (kappa (5 / 2)) := by
      unfold outEta; field_simp
    rw [e, inv_lt_one₀ (by positivity), lt_div_iff₀ hsq0]
    have h1 : 1 ≤ phi N ^ ((13 : ℝ) / 3) := Real.one_le_rpow hφ1 (by norm_num)
    have h2 : 1 ≤ phi N ^ (K + 13) := Real.one_le_rpow hφ1 (by linarith)
    have := one_le_mul_of_one_le_of_one_le h1 h2
    linarith
  · have e : {ω : Entries N | (∃ q, (radLaws N).SupportParam ((N : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) q) →
        ω ∈ outEvent N K 13 C}ᶜ = (outEvent N K 13 C)ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      exact ⟨fun h hω => h fun _ => hω, fun h h' => h (h' hq)⟩
    have := hN0 N hN (radLaws N) hi.1
    rw [e] at this
    exact this

#print axioms outEvent
#print axioms outOfSpectrum

end WEdgeNS
