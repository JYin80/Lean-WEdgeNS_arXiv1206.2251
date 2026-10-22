import WEdgeNS.LocalLaw.Strong
import WEdgeNS.LocalLaw.Truncation

/-!
# The local semicircle law (Lemma 3.1 (1))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- Elementary bounds on `φ` and on `S(K)` from the module of the self-consistent equation, and
-- the estimate at `z = i` from the module of the strong law.
open private sc_one_le_phi sc_phi_pos sc_rpow_mono sc_specDomain_mono sc_specDomain
  sc_rad_instance from WEdgeNS.LocalLaw.SelfConsistent
open private strong_err_at_i from WEdgeNS.LocalLaw.Strong

/-! ### Perturbation of the resolvent by a small change of the entries -/

/-- The complex matrix `H - z`. -/
private def ifaceShift {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  H.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ)

/-- `(H - z) G = 1` for `0 < Im z`. -/
private lemma iface_shift_mul {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : ifaceShift H z * resolventC H z = 1 :=
  resolventC_mul_eq_one hH fun α h => by
    have := congrArg Complex.im h
    rw [Complex.ofReal_im] at this
    linarith

/-- `G (H - z) = 1` for `0 < Im z`. -/
private lemma iface_mul_shift {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) : resolventC H z * ifaceShift H z = 1 :=
  mul_eq_one_comm.mp (iface_shift_mul hH hz)

/-- The second resolvent identity `G - G' = G (H' - H) G'`. -/
private lemma iface_resolvent_sub {N : ℕ} {H H' : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    resolventC H z - resolventC H' z =
      resolventC H z * (H'.map (fun x : ℝ => (x : ℂ)) - H.map (fun x : ℝ => (x : ℂ))) *
        resolventC H' z := by
  have h1 := iface_mul_shift hH hz
  have h2 := iface_shift_mul hH' hz
  have e : H'.map (fun x : ℝ => (x : ℂ)) - H.map (fun x : ℝ => (x : ℂ)) =
      ifaceShift H' z - ifaceShift H z := by
    unfold ifaceShift; abel
  rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (resolventC H z) (ifaceShift H' z),
    h2, h1]
  simp

/-- Entrywise perturbation of the resolvent: `|G_ij - G'_ij| ≤ N² κ / η²` when the entries of
`H` and `H'` differ by at most `κ`. -/
private lemma iface_norm_resolvent_sub_le {N : ℕ} {H H' : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {κ : ℝ} (hd : ∀ i j, |H i j - H' i j| ≤ κ)
    {z : ℂ} (hz : 0 < z.im) (i j : Fin N) :
    ‖resolventC H z i j - resolventC H' z i j‖ ≤ (N : ℝ) ^ 2 * κ / z.im ^ 2 := by
  have hent : resolventC H z i j - resolventC H' z i j =
      ∑ l, ∑ k, resolventC H z i k * ((H' k l - H k l : ℝ) : ℂ) * resolventC H' z l j := by
    have := congrFun (congrFun (iface_resolvent_sub hH hH' hz) i) j
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
private lemma iface_norm_stieltjes_sub_le {N : ℕ} (hN : 0 < N) {H H' : Matrix (Fin N) (Fin N) ℝ}
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
          Finset.sum_le_sum fun i _ => iface_norm_resolvent_sub_le hH hH' hd hz i i
      _ = N * ((N : ℝ) ^ 2 * κ / z.im ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (N : ℝ)⁻¹ * ‖∑ i, (resolventC H z i i - resolventC H' z i i)‖
      ≤ (N : ℝ)⁻¹ * (N * ((N : ℝ) ^ 2 * κ / z.im ^ 2)) := by gcongr
    _ = (N : ℝ) ^ 2 * κ / z.im ^ 2 := by field_simp

/-! ### Monotonicity in the threshold `q` -/

/-- Raising the threshold `q` lowers the right side of (3.2). -/
private lemma iface_avgErr_anti {N : ℕ} {C q q' : ℝ} {z : ℂ} (hq : 0 < q) (hqq : q ≤ q')
    (hC : 0 ≤ phi N ^ C) : avgErr N C q' z ≤ avgErr N C q z := by
  unfold avgErr
  refine mul_le_mul_of_nonneg_left (add_le_add (min_le_min ?_ ?_) le_rfl) hC
  · have hq' : 0 < q' := hq.trans_le hqq
    rcases (Real.sqrt_nonneg (kappa z.re + z.im)).eq_or_lt with h | h
    · rw [← h]; simp
    · exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  · exact one_div_le_one_div_of_le hq hqq

/-- Raising the threshold `q` lowers the right side of (3.3). -/
private lemma iface_entryErr_anti {N : ℕ} {C q q' : ℝ} {z : ℂ} (hq : 0 < q) (hqq : q ≤ q')
    (hC : 0 ≤ phi N ^ C) : entryErr N C q' z ≤ entryErr N C q z := by
  unfold entryErr
  refine mul_le_mul_of_nonneg_left ?_ hC
  have := one_div_le_one_div_of_le hq hqq
  linarith

/-- `φ ≥ 0` for every `N`. -/
private lemma iface_phi_nonneg (N : ℕ) : 0 ≤ phi N :=
  Real.rpow_nonneg (Real.log_natCast_nonneg N) _

/-- The events (3.2) and (3.3) decrease as the threshold `q` increases. -/
private lemma iface_localLawEvent_anti (N : ℕ) (C : ℝ) {q q' : ℝ} (hq : 0 < q)
    (hqq : q ≤ q') : localLawEvent N C q' ⊆ localLawEvent N C q := by
  have hC : 0 ≤ phi N ^ C := Real.rpow_nonneg (iface_phi_nonneg N) C
  intro ω hω z hz
  obtain ⟨h1, h2⟩ := hω z hz
  exact ⟨h1.trans (iface_avgErr_anti hq hqq hC), fun i j =>
    (h2 i j).trans (iface_entryErr_anti hq hqq hC)⟩

/-! ### Comparison of the error bounds at the two levels -/

/-- The right side of (3.2) at level `(Cs, q / 2)` plus a perturbation `N⁴ κ` is at most the
right side at level `(Cs + 1, q)`. -/
private lemma iface_avgErr_le {N : ℕ} {Cs q κ : ℝ} {z : ℂ} (hN : 3 ≤ N) (hφ : 5 ≤ phi N)
    (hCs : 0 ≤ Cs) (hq : 0 < q) (hη : 0 < z.im) (hη10 : z.im ≤ 10)
    (hκ : (N : ℝ) ^ 4 * κ ≤ 1 / (10 * N)) :
    avgErr N Cs (q / 2) z + (N : ℝ) ^ 4 * κ ≤ avgErr N (Cs + 1) q z := by
  have hφ1 : 1 ≤ phi N := by linarith
  have ha : 1 ≤ phi N ^ Cs := Real.one_le_rpow hφ1 hCs
  have hpow : phi N ^ (Cs + 1) = phi N ^ Cs * phi N := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hNr : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set s := Real.sqrt (kappa z.re + z.im) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set w : ℝ := 1 / ((N : ℝ) * z.im) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : 1 / (10 * (N : ℝ)) ≤ w := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hM0 : 0 ≤ min (1 / (q ^ 2 * s)) (1 / q) := le_min (by positivity) (by positivity)
  have hM2 : min (1 / ((q / 2) ^ 2 * s)) (1 / (q / 2)) ≤
      4 * min (1 / (q ^ 2 * s)) (1 / q) := by
    have e1 : 1 / ((q / 2) ^ 2 * s) = 4 * (1 / (q ^ 2 * s)) := by
      have : (q / 2) ^ 2 * s = (q ^ 2 * s) / 4 := by ring
      rw [this, one_div_div]
      ring
    have e2 : 1 / (q / 2) = 2 * (1 / q) := by
      rw [one_div_div]; ring
    have hb0 : 0 ≤ 1 / q := by positivity
    rw [e1, e2]
    calc min (4 * (1 / (q ^ 2 * s))) (2 * (1 / q))
        ≤ min (4 * (1 / (q ^ 2 * s))) (4 * (1 / q)) := min_le_min le_rfl (by linarith)
      _ = 4 * min (1 / (q ^ 2 * s)) (1 / q) := (mul_min_of_nonneg _ _ (by norm_num)).symm
  unfold avgErr
  rw [hpow]
  set M := min (1 / (q ^ 2 * s)) (1 / q)
  set M2 := min (1 / ((q / 2) ^ 2 * s)) (1 / (q / 2))
  set a := phi N ^ Cs
  have h1 : 0 ≤ a * (phi N - 4) * M := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hM0
  have h2 : w ≤ a * (phi N - 1) * w := by
    have : 1 ≤ a * (phi N - 1) := by nlinarith
    nlinarith
  have h3 : a * M2 ≤ a * (4 * M) := mul_le_mul_of_nonneg_left hM2 (by linarith)
  have h4 : (N : ℝ) ^ 4 * κ ≤ w := hκ.trans hw1
  nlinarith

/-- The same comparison for the right side of (3.3). -/
private lemma iface_entryErr_le {N : ℕ} {Cs q κ : ℝ} {z : ℂ} (hN : 3 ≤ N) (hφ : 5 ≤ phi N)
    (hCs : 0 ≤ Cs) (hq : 0 < q) (hη : 0 < z.im) (hη10 : z.im ≤ 10)
    (hκ : (N : ℝ) ^ 4 * κ ≤ 1 / (10 * N)) :
    entryErr N Cs (q / 2) z + (N : ℝ) ^ 4 * κ ≤ entryErr N (Cs + 1) q z := by
  have hφ1 : 1 ≤ phi N := by linarith
  have ha : 1 ≤ phi N ^ Cs := Real.one_le_rpow hφ1 hCs
  have hpow : phi N ^ (Cs + 1) = phi N ^ Cs * phi N := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hNr : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set r := Real.sqrt ((msc z).im / ((N : ℝ) * z.im)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set w : ℝ := 1 / ((N : ℝ) * z.im) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : 1 / (10 * (N : ℝ)) ≤ w := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hb0 : 0 ≤ 1 / q := by positivity
  have e2 : 1 / (q / 2) = 2 * (1 / q) := by
    rw [one_div_div]; ring
  unfold entryErr
  rw [hpow, e2]
  set b := 1 / q
  set a := phi N ^ Cs
  have h1 : 0 ≤ a * (phi N - 2) * b := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb0
  have h1' : 0 ≤ a * (phi N - 1) * r := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hr0
  have h2 : w ≤ a * (phi N - 1) * w := by
    have : 1 ≤ a * (phi N - 1) := by nlinarith
    nlinarith
  have h4 : (N : ℝ) ^ 4 * κ ≤ w := hκ.trans hw1
  nlinarith

/-! ### Transfer of the events (3.2) and (3.3) between two matrices -/

/-- Transfer of (3.2) and (3.3) on `S(Cs + 1)` from `H'` at level `(Cs, q / 2)` to `H` at
level `(Cs + 1, q)`, when the entries of `H` and `H'` differ by at most `κ`. -/
private lemma iface_transfer {N : ℕ} {Cs q κ : ℝ} {H H' : Matrix (Fin N) (Fin N) ℝ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) (hN : 3 ≤ N) (hφ : 5 ≤ phi N) (hCs : 0 ≤ Cs)
    (hq : phi N ^ (Cs + 1) ≤ q) (hκ0 : 0 ≤ κ) (hκ : (N : ℝ) ^ 4 * κ ≤ 1 / (10 * N))
    (hd : ∀ i j, |H i j - H' i j| ≤ κ)
    (hev : ∀ z ∈ specDomain N Cs, ‖stieltjesM H' z - msc z‖ ≤ avgErr N Cs (q / 2) z ∧
      ∀ i j, ‖resolventC H' z i j - (if i = j then msc z else 0)‖ ≤ entryErr N Cs (q / 2) z) :
    ∀ z ∈ specDomain N (Cs + 1), ‖stieltjesM H z - msc z‖ ≤ avgErr N (Cs + 1) q z ∧
      ∀ i j, ‖resolventC H z i j - (if i = j then msc z else 0)‖ ≤ entryErr N (Cs + 1) q z := by
  intro z hz
  obtain ⟨_, hη, hη10, hNη⟩ := sc_specDomain hN hz
  have hz' : z ∈ specDomain N Cs := sc_specDomain_mono hN (by linarith) hz
  obtain ⟨h1, h2⟩ := hev z hz'
  have hφ1 : 1 ≤ phi N := by linarith
  have hφC : 1 ≤ phi N ^ (Cs + 1) := Real.one_le_rpow hφ1 (by linarith)
  have hq0 : 0 < q := by linarith
  have hNr : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNη1 : 1 ≤ (N : ℝ) * z.im := by linarith
  have hbound : (N : ℝ) ^ 2 * κ / z.im ^ 2 ≤ (N : ℝ) ^ 4 * κ := by
    rw [div_le_iff₀ (by positivity)]
    have h : 1 ≤ ((N : ℝ) * z.im) ^ 2 := one_le_pow₀ hNη1
    have h0 : 0 ≤ (N : ℝ) ^ 2 * κ := mul_nonneg (sq_nonneg _) hκ0
    nlinarith
  refine ⟨?_, fun i j => ?_⟩
  · calc ‖stieltjesM H z - msc z‖ ≤ ‖stieltjesM H z - stieltjesM H' z‖ +
          ‖stieltjesM H' z - msc z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (N : ℝ) ^ 4 * κ + avgErr N Cs (q / 2) z :=
          add_le_add ((iface_norm_stieltjes_sub_le (by omega) hH hH' hd hη).trans hbound) h1
      _ ≤ avgErr N (Cs + 1) q z := by
          have := iface_avgErr_le (z := z) hN hφ hCs hq0 hη hη10 hκ
          linarith
  · calc ‖resolventC H z i j - (if i = j then msc z else 0)‖
        ≤ ‖resolventC H z i j - resolventC H' z i j‖ +
          ‖resolventC H' z i j - (if i = j then msc z else 0)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (N : ℝ) ^ 4 * κ + entryErr N Cs (q / 2) z :=
          add_le_add ((iface_norm_resolvent_sub_le hH hH' hd hη i j).trans hbound) (h2 i j)
      _ ≤ entryErr N (Cs + 1) q z := by
          have := iface_entryErr_le (z := z) hN hφ hCs hq0 hη hη10 hκ
          linarith

/-! ### Asymptotic bounds -/

/-- `N ^ k exp (-b N ^ c) → 0`. -/
private lemma iface_tendsto_pow_mul_exp {c b : ℝ} (hc : 0 < c) (hb : 0 < b) (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-b * (N : ℝ) ^ c)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) / c) b hb
  have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  refine (h1.comp h2).congr fun N => ?_
  simp only [Function.comp_apply]
  congr 1
  have : c * ((k : ℝ) / c) = k := by field_simp
  rw [← Real.rpow_mul (Nat.cast_nonneg N), this, Real.rpow_natCast]

/-- The truncation error `2 N² exp(-N^c)` and the strong-law error add up to a single
`N exp(-c' φ^ζ)`. -/
private lemma iface_real_bound {N : ℕ} {ζ c cs : ℝ} (hN : 3 ≤ N)
    (h6 : phi N ^ ζ ≤ (N : ℝ) ^ (c / 2)) (h7 : 2 ≤ (N : ℝ) ^ (c / 2))
    (h5 : (N : ℝ) ^ 2 * Real.exp (-(1 / 2) * (N : ℝ) ^ c) < 1 / 2) :
    2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c) + Real.exp (-cs * phi N ^ ζ) ≤
      (N : ℝ) ^ 1 * Real.exp (-(min 1 cs) * phi N ^ ζ) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hφ0 : 0 ≤ phi N ^ ζ := Real.rpow_nonneg (sc_phi_pos hN).le ζ
  set t : ℝ := (N : ℝ) ^ (c / 2) with ht
  have hNc : (N : ℝ) ^ c = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1; push_cast; ring
  have hhalf : phi N ^ ζ ≤ (1 / 2) * (N : ℝ) ^ c := by
    rw [hNc]; nlinarith
  have hexp : Real.exp (-(N : ℝ) ^ c) ≤
      Real.exp (-phi N ^ ζ) * Real.exp (-(1 / 2) * (N : ℝ) ^ c) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hE : 2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c) ≤ Real.exp (-phi N ^ ζ) := by
    have hp : 0 < Real.exp (-phi N ^ ζ) := Real.exp_pos _
    calc 2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c)
        ≤ 2 * (N : ℝ) ^ 2 * (Real.exp (-phi N ^ ζ) * Real.exp (-(1 / 2) * (N : ℝ) ^ c)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp (-phi N ^ ζ) * (2 * ((N : ℝ) ^ 2 * Real.exp (-(1 / 2) * (N : ℝ) ^ c))) := by
          ring
      _ ≤ Real.exp (-phi N ^ ζ) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hp.le
          linarith
      _ = Real.exp (-phi N ^ ζ) := mul_one _
  have hm1 : min 1 cs ≤ 1 := min_le_left _ _
  have hmc : min 1 cs ≤ cs := min_le_right _ _
  have e1 : Real.exp (-phi N ^ ζ) ≤ Real.exp (-(min 1 cs) * phi N ^ ζ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (-cs * phi N ^ ζ) ≤ Real.exp (-(min 1 cs) * phi N ^ ζ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [pow_one]
  have hp : 0 < Real.exp (-(min 1 cs) * phi N ^ ζ) := Real.exp_pos _
  nlinarith

/-! ### The local semicircle law -/

/-- Lemma 3.1 (1) with Remark 3.2. -/
theorem localLaw {ζ C0 c : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) (hc : 0 < c) :
    ∃ C > 0, HighProbOn ζ (fun _ L => L.IsGenWigner C0)
      (fun N L => {ω | ∀ q, L.SupportParam (phi N ^ C) c q → ω ∈ localLawEvent N C q}) := by
  obtain ⟨Cs, hCs, cs, hcs, Ns, hNs⟩ :=
    localLaw_boundedAS (C0 := max C0 1) hζ (le_max_of_le_right zero_le_one)
  obtain ⟨Nt, hNt⟩ := exists_truncation hC0 hc
  have hc2 : 0 < c / 2 := half_pos hc
  have hev := (eventually_ge_atTop (max Ns Nt)).and <|
    (eventually_ge_atTop 16).and <|
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 5).and <|
    ((iface_tendsto_pow_mul_exp hc (by norm_num : (0 : ℝ) < 1 / 4) 5).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))).and <|
    ((iface_tendsto_pow_mul_exp hc (by norm_num : (0 : ℝ) < 1 / 2) 2).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and <|
    (phi_rpow_le_rpow ζ hc2).and <|
    (((tendsto_rpow_atTop hc2).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨Cs + 1, by linarith, highProbOn_forall_param (Q := fun N => phi N ^ (Cs + 1)) hc
    (fun N q q' hq hqq => iface_localLawEvent_anti N (Cs + 1) hq hqq) ?_⟩
  refine ⟨min 1 cs, lt_min one_pos hcs, 1, one_pos, N0, fun N hN L q hG hS => ?_⟩
  obtain ⟨hNN, h16, hlog5, h4, h5, h6, h7⟩ := hN0 N hN
  have hNs' : Ns ≤ N := le_trans (le_max_left _ _) hNN
  have hNt' : Nt ≤ N := le_trans (le_max_right _ _) hNN
  have h3 : 3 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast h3
    linarith
  have hφ5 : 5 ≤ phi N := hlog5.trans (log_le_phi h16)
  have hφ1 : 1 ≤ phi N := by linarith
  have hφC : 1 ≤ phi N ^ (Cs + 1) := Real.one_le_rpow hφ1 (by linarith)
  have hS1 : L.SupportParam 1 c q := ⟨hφC.trans hS.1, hS.2.1, hS.2.2⟩
  obtain ⟨L', T, hT, hmap, hG', hBS', hbad⟩ := hNt N hNt' L q hG hS1
  have hq2 : phi N ^ Cs ≤ q / 2 := by
    have hpow : phi N ^ (Cs + 1) = phi N ^ Cs * phi N := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have ha : 0 ≤ phi N ^ Cs := Real.rpow_nonneg (iface_phi_nonneg N) _
    have := hS.1
    nlinarith
  have hbd := hNs N hNs' L' (q / 2) hG' hBS' hq2
  set κ : ℝ := Real.exp (-(N : ℝ) ^ c / 4) with hκdef
  have hκ0 : 0 ≤ κ := (Real.exp_pos _).le
  have hκe : κ = Real.exp (-(1 / 4) * (N : ℝ) ^ c) := by
    rw [hκdef]; congr 1; ring
  have hκ : (N : ℝ) ^ 4 * κ ≤ 1 / (10 * N) := by
    rw [le_div_iff₀ (by positivity)]
    rw [hκe]
    calc (N : ℝ) ^ 4 * Real.exp (-(1 / 4) * (N : ℝ) ^ c) * (10 * N)
        = 10 * ((N : ℝ) ^ 5 * Real.exp (-(1 / 4) * (N : ℝ) ^ c)) := by ring
      _ ≤ 1 := by linarith
  have hsub : (localLawEvent N (Cs + 1) q)ᶜ ⊆
      {ω | ∃ i j, κ < |symOfEntries ω i j - symOfEntries (T ω) i j|} ∪
        T ⁻¹' (localLawEvent N Cs (q / 2))ᶜ := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, not_or,
      not_exists, not_lt, not_not] at hcon
    obtain ⟨hclose, hTω⟩ := hcon
    exact hω (iface_transfer (symOfEntries_isHermitian ω) (symOfEntries_isHermitian (T ω)) h3 hφ5
      hCs.le hS.1 hκ0 hκ hclose hTω)
  have hmeas : L.law (localLawEvent N (Cs + 1) q)ᶜ ≤
      ENNReal.ofReal (2 * (N : ℝ) ^ 2 * Real.exp (-(N : ℝ) ^ c)) +
        ENNReal.ofReal (Real.exp (-cs * phi N ^ ζ)) := by
    calc L.law (localLawEvent N (Cs + 1) q)ᶜ
        ≤ L.law ({ω | ∃ i j, κ < |symOfEntries ω i j - symOfEntries (T ω) i j|} ∪
            T ⁻¹' (localLawEvent N Cs (q / 2))ᶜ) := measure_mono hsub
      _ ≤ L.law {ω | ∃ i j, κ < |symOfEntries ω i j - symOfEntries (T ω) i j|} +
            L.law (T ⁻¹' (localLawEvent N Cs (q / 2))ᶜ) := measure_union_le _ _
      _ ≤ _ := by
          refine add_le_add hbad ?_
          calc L.law (T ⁻¹' (localLawEvent N Cs (q / 2))ᶜ)
              ≤ (L.law.map T) (localLawEvent N Cs (q / 2))ᶜ :=
                Measure.le_map_apply hT.aemeasurable _
            _ = L'.law (localLawEvent N Cs (q / 2))ᶜ := by rw [hmap]
            _ ≤ _ := hbd
  refine hmeas.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (iface_real_bound h3 h6 h7 h5)

/-! ### Compiled check -/

/-- Lemma 3.1 (1) for the Rademacher laws with `ζ = 1`, `C0 = 1`, `c = 1/2`: for all large `N`
the laws are generalized Wigner laws, `q = N^{2/5}` is an admissible support parameter, `i` lies
in `S(C)`, the errors of (3.2) and (3.3) at `i` are below `1` (while `|m(i) - m_sc(i)| ≤ 2` and
`|G_ii(i) - m_sc(i)| ≤ 2` hold for every matrix), and the conclusion of `localLaw` applies. -/
example : ∃ C > (0 : ℝ), ∃ c' > (0 : ℝ), ∃ C' : ℕ, ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧
    (radLaws N).SupportParam (phi N ^ C) (1 / 2) ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    (⟨0, 1⟩ : ℂ) ∈ specDomain N C ∧
    avgErr N C ((N : ℝ) ^ (2 / 5 : ℝ)) ⟨0, 1⟩ < 1 ∧
    entryErr N C ((N : ℝ) ^ (2 / 5 : ℝ)) ⟨0, 1⟩ < 1 ∧
    (radLaws N).law {ω | ∀ q, (radLaws N).SupportParam (phi N ^ C) (1 / 2) q →
        ω ∈ localLawEvent N C q}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c' * phi N ^ (1 : ℝ))) := by
  obtain ⟨C, hC, c', hc', C', hC', N0, h⟩ :=
    localLaw (ζ := 1) (C0 := 1) (c := 1 / 2) one_pos zero_le_one (by norm_num)
  refine ⟨C, hC, c', hc', C', ?_⟩
  filter_upwards [sc_rad_instance C 1, eventually_ge_atTop N0,
    phi_rpow_le_rpow C (by norm_num : (0 : ℝ) < 1 / 5), eventually_ge_atTop 244]
    with N hi hN h5 h244
  have hN1 : (244 : ℝ) ≤ N := by exact_mod_cast h244
  have hC0 : 0 ≤ phi N ^ C := Real.rpow_nonneg (sc_phi_pos (by omega)).le _
  obtain ⟨e1, e2⟩ := strong_err_at_i (by omega) h5 hC0
  have h3 : 3 < (N : ℝ) ^ (1 / 5 : ℝ) := by
    have h243 : (3 : ℝ) = ((3 : ℝ) ^ (5 : ℕ)) ^ ((5 : ℕ)⁻¹ : ℝ) :=
      (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
    rw [h243, show (1 / 5 : ℝ) = ((5 : ℕ)⁻¹ : ℝ) by norm_num]
    exact Real.rpow_lt_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have h31 : 3 / (N : ℝ) ^ (1 / 5 : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]; exact h3
  exact ⟨hi.1, ⟨hi.2.2.1, hi.2.1.boundedSupport _, hi.2.1.tailVarOff _⟩, hi.2.2.2.1,
    e1.trans_lt h31, e2.trans_lt h31, h N hN (radLaws N) hi.1⟩

#print axioms localLaw

end WEdgeNS
