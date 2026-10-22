import WEdgeNS.LocalLaw.FluctAvg

/-!
# The strong local semicircle law for almost surely bounded entries
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Right side of (3.2). -/
def avgErr (N : ℕ) (C q : ℝ) (z : ℂ) : ℝ :=
  phi N ^ C * (min (1 / (q ^ 2 * Real.sqrt (kappa z.re + z.im))) (1 / q) + 1 / (N * z.im))

/-- Right side of (3.3). -/
def entryErr (N : ℕ) (C q : ℝ) (z : ℂ) : ℝ :=
  phi N ^ C * (1 / q + Real.sqrt ((msc z).im / (N * z.im)) + 1 / (N * z.im))

/-- The events (3.2) and (3.3) on `S(C)`. -/
def localLawEvent (N : ℕ) (C q : ℝ) : Set (Entries N) :=
  {ω | ∀ z ∈ specDomain N C,
    ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ avgErr N C q z ∧
    ∀ i j, ‖resolventC (symOfEntries ω) z i j - (if i = j then msc z else 0)‖ ≤
      entryErr N C q z}

-- Elementary bounds on `φ`, on `S(K)` and on the control parameters, and the Lipschitz bounds
-- in `z`, from the modules of the self-consistent equation and of the weak law.
open private sc_one_le_phi sc_phi_pos sc_rpow_sq sc_rpow_mono sc_specDomain_mono sc_specDomain
  sc_msc_ne_zero sc_lamO_nonneg sc_lamD_nonneg sc_rad_instance from WEdgeNS.LocalLaw.SelfConsistent
open private weak_norm_msc_sub_le weak_norm_stieltjesM_sub_le weak_w_bounds weak_im_msc_le
  WeakMscBd WeakDich from WEdgeNS.LocalLaw.Weak

/-! ### From a lattice point to a nearby point: the estimate (4.5) of [15] -/

/-- The left side of (3.40) without `[Z]`, `(1 - a²) v - a³ v²`, moves by at most `13 ε` when
`a` moves by `ε` and `v` by `2 ε` inside the unit ball. -/
private lemma strong_F_sub_le {ε : ℝ} {a a' v v' : ℂ} (ha1 : ‖a‖ ≤ 1) (ha'1 : ‖a'‖ ≤ 1)
    (hv1 : ‖v‖ ≤ 1) (hv'1 : ‖v'‖ ≤ 1) (hda : ‖a - a'‖ ≤ ε) (hdv : ‖v - v'‖ ≤ 2 * ε) :
    ‖(1 - a ^ 2) * v - a ^ 3 * v ^ 2‖ ≤ ‖(1 - a' ^ 2) * v' - a' ^ 3 * v' ^ 2‖ + 13 * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hda
  have e : (1 - a ^ 2) * v - a ^ 3 * v ^ 2 = ((1 - a' ^ 2) * v' - a' ^ 3 * v' ^ 2) +
      ((1 - a ^ 2) * (v - v') - (a - a') * (a + a') * v' - a ^ 3 * (v - v') * (v + v') -
        (a - a') * (a ^ 2 + a * a' + a' ^ 2) * v' ^ 2) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  have n1 : ‖(1 - a ^ 2) * (v - v')‖ ≤ 2 * (2 * ε) := by
    rw [norm_mul]
    have h2 : ‖a ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha1
    have : ‖1 - a ^ 2‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      linarith
    exact mul_le_mul this hdv (norm_nonneg _) (by norm_num)
  have n2 : ‖(a - a') * (a + a') * v'‖ ≤ ε * 2 * 1 := by
    rw [norm_mul, norm_mul]
    have : ‖a + a'‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
    exact mul_le_mul (mul_le_mul hda this (norm_nonneg _) hε0) hv'1 (norm_nonneg _)
      (by positivity)
  have n3 : ‖a ^ 3 * (v - v') * (v + v')‖ ≤ 1 * (2 * ε) * 2 := by
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖a‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) ha1
    have : ‖v + v'‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
    exact mul_le_mul (mul_le_mul h1 hdv (norm_nonneg _) zero_le_one) this (norm_nonneg _)
      (by positivity)
  have n4 : ‖(a - a') * (a ^ 2 + a * a' + a' ^ 2) * v' ^ 2‖ ≤ ε * 3 * 1 := by
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖a ^ 2 + a * a' + a' ^ 2‖ ≤ 3 := by
      have k1 := norm_add_le (a ^ 2 + a * a') (a' ^ 2)
      have k2 := norm_add_le (a ^ 2) (a * a')
      rw [norm_pow] at k1
      rw [norm_pow, norm_mul] at k2
      have : ‖a‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) ha1
      have : ‖a'‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) ha'1
      have : ‖a‖ * ‖a'‖ ≤ 1 := by nlinarith only [ha1, ha'1, norm_nonneg a, norm_nonneg a']
      linarith
    have h2 : ‖v'‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hv'1
    exact mul_le_mul (mul_le_mul hda h1 (norm_nonneg _) hε0) h2 (by positivity)
      (by positivity)
  have m1 := norm_sub_le ((1 - a ^ 2) * (v - v') - (a - a') * (a + a') * v' -
    a ^ 3 * (v - v') * (v + v')) ((a - a') * (a ^ 2 + a * a' + a' ^ 2) * v' ^ 2)
  have m2 := norm_sub_le ((1 - a ^ 2) * (v - v') - (a - a') * (a + a') * v')
    (a ^ 3 * (v - v') * (v + v'))
  have m3 := norm_sub_le ((1 - a ^ 2) * (v - v')) ((a - a') * (a + a') * v')
  linarith

/-- The arithmetic behind (4.5) of [15] at `z` from (3.40) and (4.2) at a nearby point `p`:
`F' = |(1 - m_sc²)[v] - m_sc³[v]²|` at `p`, `Z = |[Z]|` at `p`, `Λ' = Λ(p)`, `I' = Im m_sc(p)`,
`n' = Nη_p`, and `Λ`, `I`, `n` the same quantities at `z`; `W = |1 - m_sc²|/|m_sc|³` at `z`. -/
private lemma strong_transfer_arith {Cm Cs s q lg n n' ε γ γ' Λ Λ' I I' W F' Z : ℝ}
    (hCm : 1 ≤ Cm) (hCs : 0 < Cs) (hs1 : 1 ≤ s) (hlg1 : 1 ≤ lg) (hlgs : lg ≤ s) (hq1 : 1 ≤ q)
    (hε0 : 0 ≤ ε) (hεq : s ^ 18 * ε ≤ 1 / q ^ 2) (hn1 : 1 ≤ n) (hnn : n ≤ 2 * n')
    (hn' : 0 < n') (hγ0 : 0 ≤ γ) (hγ' : γ' ≤ 2 * γ) (hΛ'0 : 0 ≤ Λ')
    (hΛ'γ : Λ' ≤ γ') (hΛ' : Λ' ≤ Λ + 2 * ε) (hW0 : 0 ≤ W) (hI : I ≤ Cm ^ 5 * W)
    (hI' : I' ≤ I + ε) (hI'0 : 0 ≤ I')
    (hF' : F' ≤ Cs * (s ^ 2 * lg / q ^ 2 + s ^ 4 * lg * ((Λ' + I') / n') + Λ' ^ 2 / lg) + Z)
    (hZ : Z ≤ s ^ 14 * (1 / q ^ 2 + 1 / n' ^ 2 + s ^ 4 * (I' + γ') / n')) :
    F' + 13 * ε ≤ 2 * Cs / lg * Λ ^ 2 +
      (40 + 40 * Cs) * Cm ^ 5 * (s ^ 14 / q ^ 2 + s ^ 14 / n ^ 2 + s ^ 18 * (W + γ) / n) := by
  have hq0 : 0 < q := by linarith
  have hn0 : 0 < n := by linarith
  have hlg0 : 0 < lg := by linarith
  have hs0 : 0 < s := by linarith
  have hC5 : 1 ≤ Cm ^ 5 := one_le_pow₀ hCm
  have hs14 : 1 ≤ s ^ 14 := one_le_pow₀ hs1
  have hs18 : 1 ≤ s ^ 18 := one_le_pow₀ hs1
  have hs2lg : s ^ 2 * lg ≤ s ^ 14 := by
    have h1 : s ^ 2 * lg ≤ s ^ 2 * s := mul_le_mul_of_nonneg_left hlgs (by positivity)
    have h3 : s ^ 2 * s = s ^ 3 := by ring
    have h4 : s ^ 3 ≤ s ^ 14 := pow_le_pow_right₀ hs1 (by norm_num)
    linarith
  have hs4lg : s ^ 4 * lg ≤ s ^ 18 := by
    have h1 : s ^ 4 * lg ≤ s ^ 4 * s := mul_le_mul_of_nonneg_left hlgs (by positivity)
    have h3 : s ^ 4 * s = s ^ 5 := by ring
    have h4 : s ^ 5 ≤ s ^ 18 := pow_le_pow_right₀ hs1 (by norm_num)
    linarith
  have hiq : 1 / q ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hq1
  have hεq' : ε ≤ 1 / q ^ 2 := le_trans (le_mul_of_one_le_left hε0 hs18) hεq
  have hε1 : ε ≤ 1 := hεq'.trans hiq
  have hT1' : 1 / q ^ 2 ≤ s ^ 14 / q ^ 2 := by
    rw [div_le_div_iff_of_pos_right (by positivity)]; exact hs14
  have hεn : s ^ 18 * ε / n ≤ s ^ 14 / q ^ 2 := by
    refine le_trans ?_ (hεq.trans hT1')
    exact div_le_self (by positivity) hn1
  have hinvn' : 1 / n' ≤ 2 / n := by
    rw [div_le_div_iff₀ hn' hn0]; linarith
  have hn'2 : 1 / n' ^ 2 ≤ 4 / n ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hnn, hn1, hn']
  set T1 := s ^ 14 / q ^ 2 with hT1
  set T2 := s ^ 14 / n ^ 2 with hT2
  set T3 := s ^ 18 * (W + γ) / n with hT3
  have hT10 : 0 ≤ T1 := by positivity
  have hT20 : 0 ≤ T2 := by positivity
  have hT30 : 0 ≤ T3 := by positivity
  have hX : s ^ 18 * (2 * γ + Cm ^ 5 * W + ε) / n ≤ 2 * Cm ^ 5 * T3 + T1 := by
    have c1 : s ^ 18 * (2 * γ + Cm ^ 5 * W) / n ≤ 2 * Cm ^ 5 * T3 := by
      rw [hT3, mul_div_assoc', div_le_div_iff_of_pos_right hn0]
      have h1 : 2 * γ + Cm ^ 5 * W ≤ 2 * Cm ^ 5 * (W + γ) := by
        nlinarith only [hC5, hγ0, hW0]
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ s ^ 18)
      linarith
    have e : s ^ 18 * (2 * γ + Cm ^ 5 * W + ε) / n =
        s ^ 18 * (2 * γ + Cm ^ 5 * W) / n + s ^ 18 * ε / n := by ring
    linarith
  have hΨ : (Λ' + I') / n' ≤ 2 * (2 * γ + Cm ^ 5 * W + ε) / n := by
    have h1 : Λ' + I' ≤ 2 * γ + Cm ^ 5 * W + ε := by linarith
    calc (Λ' + I') / n' = (Λ' + I') * (1 / n') := by ring
      _ ≤ (2 * γ + Cm ^ 5 * W + ε) * (2 / n) :=
          mul_le_mul h1 hinvn' (by positivity) (by linarith)
      _ = 2 * (2 * γ + Cm ^ 5 * W + ε) / n := by ring
  have hb1 : s ^ 2 * lg / q ^ 2 ≤ T1 := div_le_div_of_nonneg_right hs2lg (by positivity)
  have hb2 : s ^ 4 * lg * ((Λ' + I') / n') ≤ 4 * Cm ^ 5 * T3 + 2 * T1 := by
    have h0 : 0 ≤ (Λ' + I') / n' := by positivity
    have h1 : s ^ 4 * lg * ((Λ' + I') / n') ≤ s ^ 18 * (2 * (2 * γ + Cm ^ 5 * W + ε) / n) :=
      mul_le_mul hs4lg hΨ h0 (by positivity)
    have e : s ^ 18 * (2 * (2 * γ + Cm ^ 5 * W + ε) / n) =
        2 * (s ^ 18 * (2 * γ + Cm ^ 5 * W + ε) / n) := by ring
    linarith
  have hb3 : Λ' ^ 2 / lg ≤ 2 / lg * Λ ^ 2 + 8 * T1 := by
    have h1 : Λ' ^ 2 ≤ (Λ + 2 * ε) ^ 2 := pow_le_pow_left₀ hΛ'0 hΛ' 2
    have h2 : (Λ + 2 * ε) ^ 2 ≤ 2 * Λ ^ 2 + 8 * ε ^ 2 := by
      nlinarith only [sq_nonneg (Λ - 2 * ε)]
    have h3 : Λ' ^ 2 / lg ≤ (2 * Λ ^ 2 + 8 * ε ^ 2) / lg :=
      div_le_div_of_nonneg_right (h1.trans h2) hlg0.le
    have h4 : 8 * ε ^ 2 / lg ≤ 8 * ε := by
      rw [div_le_iff₀ hlg0]
      nlinarith only [hε0, hε1, hlg1]
    have e : (2 * Λ ^ 2 + 8 * ε ^ 2) / lg = 2 / lg * Λ ^ 2 + 8 * ε ^ 2 / lg := by ring
    linarith [hεq'.trans hT1']
  have hSCb : Cs * (s ^ 2 * lg / q ^ 2 + s ^ 4 * lg * ((Λ' + I') / n') + Λ' ^ 2 / lg) ≤
      2 * Cs / lg * Λ ^ 2 + Cs * (11 * T1 + 4 * Cm ^ 5 * T3) := by
    have h1 : s ^ 2 * lg / q ^ 2 + s ^ 4 * lg * ((Λ' + I') / n') + Λ' ^ 2 / lg ≤
        2 / lg * Λ ^ 2 + (11 * T1 + 4 * Cm ^ 5 * T3) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hCs.le
    have e : Cs * (2 / lg * Λ ^ 2 + (11 * T1 + 4 * Cm ^ 5 * T3)) =
        2 * Cs / lg * Λ ^ 2 + Cs * (11 * T1 + 4 * Cm ^ 5 * T3) := by ring
    linarith
  have hZb : Z ≤ 3 * T1 + 4 * T2 + 4 * Cm ^ 5 * T3 := by
    have c1 : s ^ 14 * (1 / n' ^ 2) ≤ 4 * T2 := by
      have := mul_le_mul_of_nonneg_left hn'2 (by positivity : (0 : ℝ) ≤ s ^ 14)
      have e : s ^ 14 * (4 / n ^ 2) = 4 * T2 := by rw [hT2]; ring
      linarith
    have c2 : s ^ 14 * (s ^ 4 * (I' + γ') / n') ≤ 4 * Cm ^ 5 * T3 + 2 * T1 := by
      have h1 : (I' + γ') / n' ≤ 2 * (2 * γ + Cm ^ 5 * W + ε) / n := by
        have h1 : I' + γ' ≤ 2 * γ + Cm ^ 5 * W + ε := by linarith
        calc (I' + γ') / n' = (I' + γ') * (1 / n') := by ring
          _ ≤ (2 * γ + Cm ^ 5 * W + ε) * (2 / n) :=
              mul_le_mul h1 hinvn' (by positivity) (by linarith)
          _ = 2 * (2 * γ + Cm ^ 5 * W + ε) / n := by ring
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ s ^ 18)
      have e1 : s ^ 14 * (s ^ 4 * (I' + γ') / n') = s ^ 18 * ((I' + γ') / n') := by ring
      have e2 : s ^ 18 * (2 * (2 * γ + Cm ^ 5 * W + ε) / n) =
          2 * (s ^ 18 * (2 * γ + Cm ^ 5 * W + ε) / n) := by ring
      linarith
    have e : s ^ 14 * (1 / q ^ 2 + 1 / n' ^ 2 + s ^ 4 * (I' + γ') / n') =
        T1 + s ^ 14 * (1 / n' ^ 2) + s ^ 14 * (s ^ 4 * (I' + γ') / n') := by
      rw [hT1]; ring
    linarith
  have hεT : 13 * ε ≤ 13 * T1 := by linarith [hεq'.trans hT1']
  have k1 : Cs * (11 * T1 + 4 * Cm ^ 5 * T3) ≤ Cs * (15 * Cm ^ 5 * (T1 + T2 + T3)) := by
    apply mul_le_mul_of_nonneg_left _ hCs.le
    nlinarith only [hC5, hT10, hT20, hT30]
  have k2 : 3 * T1 + 4 * T2 + 4 * Cm ^ 5 * T3 + 13 * T1 ≤ 20 * Cm ^ 5 * (T1 + T2 + T3) := by
    nlinarith only [hC5, hT10, hT20, hT30]
  have k3 : Cs * (15 * Cm ^ 5 * (T1 + T2 + T3)) + 20 * Cm ^ 5 * (T1 + T2 + T3) ≤
      (40 + 40 * Cs) * Cm ^ 5 * (T1 + T2 + T3) := by
    have : 0 ≤ Cm ^ 5 * (T1 + T2 + T3) := by positivity
    nlinarith only [this, hCs]
  linarith

/-- (3.40) and (4.2) of [15] at a point `p`, moved to a point `z` at distance `ε` in the
Lipschitz scale, give (4.5) at `z`: `a = m_sc(z)`, `a' = m_sc(p)`, `v = m(z) - m_sc(z)`,
`v' = m(p) - m_sc(p)`, `n = Nη_z`, `n' = Nη_p`, `Z = [Z](p)`. -/
private lemma strong_transfer {Cm Cs s q lg n n' ε γ γ' : ℝ} {a a' v v' Z : ℂ}
    (hCm : 1 ≤ Cm) (hCs : 0 < Cs) (ha1 : ‖a‖ ≤ 1) (ha'1 : ‖a'‖ ≤ 1) (haC : Cm⁻¹ ≤ ‖a‖)
    (hv1 : ‖v‖ ≤ 1) (hv'1 : ‖v'‖ ≤ 1) (hda : ‖a - a'‖ ≤ ε) (hdv : ‖v - v'‖ ≤ 2 * ε)
    (hs1 : 1 ≤ s) (hlg1 : 1 ≤ lg) (hlgs : lg ≤ s) (hq1 : 1 ≤ q)
    (hεq : s ^ 18 * ε ≤ 1 / q ^ 2) (hn1 : 1 ≤ n) (hnn : n ≤ 2 * n') (hn' : 0 < n')
    (hγ0 : 0 ≤ γ) (hγ' : γ' ≤ 2 * γ) (hv'γ : ‖v'‖ ≤ γ')
    (hIa : a.im ≤ Cm ^ 5 * ‖(1 - a ^ 2) / a ^ 3‖) (hIa' : a'.im ≤ a.im + ε) (hIa'0 : 0 ≤ a'.im)
    (hSC : ‖(1 - a' ^ 2) * v' - a' ^ 3 * v' ^ 2 - a' ^ 2 * Z‖ ≤
      Cs * (s ^ 2 * lg / q ^ 2 + s ^ 4 * lg * ((‖v'‖ + a'.im) / n') + ‖v'‖ ^ 2 / lg))
    (hFA : ‖Z‖ ≤ s ^ 14 * (1 / q ^ 2 + 1 / n' ^ 2 + s ^ 4 * (a'.im + γ') / n')) :
    ‖(1 - a ^ 2) / a ^ 3 * v - v ^ 2‖ ≤ 2 * Cm ^ 3 * Cs / lg * ‖v‖ ^ 2 +
      Cm ^ 8 * (40 + 40 * Cs) * (s ^ 14 / q ^ 2 + s ^ 14 / n ^ 2 +
        s ^ 18 * (‖(1 - a ^ 2) / a ^ 3‖ + γ) / n) := by
  have hCm0 : 0 < Cm := by linarith
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hda
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le (inv_pos.mpr hCm0) haC
  have hane : a ≠ 0 := norm_pos_iff.mp ha0
  have hF := strong_F_sub_le ha1 ha'1 hv1 hv'1 hda hdv
  have hF' : ‖(1 - a' ^ 2) * v' - a' ^ 3 * v' ^ 2‖ ≤
      ‖(1 - a' ^ 2) * v' - a' ^ 3 * v' ^ 2 - a' ^ 2 * Z‖ + ‖Z‖ := by
    have h1 := norm_add_le ((1 - a' ^ 2) * v' - a' ^ 3 * v' ^ 2 - a' ^ 2 * Z) (a' ^ 2 * Z)
    rw [sub_add_cancel] at h1
    refine h1.trans (add_le_add le_rfl ?_)
    rw [norm_mul, norm_pow]
    have : ‖a'‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) ha'1
    exact mul_le_of_le_one_left (norm_nonneg Z) this
  have hΛ' : ‖v'‖ ≤ ‖v‖ + 2 * ε := by
    have := norm_sub_norm_le v' v
    rw [norm_sub_rev] at this
    linarith
  have hA := strong_transfer_arith hCm hCs hs1 hlg1 hlgs hq1 hε0 hεq hn1 hnn hn' hγ0 hγ'
    (norm_nonneg v') hv'γ hΛ' (norm_nonneg _) hIa hIa' hIa'0
    (hF'.trans (add_le_add hSC le_rfl)) hFA
  have hdiv : (1 - a ^ 2) / a ^ 3 * v - v ^ 2 = ((1 - a ^ 2) * v - a ^ 3 * v ^ 2) / a ^ 3 := by
    field_simp
  rw [hdiv, norm_div, norm_pow, div_eq_mul_inv]
  have hinv3 : (‖a‖ ^ 3)⁻¹ ≤ Cm ^ 3 := by
    rw [← inv_pow]
    have : ‖a‖⁻¹ ≤ Cm := by rw [inv_le_comm₀ ha0 hCm0]; exact haC
    exact pow_le_pow_left₀ (by positivity) this 3
  have hFtot := hF.trans hA
  have hR : 0 ≤ 2 * Cs / lg * ‖v‖ ^ 2 + (40 + 40 * Cs) * Cm ^ 5 * (s ^ 14 / q ^ 2 +
      s ^ 14 / n ^ 2 + s ^ 18 * (‖(1 - a ^ 2) / a ^ 3‖ + γ) / n) := by
    have : 0 < lg := by linarith
    have : 0 < n := by linarith
    positivity
  calc ‖(1 - a ^ 2) * v - a ^ 3 * v ^ 2‖ * (‖a‖ ^ 3)⁻¹ ≤
        (2 * Cs / lg * ‖v‖ ^ 2 + (40 + 40 * Cs) * Cm ^ 5 * (s ^ 14 / q ^ 2 +
          s ^ 14 / n ^ 2 + s ^ 18 * (‖(1 - a ^ 2) / a ^ 3‖ + γ) / n)) * Cm ^ 3 :=
        mul_le_mul hFtot hinv3 (by positivity) hR
    _ = _ := by ring

/-! ### The continuity argument of Lemma 4.2 of [15] -/

/-- The distance of two points on one vertical line. -/
private lemma strong_norm_vert (E a b : ℝ) : ‖(⟨E, a⟩ : ℂ) - ⟨E, b⟩‖ = |a - b| := by
  have e : (⟨E, a⟩ : ℂ) - ⟨E, b⟩ = ((a - b : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- A function with the Lipschitz bound `|f(z) - f(w)| ≤ c |z - w|/(Im z Im w)` is continuous on
every vertical segment `E + i[η, 10]` with `η > 0`. -/
private lemma strong_contOn_vert {f : ℂ → ℂ} {c E η : ℝ} (hc : 0 ≤ c) (hη : 0 < η)
    (hf : ∀ z w : ℂ, 0 < z.im → 0 < w.im → ‖f z - f w‖ ≤ c * (‖z - w‖ / (z.im * w.im))) :
    ContinuousOn (fun y : ℝ => f ⟨E, y⟩) (Set.Icc η 10) := by
  have hK : 0 ≤ c / η ^ 2 := by positivity
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (c / η ^ 2)) ?_).continuousOn
  intro a ha b hb
  rw [Real.coe_toNNReal _ hK, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
  have ha0 : 0 < a := lt_of_lt_of_le hη ha.1
  have hb0 : 0 < b := lt_of_lt_of_le hη hb.1
  have h1 := hf ⟨E, a⟩ ⟨E, b⟩ ha0 hb0
  simp only at h1
  rw [strong_norm_vert] at h1
  refine h1.trans ?_
  have h2 : |a - b| / (a * b) ≤ |a - b| / η ^ 2 := by
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    rw [sq]
    exact mul_le_mul ha.1 hb.1 hη.le ha0.le
  calc c * (|a - b| / (a * b)) ≤ c * (|a - b| / η ^ 2) := mul_le_mul_of_nonneg_left h2 hc
    _ = c / η ^ 2 * |a - b| := by ring

/-- The dichotomy of Lemma 3.17 of [15] at every point of `S(C)`, together with the continuity
in `η` along vertical lines, gives `Λ ≤ max(U, C₁) β` on `S(C)` (the continuity argument in the
proof of Lemma 4.2 of [15]). Here `β` decreases in `η` on vertical lines and the bad branch
`Λ ≥ |w|/U` is excluded at `η = 10`. -/
private lemma strong_cont_dich {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hN : 3 ≤ N)
    (hH : H.IsHermitian) {Cd Cm U C1 δ : ℝ} {β : ℂ → ℝ} (hCm : 1 ≤ Cm) (hU : 0 < U)
    (hmsc : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
      (Cm⁻¹ ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ Cm) ∧
      (Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ ‖1 - msc z ^ 2‖ ∧
        ‖1 - msc z ^ 2‖ ≤ Cm * Real.sqrt (kappa z.re + z.im)))
    (hdich : ∀ (w v : ℂ) (t β δ : ℝ), 0 < t → 0 < β → 0 ≤ δ → δ ≤ 1 / 2 →
      (Cm ^ 4)⁻¹ * t ≤ ‖w‖ → ‖w‖ ≤ Cm ^ 4 * t →
      ‖w * v - v ^ 2‖ ≤ δ * ‖v‖ ^ 2 + 1 * (β * ‖v‖ + ‖w‖ * β + β ^ 2) →
      (2 * U ^ 2 * Cm ^ 4 * β ≤ t → ‖v‖ ≤ U * β ∨ ‖w‖ / U ≤ ‖v‖) ∧
      (t < 2 * U ^ 2 * Cm ^ 4 * β → ‖v‖ ≤ C1 * β))
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (h45 : ∀ z ∈ specDomain N Cd,
      ‖(1 - msc z ^ 2) / msc z ^ 3 * (stieltjesM H z - msc z) - (stieltjesM H z - msc z) ^ 2‖ ≤
        δ * ‖stieltjesM H z - msc z‖ ^ 2 + 1 * (β z * ‖stieltjesM H z - msc z‖ +
          ‖(1 - msc z ^ 2) / msc z ^ 3‖ * β z + β z ^ 2))
    (hβ : ∀ z ∈ specDomain N Cd, 0 < β z)
    (hβanti : ∀ z ∈ specDomain N Cd, ∀ y : ℝ, z.im ≤ y → y ≤ 10 → β ⟨z.re, y⟩ ≤ β z)
    (htop : ∀ E : ℝ, (⟨E, 10⟩ : ℂ) ∈ specDomain N Cd → ‖stieltjesM H ⟨E, 10⟩ - msc ⟨E, 10⟩‖ <
      ‖(1 - msc ⟨E, 10⟩ ^ 2) / msc ⟨E, 10⟩ ^ 3‖ / U) :
    ∀ z ∈ specDomain N Cd, ‖stieltjesM H z - msc z‖ ≤ max U C1 * β z := by
  intro z hz
  obtain ⟨hre, hpos, hle, -⟩ := sc_specDomain hN hz
  have hCm0 : 0 < Cm := by linarith
  have hK0 : 0 < Cm ^ 4 := by positivity
  set E := z.re with hE
  set η := z.im with hη
  -- the vertical segment above `z` lies in `S(C)`
  have hseg : ∀ y ∈ Set.Icc η 10, (⟨E, y⟩ : ℂ) ∈ specDomain N Cd := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := hz
    exact ⟨h1, lt_of_lt_of_le h2 hy.1, hy.2⟩
  have hz' : (⟨E, η⟩ : ℂ) = z := Complex.ext rfl rfl
  -- `t = √(κ + η)` and the dichotomy at every point of `S(C)`
  have ht : ∀ w ∈ specDomain N Cd, 0 < Real.sqrt (kappa w.re + w.im) := by
    intro w hw
    obtain ⟨-, hwpos, -, -⟩ := sc_specDomain hN hw
    have : 0 ≤ kappa w.re := abs_nonneg _
    exact Real.sqrt_pos.mpr (by linarith)
  have hWb : ∀ w ∈ specDomain N Cd,
      (Cm ^ 4)⁻¹ * Real.sqrt (kappa w.re + w.im) ≤ ‖(1 - msc w ^ 2) / msc w ^ 3‖ ∧
      ‖(1 - msc w ^ 2) / msc w ^ 3‖ ≤ Cm ^ 4 * Real.sqrt (kappa w.re + w.im) := by
    intro w hw
    obtain ⟨hwre, hwpos, hwle, -⟩ := sc_specDomain hN hw
    obtain ⟨⟨m1, m2⟩, ⟨m3, m4⟩⟩ := hmsc w hwre hwpos hwle
    exact weak_w_bounds hCm m1 m2 m3 m4
  have hD : ∀ w ∈ specDomain N Cd,
      (2 * U ^ 2 * Cm ^ 4 * β w ≤ Real.sqrt (kappa w.re + w.im) →
        ‖stieltjesM H w - msc w‖ ≤ U * β w ∨
          ‖(1 - msc w ^ 2) / msc w ^ 3‖ / U ≤ ‖stieltjesM H w - msc w‖) ∧
      (Real.sqrt (kappa w.re + w.im) < 2 * U ^ 2 * Cm ^ 4 * β w →
        ‖stieltjesM H w - msc w‖ ≤ C1 * β w) := fun w hw =>
    hdich _ _ _ _ _ (ht w hw) (hβ w hw) hδ0 hδ1 (hWb w hw).1 (hWb w hw).2 (h45 w hw)
  have hβz := hβ z hz
  rcases lt_or_ge (Real.sqrt (kappa E + η)) (2 * U ^ 2 * Cm ^ 4 * β z) with hc | hc
  · exact ((hD z hz).2 hc).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hβz.le)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) hβz.le)
  -- on the segment the first case holds, and the two branches are separated by `g`
  set g : ℝ → ℝ := fun y => ‖stieltjesM H ⟨E, y⟩ - msc ⟨E, y⟩‖ -
    3 / 4 * ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / U with hg
  have hbr : ∀ y ∈ Set.Icc η 10,
      (‖stieltjesM H ⟨E, y⟩ - msc ⟨E, y⟩‖ ≤ U * β ⟨E, y⟩ ∧ g y < 0) ∨
        (‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / U ≤ ‖stieltjesM H ⟨E, y⟩ - msc ⟨E, y⟩‖ ∧
          0 < g y) := by
    intro y hy
    have hw := hseg y hy
    have hβy : β ⟨E, y⟩ ≤ β z := hβanti z hz y hy.1 hy.2
    have hty : Real.sqrt (kappa E + η) ≤ Real.sqrt (kappa E + y) :=
      Real.sqrt_le_sqrt (by linarith [hy.1])
    have hcy : 2 * U ^ 2 * Cm ^ 4 * β ⟨E, y⟩ ≤ Real.sqrt (kappa E + y) := by
      have : 2 * U ^ 2 * Cm ^ 4 * β ⟨E, y⟩ ≤ 2 * U ^ 2 * Cm ^ 4 * β z :=
        mul_le_mul_of_nonneg_left hβy (by positivity)
      linarith
    have htw := ht _ hw
    have hWw := hWb _ hw
    simp only at htw hWw
    have hW0 : 0 < ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ :=
      lt_of_lt_of_le (by positivity) hWw.1
    rcases (hD _ hw).1 hcy with h | h
    · left
      refine ⟨h, ?_⟩
      have h1 : U * β ⟨E, y⟩ ≤ ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / (2 * U) := by
        rw [le_div_iff₀ (by positivity)]
        have h2 : 2 * U ^ 2 * Cm ^ 4 * β ⟨E, y⟩ ≤
            Cm ^ 4 * ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ := by
          have : Real.sqrt (kappa E + y) ≤
              Cm ^ 4 * ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ := by
            have := mul_le_mul_of_nonneg_left hWw.1 hK0.le
            rwa [← mul_assoc, mul_inv_cancel₀ hK0.ne', one_mul] at this
          linarith
        have e : U * β ⟨E, y⟩ * (2 * U) * Cm ^ 4 = 2 * U ^ 2 * Cm ^ 4 * β ⟨E, y⟩ := by ring
        have h3 : U * β ⟨E, y⟩ * (2 * U) * Cm ^ 4 ≤
            ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ * Cm ^ 4 := by linarith
        exact le_of_mul_le_mul_right h3 hK0
      have e : ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / (2 * U) =
          2 / 3 * (3 / 4 * ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / U) := by
        field_simp
        ring
      have hpos3 : 0 < 3 / 4 * ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / U := by positivity
      simp only [hg]
      linarith
    · right
      refine ⟨h, ?_⟩
      have hpos3 : 0 < ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / U := by positivity
      have e : 3 / 4 * ‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / U =
          3 / 4 * (‖(1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3‖ / U) := by ring
      simp only [hg]
      linarith
  have hηmem : η ∈ Set.Icc η 10 := ⟨le_rfl, hle⟩
  have h10mem : (10 : ℝ) ∈ Set.Icc η 10 := ⟨hle, le_rfl⟩
  have hg10 : g 10 < 0 := by
    rcases hbr 10 h10mem with h | h
    · exact h.2
    · exact absurd h.1 (not_le.mpr (htop E (hseg 10 h10mem)))
  rcases hbr η hηmem with h | h
  · rw [hz'] at h
    exact h.1
  exfalso
  -- the intermediate value theorem on `[η, 10]`
  have hcont : ContinuousOn g (Set.Icc η 10) := by
    have hm : ContinuousOn (fun y : ℝ => stieltjesM H ⟨E, y⟩) (Set.Icc η 10) := by
      refine strong_contOn_vert zero_le_one hpos (fun a b ha hb => ?_)
      rw [one_mul]
      exact weak_norm_stieltjesM_sub_le (by omega) hH ha hb
    have hs : ContinuousOn (fun y : ℝ => msc ⟨E, y⟩) (Set.Icc η 10) := by
      refine strong_contOn_vert zero_le_one hpos (fun a b ha hb => ?_)
      rw [one_mul]
      exact weak_norm_msc_sub_le ha hb
    have hne : ∀ y ∈ Set.Icc η 10, msc ⟨E, y⟩ ^ 3 ≠ 0 := by
      intro y hy
      have : (0 : ℝ) < (⟨E, y⟩ : ℂ).im := lt_of_lt_of_le hpos hy.1
      exact pow_ne_zero 3 (sc_msc_ne_zero this)
    have hW : ContinuousOn (fun y : ℝ => (1 - msc ⟨E, y⟩ ^ 2) / msc ⟨E, y⟩ ^ 3)
        (Set.Icc η 10) := (continuousOn_const.sub (hs.pow 2)).div (hs.pow 3) hne
    exact ((hm.sub hs).norm.sub ((hW.norm.const_smul (3 / 4 : ℝ)).div_const U)).congr
      (fun y _ => by simp [hg, smul_eq_mul, mul_div_assoc])
  obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc' hle hcont ⟨hg10.le, h.2.le⟩
  rcases hbr c hc with h' | h'
  · linarith [h'.2]
  · linarith [h'.2]

/-! ### (4.5) of [15] on all of `S(C)` from the lattice -/

/-- The Lipschitz scale between `z ∈ S(C)` and a lattice point `p ∈ S(C)` with
`|z - p| ≤ N⁻³`: `|z - p|/(η_z η_p) ≤ 1/(N φ^{2C})`, and `η_z ≤ 2 η_p`. -/
private lemma strong_lattice_scale {N : ℕ} (hN : 3 ≤ N) {C : ℝ} (hC1 : 1 ≤ phi N ^ C) {z p : ℂ}
    (hz : z ∈ specDomain N C) (hp : p ∈ specDomain N C) (hzp : ‖z - p‖ ≤ (N : ℝ) ^ (-(3 : ℝ))) :
    ‖z - p‖ / (z.im * p.im) ≤ 1 / (N * (phi N ^ C) ^ 2) ∧ z.im ≤ 2 * p.im ∧
      1 ≤ N * z.im ∧ 1 ≤ N * p.im := by
  obtain ⟨-, hzl, -⟩ := hz
  obtain ⟨-, hpl, -⟩ := hp
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hφ0 : 0 < phi N ^ C := by linarith
  have hn3 : (N : ℝ) ^ (-(3 : ℝ)) = 1 / (N : ℝ) ^ 3 := by
    rw [Real.rpow_neg hN0.le, one_div, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [hn3] at hzp
  have hzi : 0 < z.im := lt_of_le_of_lt (by positivity) hzl
  have hpi : 0 < p.im := lt_of_le_of_lt (by positivity) hpl
  have hz1 : 1 ≤ N * z.im := by
    rw [div_lt_iff₀ hN0] at hzl
    linarith [mul_comm (N : ℝ) z.im]
  have hp1 : 1 ≤ N * p.im := by
    rw [div_lt_iff₀ hN0] at hpl
    linarith [mul_comm (N : ℝ) p.im]
  refine ⟨?_, ?_, hz1, hp1⟩
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : phi N ^ C ≤ N * z.im := by
      rw [div_lt_iff₀ hN0] at hzl; linarith [mul_comm (N : ℝ) z.im]
    have h2 : phi N ^ C ≤ N * p.im := by
      rw [div_lt_iff₀ hN0] at hpl; linarith [mul_comm (N : ℝ) p.im]
    have h3 : (phi N ^ C) ^ 2 ≤ (N * z.im) * (N * p.im) := by
      rw [sq]; exact mul_le_mul h1 h2 hφ0.le (by positivity)
    have h4 : ‖z - p‖ * (N : ℝ) ^ 3 ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hzp; exact hzp
    have h5 : ‖z - p‖ * (N * (phi N ^ C) ^ 2) ≤ ‖z - p‖ * (N * ((N * z.im) * (N * p.im))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hN0.le) (norm_nonneg _)
    have e : ‖z - p‖ * (N * ((N * z.im) * (N * p.im))) =
        ‖z - p‖ * (N : ℝ) ^ 3 * (z.im * p.im) := by ring
    have h6 : ‖z - p‖ * (N : ℝ) ^ 3 * (z.im * p.im) ≤ 1 * (z.im * p.im) :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    linarith
  · have h1 : |z.im - p.im| ≤ ‖z - p‖ := by
      have := Complex.abs_im_le_norm (z - p)
      rwa [Complex.sub_im] at this
    have h2 : 1 / (N : ℝ) ^ 3 ≤ p.im := by
      have h3 : 1 / (N : ℝ) ^ 3 ≤ 1 / N := by
        apply div_le_div_of_nonneg_left zero_le_one hN0
        calc (N : ℝ) = N ^ 1 := (pow_one _).symm
          _ ≤ N ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
      have h4 : 1 / (N : ℝ) ≤ p.im := by
        rw [div_le_iff₀ hN0]; linarith [mul_comm (N : ℝ) p.im]
      linarith
    have := (abs_le.mp h1).2
    linarith

/-- (4.5) of [15] at every `z ∈ S(C)`: (3.40) and (4.2) hold at the points of a lattice that is
`N⁻³`-dense in `S(C)`, the a priori bound `Λ ≤ γ ≤ 1` holds on `S(C)`, and `γ` changes by at most
a factor `2` between neighbouring points. -/
private lemma strong_45_all {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hN : 3 ≤ N)
    (hH : H.IsHermitian) {C Cm Cs q s : ℝ} {γ : ℂ → ℝ} {Λl : Finset ℂ}
    (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hCs : 0 < Cs)
    (hΛlS : (↑Λl : Set ℂ) ⊆ specDomain N C)
    (hΛl : ∀ z ∈ specDomain N C, ∃ p ∈ Λl, ‖z - p‖ ≤ (N : ℝ) ^ (-(3 : ℝ)))
    (hC1 : 1 ≤ phi N ^ C) (hs1 : 1 ≤ s) (hlg : 1 ≤ Real.log N) (hlgs : Real.log N ≤ s)
    (hq1 : 1 ≤ q) (hεq : s ^ 18 * (1 / (N * (phi N ^ C) ^ 2)) ≤ 1 / q ^ 2)
    (hγ0 : ∀ z ∈ specDomain N C, 0 ≤ γ z) (hγ1 : ∀ z ∈ specDomain N C, γ z ≤ 1)
    (hγp : ∀ z ∈ specDomain N C, ∀ p ∈ specDomain N C, ‖z - p‖ ≤ (N : ℝ) ^ (-(3 : ℝ)) →
      γ p ≤ 2 * γ z)
    (hΛγ : ∀ z ∈ specDomain N C, lamAvg H z ≤ γ z)
    (hSC : ∀ p ∈ Λl, ‖(1 - msc p ^ 2) * (stieltjesM H p - msc p) -
        msc p ^ 3 * (stieltjesM H p - msc p) ^ 2 - msc p ^ 2 * zAvg H p‖ ≤
      Cs * (s ^ 2 * Real.log N / q ^ 2 + s ^ 4 * Real.log N * psiCtrl H p ^ 2 +
        lamAvg H p ^ 2 / Real.log N))
    (hFA : ∀ p ∈ Λl, ‖zAvg H p‖ ≤ s ^ 14 * (1 / q ^ 2 + 1 / (N * p.im) ^ 2 +
        s ^ 4 * ((msc p).im + γ p) / (N * p.im))) :
    ∀ z ∈ specDomain N C,
      ‖(1 - msc z ^ 2) / msc z ^ 3 * (stieltjesM H z - msc z) - (stieltjesM H z - msc z) ^ 2‖ ≤
        2 * Cm ^ 3 * Cs / Real.log N * ‖stieltjesM H z - msc z‖ ^ 2 +
          Cm ^ 8 * (40 + 40 * Cs) * (s ^ 14 / q ^ 2 + s ^ 14 / (N * z.im) ^ 2 +
            s ^ 18 * (‖(1 - msc z ^ 2) / msc z ^ 3‖ + γ z) / (N * z.im)) := by
  intro z hz
  obtain ⟨p, hpΛ, hzp⟩ := hΛl z hz
  have hp : p ∈ specDomain N C := hΛlS (Finset.mem_coe.mpr hpΛ)
  obtain ⟨hzre, hzi, hzle, -⟩ := sc_specDomain hN hz
  obtain ⟨-, hpi, -, -⟩ := sc_specDomain hN hp
  obtain ⟨hsc, hzp2, hn1, hn'1⟩ := strong_lattice_scale hN hC1 hz hp hzp
  set ε : ℝ := 1 / (N * (phi N ^ C) ^ 2) with hε
  have hda : ‖msc z - msc p‖ ≤ ε := (weak_norm_msc_sub_le hzi hpi).trans hsc
  have hdm : ‖stieltjesM H z - stieltjesM H p‖ ≤ ε :=
    (weak_norm_stieltjesM_sub_le (by omega) hH hzi hpi).trans hsc
  have hdv : ‖(stieltjesM H z - msc z) - (stieltjesM H p - msc p)‖ ≤ 2 * ε := by
    have e : (stieltjesM H z - msc z) - (stieltjesM H p - msc p) =
        (stieltjesM H z - stieltjesM H p) - (msc z - msc p) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith
  obtain ⟨⟨hm1, -⟩, ⟨ht1, ht2⟩, h3, h4⟩ := hmsc z hzre hzi hzle
  have hCm0 : 0 ≤ Cm := by linarith
  have hIa : (msc z).im ≤ Cm ^ 5 * ‖(1 - msc z ^ 2) / msc z ^ 3‖ := by
    have hI := weak_im_msc_le hzi hCm0 h3 h4
    obtain ⟨hw1, -⟩ := weak_w_bounds hCm hm1 (hmsc z hzre hzi hzle).1.2 ht1 ht2
    have hK : 0 < Cm ^ 4 := by positivity
    have : Real.sqrt (kappa z.re + z.im) ≤ Cm ^ 4 * ‖(1 - msc z ^ 2) / msc z ^ 3‖ := by
      have := mul_le_mul_of_nonneg_left hw1 hK.le
      rwa [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] at this
    calc (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im) := hI
      _ ≤ Cm * (Cm ^ 4 * ‖(1 - msc z ^ 2) / msc z ^ 3‖) := mul_le_mul_of_nonneg_left this hCm0
      _ = Cm ^ 5 * ‖(1 - msc z ^ 2) / msc z ^ 3‖ := by ring
  have hIa' : (msc p).im ≤ (msc z).im + ε := by
    have h1 : |(msc p).im - (msc z).im| ≤ ‖msc p - msc z‖ := by
      have := Complex.abs_im_le_norm (msc p - msc z)
      rwa [Complex.sub_im] at this
    rw [norm_sub_rev] at h1
    linarith [(abs_le.mp (h1.trans hda)).2]
  have hpsi : psiCtrl H p ^ 2 = (‖stieltjesM H p - msc p‖ + (msc p).im) / (N * p.im) := by
    unfold psiCtrl lamAvg
    rw [Real.sq_sqrt]
    have := im_msc_pos hpi
    positivity
  have hSCp := hSC p hpΛ
  rw [hpsi] at hSCp
  unfold lamAvg at hSCp
  have hvz : ‖stieltjesM H z - msc z‖ ≤ 1 := (hΛγ z hz).trans (hγ1 z hz)
  have hvp : ‖stieltjesM H p - msc p‖ ≤ γ p := hΛγ p hp
  have hεq' : s ^ 18 * ε ≤ 1 / q ^ 2 := hεq
  have h := strong_transfer (Z := zAvg H p) hCm hCs (norm_msc_eq_inv_and_lt_one hzi).2.le
    (norm_msc_eq_inv_and_lt_one hpi).2.le hm1 hvz (hvp.trans (hγ1 p hp)) hda hdv hs1 hlg hlgs
    hq1 hεq' hn1 (by nlinarith only [hzp2, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) (by linarith)
    (hγ0 z hz) (hγp z hz p hp hzp) hvp hIa hIa'
    (im_msc_pos hpi).le hSCp (hFA p hpΛ)
  exact h

/-! ### One step of the iteration: Lemma 4.2 of [15] -/

/-- `x = 1/q + 1/(Nη)`, the control parameter of (4.4) and (4.7) of [15]. -/
private def strongX (N : ℕ) (q : ℝ) (z : ℂ) : ℝ := 1 / q + 1 / (N * z.im)

private lemma strong_rpow_facts {X τ : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1) (hτ0 : 0 ≤ τ) :
    X ^ (1 - τ) * X = (X ^ (1 - τ / 2)) ^ 2 ∧ X ^ 2 ≤ (X ^ (1 - τ / 2)) ^ 2 ∧
      X ≤ X ^ (1 - τ / 2) ∧ 0 < X ^ (1 - τ / 2) := by
  have e2 : (X ^ (1 - τ / 2)) ^ 2 = X ^ (2 - τ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    norm_num
    ring_nf
  refine ⟨?_, ?_, ?_, Real.rpow_pos_of_pos hX0 _⟩
  · rw [e2]
    conv_lhs => rw [show X ^ (1 - τ) * X = X ^ (1 - τ) * X ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hX0]
    ring_nf
  · rw [e2]
    have := Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by linarith : 2 - τ ≤ 2)
    rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  · have := Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by linarith : 1 - τ / 2 ≤ 1)
    rwa [Real.rpow_one] at this

/-- Lemma 4.2 of [15] for one matrix, with `s1 = s`, `(log N)^{19 ξ₂} = σ^{20}`: from (4.5) on
`S(C)` with the a priori bound `γ ≤ σ^{20} x^{1-τ}` ((4.4)), and `Λ ≤ σ⁻¹` ((4.6)), it gives
`Λ ≤ σ^{20} x^{1-τ/2}` on `S(C)` ((4.7)). -/
private lemma strong_step_det {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hN : 3 ≤ N)
    (hH : H.IsHermitian) {C Cm Cs C1 q s σ τ : ℝ} {γ : ℂ → ℝ}
    (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hCs : 0 < Cs) (hdich : WeakDich 1 (Cm ^ 4) 18 C1)
    (h45 : ∀ z ∈ specDomain N C,
      ‖(1 - msc z ^ 2) / msc z ^ 3 * (stieltjesM H z - msc z) - (stieltjesM H z - msc z) ^ 2‖ ≤
        2 * Cm ^ 3 * Cs / Real.log N * ‖stieltjesM H z - msc z‖ ^ 2 +
          Cm ^ 8 * (40 + 40 * Cs) * (s ^ 14 / q ^ 2 + s ^ 14 / (N * z.im) ^ 2 +
            s ^ 18 * (‖(1 - msc z ^ 2) / msc z ^ 3‖ + γ z) / (N * z.im)))
    (hγ : ∀ z ∈ specDomain N C, γ z ≤ σ ^ 20 * strongX N q z ^ (1 - τ))
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hq : 0 < q)
    (hX1 : ∀ z ∈ specDomain N C, strongX N q z ≤ 1)
    (hs1 : 1 ≤ s) (hsσ : s ≤ σ) (hδ : 2 * Cm ^ 3 * Cs / Real.log N ≤ 1 / 2)
    (hlg : 0 < Real.log N)
    (hσ : max 18 C1 * (Cm ^ 8 * (40 + 40 * Cs)) ≤ σ)
    (hΛtop : ∀ z ∈ specDomain N C, lamAvg H z ≤ σ⁻¹) :
    ∀ z ∈ specDomain N C, lamAvg H z ≤ σ ^ 20 * strongX N q z ^ (1 - τ / 2) := by
  have hCm0 : 0 < Cm := by linarith
  set Cst : ℝ := Cm ^ 8 * (40 + 40 * Cs) with hCst
  have hC8 : 1 ≤ Cm ^ 8 := one_le_pow₀ hCm
  have hCst2 : 2 ≤ Cst := by nlinarith only [hC8, hCs]
  have hσ1 : 1 ≤ σ := by
    have : 18 * Cst ≤ max 18 C1 * Cst := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith
  have hσ0 : 0 < σ := by linarith
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hXpos : ∀ z ∈ specDomain N C, 0 < strongX N q z := by
    intro z hz
    obtain ⟨-, hzi, -, -⟩ := sc_specDomain hN hz
    unfold strongX
    positivity
  set β : ℂ → ℝ := fun z => Cst * σ ^ 19 * strongX N q z ^ (1 - τ / 2) with hβ
  have hβpos : ∀ z ∈ specDomain N C, 0 < β z := by
    intro z hz
    have := (strong_rpow_facts (hXpos z hz) (hX1 z hz) hτ0).2.2.2
    simp only [hβ]
    have : 0 < Cst := by linarith
    positivity
  -- (4.5) in the form of the dichotomy
  have hdin : ∀ z ∈ specDomain N C,
      ‖(1 - msc z ^ 2) / msc z ^ 3 * (stieltjesM H z - msc z) - (stieltjesM H z - msc z) ^ 2‖ ≤
        (2 * Cm ^ 3 * Cs / Real.log N) * ‖stieltjesM H z - msc z‖ ^ 2 +
          1 * (β z * ‖stieltjesM H z - msc z‖ + ‖(1 - msc z ^ 2) / msc z ^ 3‖ * β z + β z ^ 2) := by
    intro z hz
    obtain ⟨-, hzi, -, -⟩ := sc_specDomain hN hz
    have hX0 := hXpos z hz
    obtain ⟨f1, f2, f3, f4⟩ := strong_rpow_facts hX0 (hX1 z hz) hτ0
    set X := strongX N q z with hX
    set Y := X ^ (1 - τ / 2) with hY
    set W := ‖(1 - msc z ^ 2) / msc z ^ 3‖ with hW
    have hW0 : 0 ≤ W := norm_nonneg _
    have hn0 : 0 < (N : ℝ) * z.im := by positivity
    have hq1X : 1 / q ≤ X := by
      rw [hX, strongX]; have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
      linarith
    have hn1X : 1 / ((N : ℝ) * z.im) ≤ X := by
      rw [hX, strongX]; have : 0 < 1 / q := by positivity
      linarith
    have hsq : s ^ 14 / q ^ 2 + s ^ 14 / (N * z.im) ^ 2 ≤ σ ^ 38 * Y ^ 2 := by
      have h1 : s ^ 14 ≤ σ ^ 38 := by
        calc s ^ 14 ≤ σ ^ 14 := pow_le_pow_left₀ (by linarith) hsσ 14
          _ ≤ σ ^ 38 := pow_le_pow_right₀ hσ1 (by norm_num)
      have h2 : 1 / q ^ 2 + 1 / ((N : ℝ) * z.im) ^ 2 ≤ X ^ 2 := by
        have e1 : 1 / q ^ 2 = (1 / q) ^ 2 := by ring
        have e2 : 1 / ((N : ℝ) * z.im) ^ 2 = (1 / ((N : ℝ) * z.im)) ^ 2 := by ring
        have e3 : X = 1 / q + 1 / ((N : ℝ) * z.im) := rfl
        rw [e1, e2, e3]
        have : 0 < 1 / q := by positivity
        have : 0 < 1 / ((N : ℝ) * z.im) := by positivity
        nlinarith
      have e : s ^ 14 / q ^ 2 + s ^ 14 / (N * z.im) ^ 2 =
          s ^ 14 * (1 / q ^ 2 + 1 / ((N : ℝ) * z.im) ^ 2) := by ring
      rw [e]
      exact mul_le_mul h1 (h2.trans f2) (by positivity) (by positivity)
    have hγz : s ^ 18 * γ z / (N * z.im) ≤ σ ^ 38 * Y ^ 2 := by
      have h1 : s ^ 18 ≤ σ ^ 18 := pow_le_pow_left₀ (by linarith) hsσ 18
      have h2 : γ z / (N * z.im) ≤ σ ^ 20 * X ^ (1 - τ) * X := by
        calc γ z / (N * z.im) = γ z * (1 / (N * z.im)) := by ring
          _ ≤ σ ^ 20 * X ^ (1 - τ) * X := by
            apply mul_le_mul (hγ z hz) hn1X (by positivity)
            have : 0 < X ^ (1 - τ) := Real.rpow_pos_of_pos hX0 _
            positivity
      have e : σ ^ 20 * X ^ (1 - τ) * X = σ ^ 20 * Y ^ 2 := by rw [mul_assoc, f1]
      have hγ0 : 0 ≤ γ z / (N * z.im) ∨ γ z / (N * z.im) < 0 := le_or_gt _ _
      rcases hγ0 with hγ0 | hγ0
      · calc s ^ 18 * γ z / (N * z.im) = s ^ 18 * (γ z / (N * z.im)) := by ring
          _ ≤ σ ^ 18 * (σ ^ 20 * Y ^ 2) := mul_le_mul h1 (h2.trans e.le) hγ0 (by positivity)
          _ = σ ^ 38 * Y ^ 2 := by ring
      · have : s ^ 18 * γ z / (N * z.im) = s ^ 18 * (γ z / (N * z.im)) := by ring
        rw [this]
        have : s ^ 18 * (γ z / (N * z.im)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hγ0.le
        have : 0 ≤ σ ^ 38 * Y ^ 2 := by positivity
        linarith
    have hWz : s ^ 18 * W / (N * z.im) ≤ σ ^ 19 * Y * W := by
      have h1 : s ^ 18 ≤ σ ^ 19 := by
        calc s ^ 18 ≤ σ ^ 18 := pow_le_pow_left₀ (by linarith) hsσ 18
          _ ≤ σ ^ 19 := pow_le_pow_right₀ hσ1 (by norm_num)
      calc s ^ 18 * W / (N * z.im) = s ^ 18 * (1 / (N * z.im)) * W := by ring
        _ ≤ σ ^ 19 * Y * W := by
          apply mul_le_mul_of_nonneg_right _ hW0
          exact mul_le_mul h1 (hn1X.trans f3) (by positivity) (by positivity)
    have hR : Cst * (s ^ 14 / q ^ 2 + s ^ 14 / (N * z.im) ^ 2 +
        s ^ 18 * (W + γ z) / (N * z.im)) ≤ β z ^ 2 + W * β z := by
      have e : s ^ 18 * (W + γ z) / (N * z.im) =
          s ^ 18 * W / (N * z.im) + s ^ 18 * γ z / (N * z.im) := by ring
      rw [e]
      have hb : β z = Cst * σ ^ 19 * Y := rfl
      rw [hb]
      have hC0 : 0 ≤ Cst := by linarith
      have k1 : Cst * (σ ^ 38 * Y ^ 2 + σ ^ 38 * Y ^ 2) ≤ (Cst * σ ^ 19 * Y) ^ 2 := by
        have e2 : (Cst * σ ^ 19 * Y) ^ 2 = Cst * Cst * (σ ^ 38 * Y ^ 2) := by ring
        rw [e2]
        have : 0 ≤ σ ^ 38 * Y ^ 2 := by positivity
        nlinarith only [mul_le_mul_of_nonneg_right hCst2 (mul_nonneg hC0 this)]
      have k2 : Cst * (σ ^ 19 * Y * W) = W * (Cst * σ ^ 19 * Y) := by ring
      have k3 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hsq hWz) hγz) hC0
      nlinarith only [k1, k2, k3]
    have hb0 : 0 ≤ β z * ‖stieltjesM H z - msc z‖ := mul_nonneg (hβpos z hz).le (norm_nonneg _)
    have := h45 z hz
    linarith
  -- the continuity argument
  have hmsc' : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
      (Cm⁻¹ ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ Cm) ∧
      (Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ ‖1 - msc z ^ 2‖ ∧
        ‖1 - msc z ^ 2‖ ≤ Cm * Real.sqrt (kappa z.re + z.im)) := fun z h1 h2 h3 =>
    ⟨(hmsc z h1 h2 h3).1, (hmsc z h1 h2 h3).2.1⟩
  have hδ0 : 0 ≤ 2 * Cm ^ 3 * Cs / Real.log N := by positivity
  have hβanti : ∀ z ∈ specDomain N C, ∀ y : ℝ, z.im ≤ y → y ≤ 10 → β ⟨z.re, y⟩ ≤ β z := by
    intro z hz y hy1 hy2
    obtain ⟨-, hzi, -, -⟩ := sc_specDomain hN hz
    have hy0 : 0 < y := lt_of_lt_of_le hzi hy1
    have hXle : strongX N q ⟨z.re, y⟩ ≤ strongX N q z := by
      unfold strongX
      simp only
      have : 1 / ((N : ℝ) * y) ≤ 1 / (N * z.im) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity)
          (mul_le_mul_of_nonneg_left hy1 hN0.le)
      linarith
    have hX0 : 0 < strongX N q ⟨z.re, y⟩ := by unfold strongX; simp only; positivity
    simp only [hβ]
    have hC0 : 0 < Cst := by linarith
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow hX0.le hXle (by linarith)
  have htop : ∀ E : ℝ, (⟨E, 10⟩ : ℂ) ∈ specDomain N C → ‖stieltjesM H ⟨E, 10⟩ - msc ⟨E, 10⟩‖ <
      ‖(1 - msc ⟨E, 10⟩ ^ 2) / msc ⟨E, 10⟩ ^ 3‖ / 18 := by
    intro E hE
    obtain ⟨hEre, h10, -, -⟩ := sc_specDomain hN hE
    obtain ⟨⟨m1, m2⟩, ⟨m3, m4⟩, -⟩ := hmsc _ hEre h10 le_rfl
    obtain ⟨w1, -⟩ := weak_w_bounds hCm m1 m2 m3 m4
    simp only at w1
    have hK : 0 < Cm ^ 4 := by positivity
    have hs3 : 3 ≤ Real.sqrt (kappa E + 10) := by
      have : 0 ≤ kappa E := abs_nonneg _
      rw [show (3 : ℝ) = Real.sqrt (3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hW3 : 3 / Cm ^ 4 ≤ ‖(1 - msc ⟨E, 10⟩ ^ 2) / msc ⟨E, 10⟩ ^ 3‖ := by
      calc 3 / Cm ^ 4 = (Cm ^ 4)⁻¹ * 3 := by ring
        _ ≤ (Cm ^ 4)⁻¹ * Real.sqrt (kappa E + 10) :=
            mul_le_mul_of_nonneg_left hs3 (by positivity)
        _ ≤ _ := w1
    have hΛ := hΛtop _ hE
    unfold lamAvg at hΛ
    have hσbig : 6 * Cm ^ 4 < σ := by
      have h1 : 18 * Cst ≤ max 18 C1 * Cst :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      have h2 : Cm ^ 4 ≤ Cm ^ 8 := pow_le_pow_right₀ hCm (by norm_num)
      have h3 : 40 * Cm ^ 8 ≤ Cst := by
        rw [hCst]; nlinarith only [hC8, hCs]
      linarith
    have : σ⁻¹ < 3 / Cm ^ 4 / 18 := by
      rw [inv_lt_comm₀ hσ0 (by positivity)]
      rw [show (3 / Cm ^ 4 / 18)⁻¹ = 6 * Cm ^ 4 by field_simp; ring]
      exact hσbig
    calc ‖stieltjesM H ⟨E, 10⟩ - msc ⟨E, 10⟩‖ ≤ σ⁻¹ := hΛ
      _ < 3 / Cm ^ 4 / 18 := this
      _ ≤ _ := by gcongr
  have hmain := strong_cont_dich hN hH hCm (by norm_num : (0 : ℝ) < 18) hmsc' hdich hδ0 hδ
    hdin hβpos hβanti htop
  intro z hz
  have h1 := hmain z hz
  unfold lamAvg
  have hY := (strong_rpow_facts (hXpos z hz) (hX1 z hz) hτ0).2.2.2
  calc ‖stieltjesM H z - msc z‖ ≤ max 18 C1 * β z := h1
    _ = (max 18 C1 * Cst) * σ ^ 19 * strongX N q z ^ (1 - τ / 2) := by simp only [hβ]; ring
    _ ≤ σ * σ ^ 19 * strongX N q z ^ (1 - τ / 2) := by gcongr
    _ = σ ^ 20 * strongX N q z ^ (1 - τ / 2) := by ring

/-! ### The last step: (4.24)–(4.28) of [15] -/

/-- (4.24)–(4.28) of [15] at one point: from `Λ ≤ γ ≤ 2 σ^{20} (1/q + 1/n)` ((4.24)) and (4.5),
`Λ ≤ P (min(q⁻² t⁻¹, q⁻¹) + n⁻¹)` with `t = √(κ + η)`, `n = Nη`, `w = (1 - m_sc²)/m_sc³`,
`v = m - m_sc`. -/
private lemma strong_final_arith {Cm Cst δ s σ q n t γ P : ℝ} {w v : ℂ}
    (hCm : 1 ≤ Cm) (hCst : 1 ≤ Cst) (hδ : δ ≤ 1 / 2) (hs1 : 1 ≤ s)
    (hsσ : s ≤ σ) (hq : 0 < q) (hn : 0 < n) (ht : 0 < t)
    (hw : (Cm ^ 4)⁻¹ * t ≤ ‖w‖) (hvγ : ‖v‖ ≤ γ) (hγ : γ ≤ 2 * σ ^ 20 * (1 / q + 1 / n))
    (h45 : ‖w * v - v ^ 2‖ ≤ δ * ‖v‖ ^ 2 +
      Cst * (s ^ 14 / q ^ 2 + s ^ 14 / n ^ 2 + s ^ 18 * (‖w‖ + γ) / n))
    (hP : 64 * Cm ^ 4 * Cst * σ ^ 40 ≤ P) :
    ‖v‖ ≤ P * (min (1 / (q ^ 2 * t)) (1 / q) + 1 / n) := by
  have hσ1 : 1 ≤ σ := hs1.trans hsσ
  have hK : 1 ≤ Cm ^ 4 := one_le_pow₀ hCm
  have hK0 : 0 < Cm ^ 4 := by linarith
  have hσ20 : 1 ≤ σ ^ 20 := one_le_pow₀ hσ1
  have hσ40 : σ ^ 20 ≤ σ ^ 40 := pow_le_pow_right₀ hσ1 (by norm_num)
  have hΛ0 : 0 ≤ ‖v‖ := norm_nonneg _
  set Λ := ‖v‖ with hΛ
  set W := ‖w‖ with hW
  have hiq : 0 < 1 / q := by positivity
  have hin : 0 < 1 / n := by positivity
  have hP2 : 4 * σ ^ 20 ≤ P := by
    have h1 : 4 * σ ^ 20 ≤ 64 * Cm ^ 4 * Cst * σ ^ 40 := by
      have : 1 ≤ Cm ^ 4 * Cst := one_le_mul_of_one_le_of_one_le hK hCst
      nlinarith only [this, hσ40, hσ20]
    linarith
  have hP0 : 0 ≤ P := by linarith
  -- the bound with `1/q`
  have hb : Λ ≤ P * (1 / q + 1 / n) := by
    have : 2 * σ ^ 20 * (1 / q + 1 / n) ≤ P * (1 / q + 1 / n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have ha : Λ ≤ P * (1 / (q ^ 2 * t) + 1 / n) := by
    have hqt : 0 < 1 / (q ^ 2 * t) := by positivity
    rcases le_or_gt (1 / q) (1 / n) with hA | hA
    · -- `1/q ≤ 1/(Nη)`
      have : Λ ≤ 4 * σ ^ 20 * (1 / n) := by nlinarith only [hvγ, hγ, hA, hσ20]
      have h2 : 4 * σ ^ 20 * (1 / n) ≤ P * (1 / n) := mul_le_mul_of_nonneg_right hP2 hin.le
      nlinarith only [this, h2, hqt, hP0]
    rcases le_or_gt t (16 * Cm ^ 4 * σ ^ 20 / q) with hB | hB
    · -- `t ≤ X₂/q`
      have h1 : Λ ≤ 4 * σ ^ 20 * (1 / q) := by nlinarith only [hvγ, hγ, hA, hσ20]
      have h2 : 1 / q ≤ 16 * Cm ^ 4 * σ ^ 20 * (1 / (q ^ 2 * t)) := by
        rw [le_div_iff₀ hq] at hB
        have e : 1 / q = (t * q) * (1 / (q ^ 2 * t)) := by field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_right hB hqt.le
      have h3 : 4 * σ ^ 20 * (16 * Cm ^ 4 * σ ^ 20) ≤ P := by
        have e : 4 * σ ^ 20 * (16 * Cm ^ 4 * σ ^ 20) = 64 * Cm ^ 4 * σ ^ 40 * 1 := by ring
        have h := mul_le_mul_of_nonneg_left hCst (by positivity : (0 : ℝ) ≤ 64 * Cm ^ 4 * σ ^ 40)
        have e2 : 64 * Cm ^ 4 * σ ^ 40 * Cst = 64 * Cm ^ 4 * Cst * σ ^ 40 := by ring
        linarith
      calc Λ ≤ 4 * σ ^ 20 * (1 / q) := h1
        _ ≤ 4 * σ ^ 20 * (16 * Cm ^ 4 * σ ^ 20 * (1 / (q ^ 2 * t))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (4 * σ ^ 20 * (16 * Cm ^ 4 * σ ^ 20)) * (1 / (q ^ 2 * t)) := by ring
        _ ≤ P * (1 / (q ^ 2 * t)) := mul_le_mul_of_nonneg_right h3 hqt.le
        _ ≤ P * (1 / (q ^ 2 * t) + 1 / n) := by nlinarith only [hP0, hin]
    · -- the stable case: `Λ ≤ |w|/4`
      have hγq : γ ≤ 4 * σ ^ 20 * (1 / q) := by nlinarith only [hγ, hA, hσ20]
      have hW4 : 4 * γ ≤ W := by
        have h1 : 16 * σ ^ 20 * (1 / q) < (Cm ^ 4)⁻¹ * t := by
          rw [div_lt_iff₀ hq] at hB
          rw [lt_inv_mul_iff₀ hK0]
          have e : Cm ^ 4 * (16 * σ ^ 20 * (1 / q)) = 16 * Cm ^ 4 * σ ^ 20 / q := by ring
          rw [e, div_lt_iff₀ hq]
          linarith
        linarith
      have hΛW : Λ ≤ W / 4 := by linarith
      have hW0 : 0 < W := by
        have : 0 < (Cm ^ 4)⁻¹ * t := by positivity
        linarith
      have hlow : W * Λ ≤ ‖w * v - v ^ 2‖ + Λ ^ 2 := by
        have h1 := norm_sub_norm_le (w * v) (v ^ 2)
        rw [norm_mul, norm_pow] at h1
        have h2 : ‖w * v‖ - ‖v ^ 2‖ ≤ ‖w * v - v ^ 2‖ := norm_sub_norm_le _ _
        rw [norm_mul, norm_pow] at h2
        linarith
      set R := Cst * (s ^ 14 / q ^ 2 + s ^ 14 / n ^ 2 + s ^ 18 * (W + γ) / n) with hR
      have hkey : 5 / 8 * W * Λ ≤ R := by
        have h1 : W * Λ ≤ δ * Λ ^ 2 + R + Λ ^ 2 := by linarith
        have h2 : (δ + 1) * Λ ^ 2 ≤ 3 / 2 * (W / 4) * Λ := by
          have : Λ ^ 2 ≤ W / 4 * Λ := by nlinarith only [hΛW, hΛ0]
          nlinarith only [this, hδ, hΛ0, hW0]
        nlinarith only [h1, h2]
      have hn2 : s ^ 14 / n ^ 2 ≤ s ^ 14 / q ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have : q < n := by
          rw [div_lt_div_iff₀ hn hq] at hA; linarith
        nlinarith only [this, hq]
      have hRb : R ≤ Cst * (2 * s ^ 14 / q ^ 2 + 5 / 4 * s ^ 18 * W / n) := by
        rw [hR]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have : s ^ 18 * (W + γ) / n ≤ 5 / 4 * s ^ 18 * W / n := by
          rw [div_le_div_iff_of_pos_right hn]
          have : 0 ≤ s ^ 18 := by positivity
          nlinarith only [this, hW4]
        have e : 2 * s ^ 14 / q ^ 2 = s ^ 14 / q ^ 2 + s ^ 14 / q ^ 2 := by ring
        linarith
      have hΛb : Λ ≤ 16 / 5 * Cst * s ^ 14 / (q ^ 2 * W) + 2 * Cst * s ^ 18 / n := by
        have h1 : 5 / 8 * W * Λ ≤ Cst * (2 * s ^ 14 / q ^ 2 + 5 / 4 * s ^ 18 * W / n) :=
          hkey.trans hRb
        have e : 16 / 5 * Cst * s ^ 14 / (q ^ 2 * W) + 2 * Cst * s ^ 18 / n =
            Cst * (2 * s ^ 14 / q ^ 2 + 5 / 4 * s ^ 18 * W / n) / (5 / 8 * W) := by
          field_simp
          ring
        rw [e, le_div_iff₀ (by positivity)]
        linarith
      have hWt : 1 / (q ^ 2 * W) ≤ Cm ^ 4 * (1 / (q ^ 2 * t)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : t ≤ Cm ^ 4 * W := by
          have := mul_le_mul_of_nonneg_left hw hK0.le
          rwa [← mul_assoc, mul_inv_cancel₀ hK0.ne', one_mul] at this
        nlinarith only [this, hq, sq_nonneg q, mul_pos hq hq]
      have hs14 : s ^ 14 ≤ σ ^ 40 := (pow_le_pow_left₀ (by linarith) hsσ 14).trans
        (pow_le_pow_right₀ hσ1 (by norm_num))
      have hs18 : s ^ 18 ≤ σ ^ 40 := (pow_le_pow_left₀ (by linarith) hsσ 18).trans
        (pow_le_pow_right₀ hσ1 (by norm_num))
      have t1 : 16 / 5 * Cst * s ^ 14 / (q ^ 2 * W) ≤ P * (1 / (q ^ 2 * t)) := by
        have e : 16 / 5 * Cst * s ^ 14 / (q ^ 2 * W) =
            16 / 5 * Cst * s ^ 14 * (1 / (q ^ 2 * W)) := by
          ring
        rw [e]
        calc 16 / 5 * Cst * s ^ 14 * (1 / (q ^ 2 * W)) ≤
              16 / 5 * Cst * s ^ 14 * (Cm ^ 4 * (1 / (q ^ 2 * t))) :=
              mul_le_mul_of_nonneg_left hWt (by positivity)
          _ = (16 / 5 * Cst * s ^ 14 * Cm ^ 4) * (1 / (q ^ 2 * t)) := by ring
          _ ≤ P * (1 / (q ^ 2 * t)) := by
              apply mul_le_mul_of_nonneg_right _ hqt.le
              have : 0 ≤ Cst * Cm ^ 4 := by positivity
              nlinarith only [hs14, this, hP,
                mul_nonneg this (pow_nonneg (by linarith : (0 : ℝ) ≤ σ) 40)]
      have t2 : 2 * Cst * s ^ 18 / n ≤ P * (1 / n) := by
        rw [mul_one_div, div_le_div_iff_of_pos_right hn]
        have : 0 ≤ Cst := by linarith
        nlinarith only [hs18, this, hP, hK,
          mul_nonneg this (pow_nonneg (by linarith : (0 : ℝ) ≤ σ) 40)]
      have : P * (1 / (q ^ 2 * t) + 1 / n) = P * (1 / (q ^ 2 * t)) + P * (1 / n) := by ring
      linarith
  rw [← min_add_add_right]
  calc Λ ≤ min (P * (1 / (q ^ 2 * t) + 1 / n)) (P * (1 / q + 1 / n)) := le_min ha hb
    _ = P * min (1 / (q ^ 2 * t) + 1 / n) (1 / q + 1 / n) := (mul_min_of_nonneg _ _ hP0).symm

/-! ### The entries: (2.17) of [15] from (2.16), (3.32) and (3.36) -/

private lemma strong_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
  nlinarith only [h1, h2, h3]

/-- (2.17) of [15] at `z` from (3.32), (3.36) and (2.16) at a nearby point `p`: `g = G_ij(z) - δ_ij
m_sc(z)`, `g' = G_ij(p) - δ_ij m_sc(p)`, `Ψ_p` of (3.26), `Λ_p = Λ(p)`, `I = Im m_sc`, `n = Nη`;
`A₁ = φ^ζ`, `A₂ = φ^{2ζ}`. -/
private lemma strong_entry_arith {Co Cd A1 A2 Pa Pe q nz np ε Λp Ip Iz Ψp : ℝ} {g g' : ℂ}
    (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hPa : 1 ≤ Pa) (hq : 1 ≤ q)
    (hnz : 1 ≤ nz) (hnp : nz ≤ 2 * np) (hε : ε ≤ 1 / q ^ 2) (hΛp0 : 0 ≤ Λp)
    (hΛp : Λp ≤ Pa * (1 / q + 1 / np)) (hIp0 : 0 ≤ Ip) (hIz0 : 0 ≤ Iz) (hIp : Ip ≤ Iz + ε)
    (hΨ : Ψp = Real.sqrt ((Λp + Ip) / np))
    (hg' : ‖g'‖ ≤ Co * (1 / q + A2 * Ψp) + Cd * (A1 / q + A2 * Ψp) + Λp)
    (hg : ‖g - g'‖ ≤ 2 * ε)
    (hPe : Co + Cd * A1 + (Co + Cd) * A2 * (4 * Pa + 2) + 2 * Pa + 2 ≤ Pe) :
    ‖g‖ ≤ Pe * (1 / q + Real.sqrt (Iz / nz) + 1 / nz) := by
  have hq0 : 0 < q := by linarith
  have hnz0 : 0 < nz := by linarith
  have hnp0 : 0 < np := by linarith
  set u := 1 / q with hu
  set r := Real.sqrt (Iz / nz) with hr
  set w := 1 / nz with hw
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one hq0]; exact hq
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 := by rw [hw, div_le_one hnz0]; exact hnz
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hεu : ε ≤ u ^ 2 := by rw [hu, div_pow, one_pow]; exact hε
  have hε0 : 0 ≤ ε := by linarith [(norm_nonneg _).trans hg]
  have hnpw : 1 / np ≤ 2 * w := by
    rw [hw, div_le_iff₀ hnp0]
    have : 2 * (1 / nz) * np = 2 * np / nz := by ring
    rw [this, le_div_iff₀ hnz0]
    linarith
  have hΛp' : Λp ≤ Pa * (u + 2 * w) := by
    refine hΛp.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    linarith
  -- `Ψ_p`
  have hΨ1 : Real.sqrt (Λp / np) ≤ 2 * Pa * (u + 2 * w) := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : Λp / np ≤ Pa * (u + 2 * w) * (2 * w) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hΛp' hnpw (by positivity) (by positivity)
    have h2 : Pa * (u + 2 * w) * (2 * w) ≤ (2 * Pa * (u + 2 * w)) ^ 2 := by
      have h0 : 0 ≤ Pa * (u + 2 * w) := by positivity
      have k : 2 * w ≤ 4 * (Pa * (u + 2 * w)) := by nlinarith only [hPa, hu0, hw0]
      have k2 := mul_le_mul_of_nonneg_left k h0
      have e : (2 * Pa * (u + 2 * w)) ^ 2 = Pa * (u + 2 * w) * (4 * (Pa * (u + 2 * w))) := by
        ring
      rw [e]; exact k2
    linarith
  have hΨ2 : Real.sqrt (Ip / np) ≤ 2 * r + 2 * u := by
    have h1 : Ip / np ≤ 2 * (Iz / nz) + 2 * u ^ 2 := by
      have k1 : Ip / np ≤ (Iz + ε) * (2 * w) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul hIp hnpw (by positivity) (by positivity)
      have k2 : (Iz + ε) * (2 * w) = 2 * (Iz / nz) + 2 * ε * w := by rw [hw]; ring
      have k3 : 2 * ε * w ≤ 2 * u ^ 2 := by nlinarith only [hεu, hw1, hε0, hw0]
      linarith
    calc Real.sqrt (Ip / np) ≤ Real.sqrt (2 * (Iz / nz) + 2 * u ^ 2) := Real.sqrt_le_sqrt h1
      _ ≤ Real.sqrt (2 * (Iz / nz)) + Real.sqrt (2 * u ^ 2) :=
          strong_sqrt_add_le (by positivity) (by positivity)
      _ ≤ 2 * r + 2 * u := by
          have e1 : Real.sqrt (2 * (Iz / nz)) = Real.sqrt 2 * r := by
            rw [hr, Real.sqrt_mul (by norm_num)]
          have e2 : Real.sqrt (2 * u ^ 2) = Real.sqrt 2 * u := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hu0.le]
          have h2 : Real.sqrt 2 ≤ 2 := by
            rw [Real.sqrt_le_left (by norm_num)]; norm_num
          rw [e1, e2]
          nlinarith only [h2, hr0, hu0]
  have hΨb : Ψp ≤ 2 * Pa * (u + 2 * w) + 2 * r + 2 * u := by
    rw [hΨ]
    have e : (Λp + Ip) / np = Λp / np + Ip / np := by ring
    rw [e]
    refine (strong_sqrt_add_le (by positivity) (by positivity)).trans ?_
    linarith
  -- the sum
  have hΨ0 : 0 ≤ Ψp := by rw [hΨ]; exact Real.sqrt_nonneg _
  set K := Co + Cd * A1 + (Co + Cd) * A2 * (4 * Pa + 2) + 2 * Pa + 2 with hK
  have hgb : ‖g‖ ≤ ‖g'‖ + 2 * u := by
    have h1 := norm_le_norm_add_norm_sub' g g'
    have h2 : 2 * ε ≤ 2 * u := by nlinarith only [hεu, hu1, hu0]
    have h3 : ‖g - g'‖ = ‖g' - g‖ := norm_sub_rev _ _
    linarith [norm_sub_norm_le g g']
  have hT : Co * (u + A2 * Ψp) + Cd * (A1 * u + A2 * Ψp) + Λp + 2 * u ≤ K * (u + r + w) := by
    have h1 : (Co + Cd) * A2 * Ψp ≤ (Co + Cd) * A2 * (2 * Pa * (u + 2 * w) + 2 * r + 2 * u) :=
      mul_le_mul_of_nonneg_left hΨb (by positivity)
    have e : Co * (u + A2 * Ψp) + Cd * (A1 * u + A2 * Ψp) =
        Co * u + Cd * A1 * u + (Co + Cd) * A2 * Ψp := by ring
    have hB : 0 ≤ (Co + Cd) * A2 := by positivity
    have h2 : Co * u + Cd * A1 * u + (Co + Cd) * A2 * (2 * Pa * (u + 2 * w) + 2 * r + 2 * u) +
        Pa * (u + 2 * w) + 2 * u ≤ K * (u + r + w) := by
      rw [hK]
      have c1 : 0 ≤ (Co + Cd) * A2 * Pa * u := by positivity
      have c2 : 0 ≤ (Co + Cd) * A2 * Pa * r := by positivity
      have c3 : 0 ≤ (Co + Cd) * A2 * w := by positivity
      have c4 : 0 ≤ (Co + Cd) * A2 * u := by positivity
      have c5 : 0 ≤ Co * r := by positivity
      have c6 : 0 ≤ Co * w := by positivity
      have c7 : 0 ≤ Cd * A1 * r := by positivity
      have c8 : 0 ≤ Cd * A1 * w := by positivity
      have c9 : 0 ≤ Pa * r := by positivity
      have c10 : 0 ≤ Pa * u := by positivity
      have c11 : 0 ≤ (Co + Cd) * A2 * Pa * w := by positivity
      nlinarith only [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, hr0, hw0, hu0]
    have h3 : Λp ≤ Pa * (u + 2 * w) := hΛp'
    linarith
  have hg'' : ‖g'‖ ≤ Co * (u + A2 * Ψp) + Cd * (A1 * u + A2 * Ψp) + Λp := by
    have : A1 / q = A1 * u := by rw [hu]; ring
    rw [← this]; exact hg'
  have hK0 : K * (u + r + w) ≤ Pe * (u + r + w) :=
    mul_le_mul_of_nonneg_right hPe (by positivity)
  linarith

/-! ### Parameter arithmetic -/

/-- On `S(C)` with `φ^C ≤ q`: `0 < 1/q ≤ x ≤ 2/φ^C`. -/
private lemma strong_X_bounds {N : ℕ} (hN : 3 ≤ N) {C q : ℝ} (hC : 0 < phi N ^ C)
    (hq : phi N ^ C ≤ q) {z : ℂ} (hz : z ∈ specDomain N C) :
    0 < strongX N q z ∧ 1 / q ≤ strongX N q z ∧ strongX N q z ≤ 2 / phi N ^ C := by
  obtain ⟨-, hzl, -⟩ := hz
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hq0 : 0 < q := lt_of_lt_of_le hC hq
  have hn : phi N ^ C < N * z.im := by
    rw [div_lt_iff₀ hN0] at hzl; linarith [mul_comm (N : ℝ) z.im]
  have hn0 : 0 < (N : ℝ) * z.im := lt_trans hC hn
  unfold strongX
  have hn1 : 0 < 1 / ((N : ℝ) * z.im) := by positivity
  refine ⟨by positivity, by linarith, ?_⟩
  have h1 : 1 / q ≤ 1 / phi N ^ C := div_le_div_of_nonneg_left zero_le_one hC hq
  have h2 : 1 / ((N : ℝ) * z.im) ≤ 1 / phi N ^ C := div_le_div_of_nonneg_left zero_le_one hC hn.le
  have e : 2 / phi N ^ C = 1 / phi N ^ C + 1 / phi N ^ C := by ring
  linarith

/-- Between neighbouring points with `η_z ≤ 2 η_p`: `x(p)^{1-τ} ≤ 2 x(z)^{1-τ}`. -/
private lemma strong_X_near {N : ℕ} {q τ : ℝ} {z p : ℂ} (hq : 0 < q) (hN : (0 : ℝ) < N)
    (hzi : 0 < z.im) (hpi : 0 < p.im) (hzp : z.im ≤ 2 * p.im) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    strongX N q p ^ (1 - τ) ≤ 2 * strongX N q z ^ (1 - τ) := by
  have hXz : 0 < strongX N q z := by unfold strongX; positivity
  have hXp : 0 < strongX N q p := by unfold strongX; positivity
  have h1 : strongX N q p ≤ 2 * strongX N q z := by
    unfold strongX
    have : 1 / ((N : ℝ) * p.im) ≤ 2 * (1 / (N * z.im)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hzp, hN, hzi, hpi]
    have : 0 < 1 / q := by positivity
    linarith
  calc strongX N q p ^ (1 - τ) ≤ (2 * strongX N q z) ^ (1 - τ) :=
        Real.rpow_le_rpow hXp.le h1 (by linarith)
    _ = (2 : ℝ) ^ (1 - τ) * strongX N q z ^ (1 - τ) := Real.mul_rpow (by norm_num) hXz.le
    _ ≤ 2 * strongX N q z ^ (1 - τ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXz.le _)
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : 1 - τ ≤ 1)
        rwa [Real.rpow_one] at this

/-- (4.6) and the condition `γ ≤ s⁻¹` of Lemma 4.1 of [15]: `σ^{20} x^{1-τ} ≤ σ⁻¹` once
`x ≤ σ^{-63}` and `τ ≤ 2/3`. -/
private lemma strong_gamma_small {X σ τ : ℝ} (hX0 : 0 < X) (hσ1 : 1 ≤ σ) (hX : X ≤ (σ ^ 63)⁻¹)
    (hτ : τ ≤ 2 / 3) : σ ^ 20 * X ^ (1 - τ) ≤ σ⁻¹ := by
  have hσ0 : 0 < σ := by linarith
  have hX1 : X ≤ 1 := hX.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hσ1))
  have h1 : X ^ (1 - τ) ≤ X ^ ((3 : ℕ)⁻¹ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hX0 hX1 (by norm_num; linarith)
  have h2 : X ^ ((3 : ℕ)⁻¹ : ℝ) ≤ (σ ^ 21)⁻¹ := by
    have e : (σ ^ 63)⁻¹ = ((σ ^ 21)⁻¹) ^ 3 := by rw [inv_pow, ← pow_mul]
    rw [e] at hX
    calc X ^ ((3 : ℕ)⁻¹ : ℝ) ≤ (((σ ^ 21)⁻¹) ^ 3) ^ ((3 : ℕ)⁻¹ : ℝ) :=
          Real.rpow_le_rpow hX0.le hX (by positivity)
      _ = (σ ^ 21)⁻¹ := Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  calc σ ^ 20 * X ^ (1 - τ) ≤ σ ^ 20 * (σ ^ 21)⁻¹ :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = σ⁻¹ := by field_simp

/-- (4.24) of [15]: `x^{1-τ} ≤ 2 x` once `1/q ≤ x`, `q² ≤ N` and `τ log N ≤ 4/3`. -/
private lemma strong_gamma_last {N : ℕ} {X q τ : ℝ} (hq1 : 1 ≤ q) (hqN : q ^ 2 ≤ N)
    (hqX : 1 / q ≤ X) (hτ0 : 0 ≤ τ) (hτ : τ * Real.log N ≤ 4 / 3) :
    X ^ (1 - τ) ≤ 2 * X := by
  have hq0 : 0 < q := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hqX
  have hlogq : 2 * Real.log q ≤ Real.log N := by
    have := Real.log_le_log (by positivity) hqN
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hqτ : q ^ τ ≤ 2 := by
    rw [Real.rpow_def_of_pos hq0]
    have h1 : Real.log q * τ ≤ 2 / 3 := by
      have : 0 ≤ Real.log q := Real.log_nonneg hq1
      nlinarith only [hlogq, hτ, hτ0, this]
    have h2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    calc Real.exp (Real.log q * τ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hXτ : 1 / 2 ≤ X ^ τ := by
    have h1 : (1 / q) ^ τ ≤ X ^ τ := Real.rpow_le_rpow (by positivity) hqX hτ0
    have h2 : (1 / q) ^ τ = 1 / q ^ τ := by
      rw [Real.div_rpow zero_le_one hq0.le, Real.one_rpow]
    have h3 : 1 / 2 ≤ 1 / q ^ τ :=
      div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hq0 _) hqτ
    linarith
  rw [Real.rpow_sub hX0, Real.rpow_one, div_le_iff₀ (Real.rpow_pos_of_pos hX0 _)]
  nlinarith only [hXτ, hX0]

/-- The number `M = ⌊log₂ ⌊log N⌋⌋` of iteration steps (in the proof of Theorem 2.8 of [15],
`M = ⌊log log N / log 2⌋ - 1`): `2^M ≤ log N < 2^{M+1}`, and `(log N)^{2(M+1)} ≤ φ³` once
`log log N ≥ 40`. -/
private lemma strong_levels {N : ℕ} (hN : 3 ≤ N) (hlg : 2 ≤ Real.log N)
    (hll : 40 ≤ Real.log (Real.log N)) :
    (2 : ℝ) ^ Nat.log 2 ⌊Real.log N⌋₊ ≤ Real.log N ∧
      Real.log N < 2 * 2 ^ Nat.log 2 ⌊Real.log N⌋₊ ∧
      Real.log N ^ (2 * (Nat.log 2 ⌊Real.log N⌋₊ + 1)) ≤ phi N ^ (3 : ℕ) := by
  set lg := Real.log N with hlgd
  set M := Nat.log 2 ⌊lg⌋₊ with hM
  have hfl : ⌊lg⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊lg⌋₊ := Nat.le_floor (by norm_num; linarith)
    omega
  have h1 : (2 : ℝ) ^ M ≤ lg := by
    have h := Nat.pow_log_le_self 2 hfl
    have h' : ((2 ^ M : ℕ) : ℝ) ≤ (⌊lg⌋₊ : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'.trans (Nat.floor_le (by linarith))
  have h2 : lg < 2 * 2 ^ M := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊lg⌋₊
    have h' : ⌊lg⌋₊ + 1 ≤ 2 ^ (M + 1) := h
    have h'' : ((⌊lg⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (M + 1) : ℕ) : ℝ) := by exact_mod_cast h'
    push_cast at h''
    have := Nat.lt_floor_add_one lg
    rw [pow_succ] at h''
    linarith
  refine ⟨h1, h2, ?_⟩
  have hlg0 : 0 < lg := by linarith
  rw [phi_eq_exp hN, ← Real.exp_nat_mul]
  rw [← Real.exp_log (pow_pos hlg0 _), Real.log_pow]
  apply Real.exp_le_exp.mpr
  set ℓ := Real.log lg with hℓ
  have hM : (M : ℝ) * Real.log 2 ≤ ℓ := by
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at this
  have hl2 : (69 : ℝ) / 100 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hM' : (M : ℝ) * (69 / 100) ≤ ℓ := by
    have : (M : ℝ) * (69 / 100) ≤ (M : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg _)
    linarith
  push_cast
  nlinarith only [hM', hll]

/-! ### The iteration and the last step for one matrix -/

/-- One step of the iteration of [15] (proof of Theorem 2.8) for one matrix: (3.40) and (4.2) at
the lattice points, with `γ = σ^{20} x^{1-τ}` as a priori bound on `S(C)`, give the bound with
`τ/2`. -/
private lemma strong_iter_det {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hN : 3 ≤ N)
    (hH : H.IsHermitian) {C Cm Cs C1 q s σ τ : ℝ} {Λl : Finset ℂ}
    (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hCs : 0 < Cs) (hdich : WeakDich 1 (Cm ^ 4) 18 C1)
    (hΛlS : (↑Λl : Set ℂ) ⊆ specDomain N C)
    (hΛl : ∀ z ∈ specDomain N C, ∃ p ∈ Λl, ‖z - p‖ ≤ (N : ℝ) ^ (-(3 : ℝ)))
    (hC1 : 1 ≤ phi N ^ C) (hs1 : 1 ≤ s) (hlg : 1 ≤ Real.log N) (hlgs : Real.log N ≤ s)
    (hsσ : s ≤ σ) (hq1 : 1 ≤ q) (hεq : s ^ 18 * (1 / (N * (phi N ^ C) ^ 2)) ≤ 1 / q ^ 2)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hX1 : ∀ z ∈ specDomain N C, strongX N q z ≤ 1)
    (hγσ : ∀ z ∈ specDomain N C, σ ^ 20 * strongX N q z ^ (1 - τ) ≤ σ⁻¹)
    (hδ : 2 * Cm ^ 3 * Cs / Real.log N ≤ 1 / 2)
    (hσ : max 18 C1 * (Cm ^ 8 * (40 + 40 * Cs)) ≤ σ)
    (hΛγ : ∀ z ∈ specDomain N C, lamAvg H z ≤ σ ^ 20 * strongX N q z ^ (1 - τ))
    (hSC : ∀ p ∈ Λl, ‖(1 - msc p ^ 2) * (stieltjesM H p - msc p) -
        msc p ^ 3 * (stieltjesM H p - msc p) ^ 2 - msc p ^ 2 * zAvg H p‖ ≤
      Cs * (s ^ 2 * Real.log N / q ^ 2 + s ^ 4 * Real.log N * psiCtrl H p ^ 2 +
        lamAvg H p ^ 2 / Real.log N))
    (hFA : ∀ p ∈ Λl, ‖zAvg H p‖ ≤ s ^ 14 * (1 / q ^ 2 + 1 / (N * p.im) ^ 2 +
        s ^ 4 * ((msc p).im + σ ^ 20 * strongX N q p ^ (1 - τ)) / (N * p.im))) :
    ∀ z ∈ specDomain N C, lamAvg H z ≤ σ ^ 20 * strongX N q z ^ (1 - τ / 2) := by
  have hCst : 2 ≤ Cm ^ 8 * (40 + 40 * Cs) := by
    have : 1 ≤ Cm ^ 8 := one_le_pow₀ hCm
    nlinarith only [this, hCs]
  have hσ1 : 1 ≤ σ := by
    have : 18 * (Cm ^ 8 * (40 + 40 * Cs)) ≤ max 18 C1 * (Cm ^ 8 * (40 + 40 * Cs)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hq0 : 0 < q := by linarith
  have hγ0 : ∀ z ∈ specDomain N C, 0 ≤ σ ^ 20 * strongX N q z ^ (1 - τ) := by
    intro z hz
    obtain ⟨-, hzi, -, -⟩ := sc_specDomain hN hz
    have : 0 < strongX N q z := by unfold strongX; positivity
    have := Real.rpow_nonneg this.le (1 - τ)
    positivity
  have hγ1 : ∀ z ∈ specDomain N C, σ ^ 20 * strongX N q z ^ (1 - τ) ≤ 1 := fun z hz =>
    (hγσ z hz).trans (inv_le_one_of_one_le₀ hσ1)
  have hγp : ∀ z ∈ specDomain N C, ∀ p ∈ specDomain N C, ‖z - p‖ ≤ (N : ℝ) ^ (-(3 : ℝ)) →
      σ ^ 20 * strongX N q p ^ (1 - τ) ≤ 2 * (σ ^ 20 * strongX N q z ^ (1 - τ)) := by
    intro z hz p hp hzp
    obtain ⟨-, hzi, -, -⟩ := sc_specDomain hN hz
    obtain ⟨-, hpi, -, -⟩ := sc_specDomain hN hp
    obtain ⟨-, h2, -, -⟩ := strong_lattice_scale hN hC1 hz hp hzp
    have := strong_X_near hq0 hN0 hzi hpi h2 hτ0 hτ1
    have h20 : 0 ≤ σ ^ 20 := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left this h20]
  have h45 := strong_45_all (γ := fun z => σ ^ 20 * strongX N q z ^ (1 - τ)) hN hH hCm hmsc
    hCs hΛlS hΛl hC1 hs1 hlg hlgs hq1 hεq hγ0 hγ1 hγp hΛγ hSC hFA
  exact strong_step_det hN hH hCm hmsc hCs hdich h45 (fun z _ => le_rfl) hτ0 hτ1 hq0 hX1 hs1
    hsσ hδ (by linarith) hσ (fun z hz => (hΛγ z hz).trans (hγσ z hz))

/-- The last step of [15] (proof of Theorem 2.8, (4.24)–(4.28), and (2.17) from (2.16), (3.32),
(3.36)) for one matrix: with `γ = σ^{20} x^{1-τ} ≤ 2 σ^{20} x` as a priori bound on `S(C)`, the
events (3.2) and (3.3) hold on `S(C)`. -/
private lemma strong_final_det {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hN : 3 ≤ N)
    (hH : H.IsHermitian) {C Cm Cs Co Cd q s σ τ A1 : ℝ} {Λl : Finset ℂ}
    (hCm : 1 ≤ Cm) (hmsc : WeakMscBd Cm) (hCs : 0 < Cs) (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd)
    (hA1 : 0 ≤ A1)
    (hΛlS : (↑Λl : Set ℂ) ⊆ specDomain N C)
    (hΛl : ∀ z ∈ specDomain N C, ∃ p ∈ Λl, ‖z - p‖ ≤ (N : ℝ) ^ (-(3 : ℝ)))
    (hC1 : 1 ≤ phi N ^ C) (hs1 : 1 ≤ s) (hlg : 1 ≤ Real.log N) (hlgs : Real.log N ≤ s)
    (hsσ : s ≤ σ) (hq1 : 1 ≤ q) (hεq : s ^ 18 * (1 / (N * (phi N ^ C) ^ 2)) ≤ 1 / q ^ 2)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hγσ : ∀ z ∈ specDomain N C, σ ^ 20 * strongX N q z ^ (1 - τ) ≤ σ⁻¹)
    (hγ2 : ∀ z ∈ specDomain N C, strongX N q z ^ (1 - τ) ≤ 2 * strongX N q z)
    (hδ : 2 * Cm ^ 3 * Cs / Real.log N ≤ 1 / 2)
    (hP : 64 * Cm ^ 4 * (Cm ^ 8 * (40 + 40 * Cs)) * σ ^ 40 ≤ phi N ^ C)
    (hPe : Co + Cd * A1 + (Co + Cd) * A1 ^ 2 * (4 * (64 * Cm ^ 4 * (Cm ^ 8 * (40 + 40 * Cs)) *
      σ ^ 40) + 2) + 2 * (64 * Cm ^ 4 * (Cm ^ 8 * (40 + 40 * Cs)) * σ ^ 40) + 2 ≤ phi N ^ C)
    (hΛγ : ∀ z ∈ specDomain N C, lamAvg H z ≤ σ ^ 20 * strongX N q z ^ (1 - τ))
    (hSC : ∀ p ∈ Λl, ‖(1 - msc p ^ 2) * (stieltjesM H p - msc p) -
        msc p ^ 3 * (stieltjesM H p - msc p) ^ 2 - msc p ^ 2 * zAvg H p‖ ≤
      Cs * (s ^ 2 * Real.log N / q ^ 2 + s ^ 4 * Real.log N * psiCtrl H p ^ 2 +
        lamAvg H p ^ 2 / Real.log N))
    (hFA : ∀ p ∈ Λl, ‖zAvg H p‖ ≤ s ^ 14 * (1 / q ^ 2 + 1 / (N * p.im) ^ 2 +
        s ^ 4 * ((msc p).im + σ ^ 20 * strongX N q p ^ (1 - τ)) / (N * p.im)))
    (hO : ∀ p ∈ Λl, lamO H p ≤ Co * (1 / q + A1 ^ 2 * psiCtrl H p))
    (hD : ∀ p ∈ Λl, (⨆ i, ‖resolventC H p i i - stieltjesM H p‖) ≤
      Cd * (A1 / q + A1 ^ 2 * psiCtrl H p)) :
    ∀ z ∈ specDomain N C, ‖stieltjesM H z - msc z‖ ≤ avgErr N C q z ∧
      ∀ i j, ‖resolventC H z i j - (if i = j then msc z else 0)‖ ≤ entryErr N C q z := by
  set Cst := Cm ^ 8 * (40 + 40 * Cs) with hCstd
  set P := 64 * Cm ^ 4 * Cst * σ ^ 40 with hPd
  have hCst : 1 ≤ Cst := by
    have : 1 ≤ Cm ^ 8 := one_le_pow₀ hCm
    nlinarith only [this, hCs]
  have hσ1 : 1 ≤ σ := hs1.trans hsσ
  have hP1 : 1 ≤ P := by
    have h1 : 1 ≤ Cm ^ 4 := one_le_pow₀ hCm
    have h2 : 1 ≤ σ ^ 40 := one_le_pow₀ hσ1
    have h3 : 1 ≤ Cm ^ 4 * Cst := one_le_mul_of_one_le_of_one_le h1 hCst
    have h4 : 1 ≤ Cm ^ 4 * Cst * σ ^ 40 := one_le_mul_of_one_le_of_one_le h3 h2
    rw [hPd]; nlinarith only [h4]
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hq0 : 0 < q := by linarith
  have hγ0 : ∀ z ∈ specDomain N C, 0 ≤ σ ^ 20 * strongX N q z ^ (1 - τ) := by
    intro z hz
    obtain ⟨-, hzi, -, -⟩ := sc_specDomain hN hz
    have : 0 < strongX N q z := by unfold strongX; positivity
    have := Real.rpow_nonneg this.le (1 - τ)
    positivity
  have hγ1 : ∀ z ∈ specDomain N C, σ ^ 20 * strongX N q z ^ (1 - τ) ≤ 1 := fun z hz =>
    (hγσ z hz).trans (inv_le_one_of_one_le₀ hσ1)
  have hγp : ∀ z ∈ specDomain N C, ∀ p ∈ specDomain N C, ‖z - p‖ ≤ (N : ℝ) ^ (-(3 : ℝ)) →
      σ ^ 20 * strongX N q p ^ (1 - τ) ≤ 2 * (σ ^ 20 * strongX N q z ^ (1 - τ)) := by
    intro z hz p hp hzp
    obtain ⟨-, hzi, -, -⟩ := sc_specDomain hN hz
    obtain ⟨-, hpi, -, -⟩ := sc_specDomain hN hp
    obtain ⟨-, h2, -, -⟩ := strong_lattice_scale hN hC1 hz hp hzp
    have := strong_X_near hq0 hN0 hzi hpi h2 hτ0 hτ1
    have h20 : 0 ≤ σ ^ 20 := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left this h20]
  have h45 := strong_45_all (γ := fun z => σ ^ 20 * strongX N q z ^ (1 - τ)) hN hH hCm hmsc
    hCs hΛlS hΛl hC1 hs1 hlg hlgs hq1 hεq hγ0 hγ1 hγp hΛγ hSC hFA
  -- (2.16) on `S(C)` with the constant `P`
  have hΛb : ∀ z ∈ specDomain N C, ‖stieltjesM H z - msc z‖ ≤
      P * (min (1 / (q ^ 2 * Real.sqrt (kappa z.re + z.im))) (1 / q) + 1 / (N * z.im)) := by
    intro z hz
    obtain ⟨hzre, hzi, hzle, -⟩ := sc_specDomain hN hz
    obtain ⟨⟨m1, m2⟩, ⟨m3, m4⟩, -⟩ := hmsc z hzre hzi hzle
    obtain ⟨w1, -⟩ := weak_w_bounds hCm m1 m2 m3 m4
    have ht : 0 < Real.sqrt (kappa z.re + z.im) := by
      have : 0 ≤ kappa z.re := abs_nonneg _
      exact Real.sqrt_pos.mpr (by linarith)
    have hγX : σ ^ 20 * strongX N q z ^ (1 - τ) ≤ 2 * σ ^ 20 * (1 / q + 1 / (N * z.im)) := by
      have := mul_le_mul_of_nonneg_left (hγ2 z hz) (by positivity : (0 : ℝ) ≤ σ ^ 20)
      have e : σ ^ 20 * (2 * strongX N q z) = 2 * σ ^ 20 * (1 / q + 1 / (N * z.im)) := by
        unfold strongX; ring
      linarith
    exact strong_final_arith hCm hCst hδ hs1 hsσ hq0 (by positivity) ht w1 (hΛγ z hz) hγX
      (h45 z hz) le_rfl
  intro z hz
  obtain ⟨hzre, hzi, hzle, -⟩ := sc_specDomain hN hz
  have hφP : P ≤ phi N ^ C := hP
  refine ⟨?_, ?_⟩
  · refine (hΛb z hz).trans ?_
    unfold avgErr
    apply mul_le_mul_of_nonneg_right hφP
    have : 0 ≤ min (1 / (q ^ 2 * Real.sqrt (kappa z.re + z.im))) (1 / q) :=
      le_min (by positivity) (by positivity)
    positivity
  -- (2.17) from a nearby lattice point
  intro i j
  obtain ⟨p, hpΛ, hzp⟩ := hΛl z hz
  have hp : p ∈ specDomain N C := hΛlS (Finset.mem_coe.mpr hpΛ)
  obtain ⟨hpre, hpi, hple, -⟩ := sc_specDomain hN hp
  obtain ⟨hsc, hzp2, hn1, hn'1⟩ := strong_lattice_scale hN hC1 hz hp hzp
  set ε : ℝ := 1 / (N * (phi N ^ C) ^ 2) with hε
  have hεq' : ε ≤ 1 / q ^ 2 := by
    have : ε ≤ s ^ 18 * ε := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hs1)
    linarith
  have hda : ‖msc z - msc p‖ ≤ ε := (weak_norm_msc_sub_le hzi hpi).trans hsc
  have hdG : ‖resolventC H z i j - resolventC H p i j‖ ≤ ε :=
    (norm_resolventC_apply_sub_le hH hzi hpi i j).trans hsc
  have hg : ‖(resolventC H z i j - (if i = j then msc z else 0)) -
      (resolventC H p i j - (if i = j then msc p else 0))‖ ≤ 2 * ε := by
    have e : (resolventC H z i j - (if i = j then msc z else 0)) -
        (resolventC H p i j - (if i = j then msc p else 0)) =
        (resolventC H z i j - resolventC H p i j) -
          ((if i = j then msc z else 0) - (if i = j then msc p else 0)) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have : ‖(if i = j then msc z else 0) - (if i = j then msc p else 0)‖ ≤ ε := by
      split_ifs
      · exact hda
      · simp only [sub_self, norm_zero]; positivity
    linarith
  have hIp : (msc p).im ≤ (msc z).im + ε := by
    have h1 : |(msc p).im - (msc z).im| ≤ ‖msc p - msc z‖ := by
      have := Complex.abs_im_le_norm (msc p - msc z)
      rwa [Complex.sub_im] at this
    rw [norm_sub_rev] at h1
    linarith [(abs_le.mp (h1.trans hda)).2]
  have hΛp : lamAvg H p ≤ P * (1 / q + 1 / (N * p.im)) := by
    have h := hΛb p hp
    unfold lamAvg
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    have := min_le_right (1 / (q ^ 2 * Real.sqrt (kappa p.re + p.im))) (1 / q)
    linarith
  have hpsi0 : 0 ≤ psiCtrl H p := Real.sqrt_nonneg _
  have hg' : ‖resolventC H p i j - (if i = j then msc p else 0)‖ ≤
      Co * (1 / q + A1 ^ 2 * psiCtrl H p) + Cd * (A1 / q + A1 ^ 2 * psiCtrl H p) +
        lamAvg H p := by
    have hc1 : 0 ≤ Co * (1 / q + A1 ^ 2 * psiCtrl H p) := by positivity
    have hc2 : 0 ≤ Cd * (A1 / q + A1 ^ 2 * psiCtrl H p) := by positivity
    have hc3 : 0 ≤ lamAvg H p := norm_nonneg _
    split_ifs with hij
    · subst hij
      have h1 : ‖resolventC H p i i - stieltjesM H p‖ ≤
          ⨆ k, ‖resolventC H p k k - stieltjesM H p‖ :=
        le_ciSup (f := fun k => ‖resolventC H p k k - stieltjesM H p‖)
          (Set.finite_range _).bddAbove i
      have e : resolventC H p i i - msc p =
          (resolventC H p i i - stieltjesM H p) + (stieltjesM H p - msc p) := by ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have := hD p hpΛ
      unfold lamAvg at hc3 ⊢
      linarith
    · rw [sub_zero]
      have h1 := norm_resolventC_off_le_lamO (H := H) (z := p) hij
      have := hO p hpΛ
      linarith
  have hlamp0 : 0 ≤ lamAvg H p := norm_nonneg _
  have hres := strong_entry_arith (Ψp := psiCtrl H p) (Ip := (msc p).im) (Iz := (msc z).im)
    hCo hCd hA1 (sq_nonneg A1) hP1 hq1 hn1
    (by nlinarith only [hzp2, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) hεq' hlamp0 hΛp
    (im_msc_pos hpi).le (im_msc_pos hzi).le hIp rfl hg' hg hPe
  unfold entryErr
  exact hres

/-! ### The start of the iteration and the probability bookkeeping -/

/-- (4.16) of [15]: the weak law at level `ζ + 3` gives `Λ ≤ σ^{20} x^{1/3}` with `σ = φ^{ζ+3}`;
`a = φ^{4(ζ+3)/3}`, `n = Nη`. -/
private lemma strong_initial {q n σ Cw a : ℝ} (hq1 : 1 ≤ q) (hn : 0 < n) (ha : a ≤ σ ^ 2)
    (hCw : 0 < Cw) (hσ : 2 * Cw ≤ σ) (hσ1 : 1 ≤ σ) :
    Cw * (σ / Real.sqrt q + a / n ^ ((1 : ℝ) / 3)) ≤
      σ ^ 20 * (1 / q + 1 / n) ^ ((1 : ℝ) / 3) := by
  have hq0 : 0 < q := by linarith
  set X := 1 / q + 1 / n with hX
  have hX0 : 0 < X := by positivity
  have hiq : 0 < 1 / q := by positivity
  have hiq1 : 1 / q ≤ 1 := by rw [div_le_one hq0]; exact hq1
  have h1 : 1 / Real.sqrt q ≤ X ^ ((1 : ℝ) / 3) := by
    have e : 1 / Real.sqrt q = (1 / q) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.div_rpow zero_le_one hq0.le, Real.one_rpow]
    rw [e]
    calc (1 / q) ^ ((1 : ℝ) / 2) ≤ (1 / q) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_exponent_ge hiq hiq1 (by norm_num)
      _ ≤ X ^ ((1 : ℝ) / 3) := by
          have : 0 < 1 / n := by positivity
          exact Real.rpow_le_rpow hiq.le (by rw [hX]; linarith) (by norm_num)
  have h2 : 1 / n ^ ((1 : ℝ) / 3) ≤ X ^ ((1 : ℝ) / 3) := by
    have e : 1 / n ^ ((1 : ℝ) / 3) = (1 / n) ^ ((1 : ℝ) / 3) := by
      rw [Real.div_rpow zero_le_one hn.le, Real.one_rpow]
    rw [e]
    exact Real.rpow_le_rpow (by positivity) (by rw [hX]; linarith) (by norm_num)
  have hY0 : 0 ≤ X ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hX0.le _
  have ha0 : 0 ≤ a ∨ a < 0 := le_or_gt 0 a
  have h3 : σ / Real.sqrt q ≤ σ * X ^ ((1 : ℝ) / 3) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  have h4 : a / n ^ ((1 : ℝ) / 3) ≤ σ ^ 2 * X ^ ((1 : ℝ) / 3) := by
    rw [div_eq_mul_one_div]
    have hn3 : 0 < n ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn _
    rcases ha0 with ha0 | ha0
    · exact mul_le_mul ha h2 (by positivity) (by positivity)
    · have : a * (1 / n ^ ((1 : ℝ) / 3)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ha0.le (by positivity)
      have : 0 ≤ σ ^ 2 * X ^ ((1 : ℝ) / 3) := by positivity
      linarith
  have h5 : σ ≤ σ ^ 2 := by nlinarith only [hσ1]
  have h6 : 2 * Cw * σ ^ 2 ≤ σ ^ 20 := by
    have : σ ^ 3 ≤ σ ^ 20 := pow_le_pow_right₀ hσ1 (by norm_num)
    have : 2 * Cw * σ ^ 2 ≤ σ * σ ^ 2 := mul_le_mul_of_nonneg_right hσ (by positivity)
    nlinarith only [this, ‹σ ^ 3 ≤ σ ^ 20›]
  calc Cw * (σ / Real.sqrt q + a / n ^ ((1 : ℝ) / 3)) ≤
        Cw * (σ * X ^ ((1 : ℝ) / 3) + σ ^ 2 * X ^ ((1 : ℝ) / 3)) := by
        apply mul_le_mul_of_nonneg_left _ hCw.le; linarith
    _ ≤ 2 * Cw * σ ^ 2 * X ^ ((1 : ℝ) / 3) := by
        have := mul_le_mul_of_nonneg_right h5 hY0
        nlinarith only [this, hCw, hY0]
    _ ≤ σ ^ 20 * X ^ ((1 : ℝ) / 3) := mul_le_mul_of_nonneg_right h6 hY0

/-- The eventual conditions on `N` used in the proof of (2.16)–(2.17) of [15]. -/
private lemma strong_eventually {ζ : ℝ} (hζ : 0 < ζ) (Bσ B6 Bl : ℝ) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ Bσ * (Real.log N + 1) ≤ phi N ^ (ζ + 3) ∧
      1 * (Real.log N + 1) ≤ phi N ^ ζ ∧ B6 * (Real.log N + 1) ≤ phi N ^ ζ ∧
      Bl ≤ Real.log N ∧ 40 ≤ Real.log (Real.log N) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_mul_log_add_one_le_phi_rpow (by linarith : 0 < ζ + 3) Bσ,
    eventually_mul_log_add_one_le_phi_rpow hζ 1, eventually_mul_log_add_one_le_phi_rpow hζ B6,
    hlog.eventually_ge_atTop Bl, hloglog.eventually_ge_atTop 40]
    with N h1 h2 h3 h4 h5
  exact ⟨h1.1, h1.2, h2.2, h3.2, h4, h5⟩

/-- A union over a lattice of at most `N^K` points of events of probability at most `r`. -/
private lemma strong_law_lattice {N : ℕ} {L : EntryLaws N} {Λl : Finset ℂ}
    {S : ℂ → Set (Entries N)} {r K : ℝ} (hr : 0 ≤ r) (hcard : (Λl.card : ℝ) ≤ (N : ℝ) ^ K)
    (h : ∀ p ∈ Λl, L.law (S p) ≤ ENNReal.ofReal r) :
    L.law {ω | ∃ p ∈ Λl, ω ∈ S p} ≤ ENNReal.ofReal ((N : ℝ) ^ K * r) := by
  have e : {ω | ∃ p ∈ Λl, ω ∈ S p} = ⋃ p ∈ Λl, S p := by
    ext ω; simp
  rw [e]
  calc L.law (⋃ p ∈ Λl, S p) ≤ ∑ p ∈ Λl, L.law (S p) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ Λl, ENNReal.ofReal r := Finset.sum_le_sum h
    _ = ENNReal.ofReal (Λl.card * r) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ K * r) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hr)

/-- `μ (A ∪ B ∪ C ∪ D) ≤ a + b + c + d`. -/
private lemma strong_law_union4 {N : ℕ} {L : EntryLaws N} {A B C D : Set (Entries N)}
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : L.law A ≤ ENNReal.ofReal a) (hB : L.law B ≤ ENNReal.ofReal b)
    (hC : L.law C ≤ ENNReal.ofReal c) (hD : L.law D ≤ ENNReal.ofReal d) :
    L.law (A ∪ B ∪ C ∪ D) ≤ ENNReal.ofReal (a + b + c + d) := by
  calc L.law (A ∪ B ∪ C ∪ D) ≤ L.law A + L.law B + L.law C + L.law D := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d := by
        gcongr
    _ = ENNReal.ofReal (a + b + c + d) := by
        rw [ENNReal.ofReal_add (by positivity) hd, ENNReal.ofReal_add (by positivity) hc,
          ENNReal.ofReal_add ha hb]

/-- `q² ≤ N` for a generalized Wigner law with entries bounded by `q⁻¹` almost surely: the
variance `N⁻¹` of an off-diagonal entry is at most `q⁻²`. -/
private lemma strong_q_sq_le {N : ℕ} (hN : 2 ≤ N) {L : EntryLaws N} {C0 q : ℝ}
    (hL : L.IsGenWigner C0) (hq : L.BoundedSupportAS q) (hq0 : 0 < q) : q ^ 2 ≤ N := by
  let p0 : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  have := hL.isProb.off p0
  have hv := hL.var_off p0
  have hae : ∀ᵐ x ∂(L.off p0), |x| ≤ q⁻¹ := by
    rw [ae_iff]
    simpa [not_le] using hq.2 p0
  have hle : ∫ x, x ^ 2 ∂(L.off p0) ≤ q⁻¹ ^ 2 := by
    have : ∫ x, x ^ 2 ∂(L.off p0) ≤ ∫ _x, q⁻¹ ^ 2 ∂(L.off p0) :=
      integral_mono_ae (hL.sq_int_off p0) (integrable_const _) (by
        filter_upwards [hae] with x hx
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
    simpa using this
  rw [hv, inv_pow] at hle
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  exact (inv_le_inv₀ hNpos (by positivity)).1 hle

private lemma strong_exp_two : (4 : ℝ) * Real.exp (-2) ≤ 1 ∧ (6 : ℝ) * Real.exp (-2) ≤ 1 := by
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : 6 ≤ Real.exp 2 := by rw [h2]; nlinarith only [h]
  have h4 : Real.exp (-2) = (Real.exp 2)⁻¹ := by rw [Real.exp_neg]
  have h5 : 0 < Real.exp 2 := Real.exp_pos _
  rw [h4]
  constructor
  · rw [← div_eq_mul_inv, div_le_one h5]; linarith
  · rw [← div_eq_mul_inv, div_le_one h5]; linarith

/-- The probability bookkeeping of one iteration step: the input bound at the level `s_k` and the
new exceptional events give the input bound at the level `s_{k+1}`. -/
private lemma strong_exp_step {ν sk sk1 NA NK cΩ σ cs : ℝ} (hNA4 : 4 * NK ≤ NA) (hNA : 4 ≤ NA)
    (hNK0 : 0 ≤ NK) (hν : 0 < ν) (hcΩ : ν ≤ cΩ) (hcs : ν ≤ cs) (hσ : sk ≤ σ) (h1 : sk1 ≤ sk)
    (h0 : 0 ≤ sk1) (hgap : 2 ≤ ν * (sk - sk1)) :
    NA * Real.exp (-ν * sk) + Real.exp (-cΩ * σ) + NK * Real.exp (-ν * sk1) +
      NK * Real.exp (-cs * sk) ≤ NA * Real.exp (-ν * sk1) := by
  obtain ⟨e4, -⟩ := strong_exp_two
  set E := Real.exp (-ν * sk1) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have k1 : Real.exp (-ν * sk) ≤ E / 4 := by
    have : Real.exp (-ν * sk) ≤ Real.exp (-2) * E := by
      rw [hE, ← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    nlinarith only [this, e4, hE0, Real.exp_pos (-2)]
  have k2 : Real.exp (-cΩ * σ) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    nlinarith only [hcΩ, hσ, h1, h0, hν]
  have k3 : Real.exp (-cs * sk) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    nlinarith only [hcs, h1, h0, hν]
  have hNA0 : 0 ≤ NA := by linarith
  have t1 : NA * Real.exp (-ν * sk) ≤ NA * (E / 4) := mul_le_mul_of_nonneg_left k1 hNA0
  have t2 : Real.exp (-cΩ * σ) ≤ NA * E / 4 := by nlinarith only [k2, hNA, hE0]
  have t3 : NK * Real.exp (-cs * sk) ≤ NK * E := mul_le_mul_of_nonneg_left k3 hNK0
  have t4 : NK * E + NK * E ≤ NA * E / 2 := by nlinarith only [hNA4, hE0]
  nlinarith only [t1, t2, t3, t4]

/-- The final probability bound: six exceptional events of probability at most `N^A e^{-ν φ^ζ}`
each give `e^{-(ν/2) φ^ζ}`. -/
private lemma strong_exp_final {ν sM a NA NK cΩ σ cs co cd A lg : ℝ} (hNK : NK ≤ NA)
    (hNK0 : 0 ≤ NK) (hNA : NA ≤ Real.exp (A * lg)) (hν : 0 < ν) (hcΩ : ν ≤ cΩ) (hcs : ν ≤ cs)
    (hco : ν ≤ co) (hcd : ν ≤ cd) (haM : a ≤ sM) (haσ : a ≤ σ) (ha0 : 0 ≤ a)
    (hAlg : 0 ≤ A * lg) (hbig : A * lg + 2 ≤ ν / 2 * a) :
    NA * Real.exp (-ν * sM) + Real.exp (-cΩ * σ) + NK * Real.exp (-ν * a) +
      NK * Real.exp (-cs * sM) + NK * Real.exp (-co * a) + NK * Real.exp (-cd * a) ≤
      Real.exp (-(ν / 2) * a) := by
  obtain ⟨-, e6⟩ := strong_exp_two
  set E := Real.exp (-ν * a) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have k1 : Real.exp (-ν * sM) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr; nlinarith only [haM, hν]
  have k2 : Real.exp (-cΩ * σ) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr; nlinarith only [hcΩ, haσ, ha0, hν]
  have k3 : Real.exp (-cs * sM) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr; nlinarith only [hcs, haM, ha0, hν]
  have k4 : Real.exp (-co * a) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr; nlinarith only [hco, ha0]
  have k5 : Real.exp (-cd * a) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr; nlinarith only [hcd, ha0]
  have hNA0 : 0 ≤ NA := le_trans hNK0 hNK
  have hsum : NA * Real.exp (-ν * sM) + Real.exp (-cΩ * σ) + NK * Real.exp (-ν * a) +
      NK * Real.exp (-cs * sM) + NK * Real.exp (-co * a) + NK * Real.exp (-cd * a) ≤
      (5 * NA + 1) * E := by
    have t1 := mul_le_mul_of_nonneg_left k1 hNA0
    have t3 := mul_le_mul_of_nonneg_left k3 hNK0
    have t4 := mul_le_mul_of_nonneg_left k4 hNK0
    have t5 := mul_le_mul_of_nonneg_left k5 hNK0
    have t6 : NK * E ≤ NA * E := mul_le_mul_of_nonneg_right hNK hE0.le
    nlinarith only [t1, k2, t3, t4, t5, t6, hNK, hE0]
  refine hsum.trans ?_
  have hA : (5 * NA + 1) * E ≤ 6 * Real.exp (A * lg) * E := by
    apply mul_le_mul_of_nonneg_right _ hE0.le
    have : 1 ≤ Real.exp (A * lg) := Real.one_le_exp hAlg
    linarith
  refine hA.trans ?_
  have e : 6 * Real.exp (A * lg) * E = 6 * Real.exp (-2) * Real.exp (A * lg + 2 - ν * a) := by
    rw [hE, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [e]
  have h1 : Real.exp (A * lg + 2 - ν * a) ≤ Real.exp (-(ν / 2) * a) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : 0 < Real.exp (A * lg + 2 - ν * a) := Real.exp_pos _
  nlinarith only [e6, h1, h2]

/-- The constant of (2.17): `Co + Cd a + (Co + Cd) a² (4P + 2) + 2P + 2 ≤ σ^n` for
`P = Q σ^{40}`, `a ≤ σ`, `(7 Co + 7 Cd + 4) Q ≤ σ` and `n ≥ 43`. -/
private lemma strong_Pe {Co Cd a σ Q : ℝ} {n : ℕ} (hCo : 0 ≤ Co) (hCd : 0 ≤ Cd) (ha0 : 0 ≤ a)
    (haσ : a ≤ σ) (hσ1 : 1 ≤ σ) (hQ1 : 1 ≤ Q) (hσQ : (7 * Co + 7 * Cd + 4) * Q ≤ σ)
    (hn : 43 ≤ n) :
    Co + Cd * a + (Co + Cd) * a ^ 2 * (4 * (Q * σ ^ 40) + 2) + 2 * (Q * σ ^ 40) + 2 ≤
      σ ^ n := by
  set P := Q * σ ^ 40 with hP
  have hσ40 : 1 ≤ σ ^ 40 := one_le_pow₀ hσ1
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le hQ1 hσ40
  have hσ2 : 1 ≤ σ ^ 2 := one_le_pow₀ hσ1
  have ha2 : a ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ ha0 haσ 2
  have hP0 : 0 ≤ P := by linarith
  have k1 : Co ≤ Co * (σ ^ 2 * P) :=
    le_mul_of_one_le_right hCo (one_le_mul_of_one_le_of_one_le hσ2 hP1)
  have k2 : Cd * a ≤ Cd * (σ ^ 2 * P) := by
    apply mul_le_mul_of_nonneg_left _ hCd
    nlinarith only [haσ, hσ1, hP1, hσ2, ha0]
  have k3 : (Co + Cd) * a ^ 2 * (4 * P + 2) ≤ (Co + Cd) * (6 * (σ ^ 2 * P)) := by
    have : a ^ 2 * (4 * P + 2) ≤ 6 * (σ ^ 2 * P) := by
      nlinarith only [ha2, hP1, hσ2, sq_nonneg a]
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ Co + Cd)
    linarith
  have k4 : 2 * P + 2 ≤ 4 * (σ ^ 2 * P) := by nlinarith only [hσ2, hP1]
  have hsum : Co + Cd * a + (Co + Cd) * a ^ 2 * (4 * P + 2) + 2 * P + 2 ≤
      (7 * Co + 7 * Cd + 4) * Q * σ ^ 42 := by
    have e : (7 * Co + 7 * Cd + 4) * Q * σ ^ 42 = (7 * Co + 7 * Cd + 4) * (σ ^ 2 * P) := by
      rw [hP]; ring
    rw [e]
    nlinarith only [k1, k2, k3, k4]
  have h43 : σ ^ 43 ≤ σ ^ n := pow_le_pow_right₀ hσ1 hn
  have : (7 * Co + 7 * Cd + 4) * Q * σ ^ 42 ≤ σ * σ ^ 42 :=
    mul_le_mul_of_nonneg_right hσQ (by positivity)
  have e2 : σ * σ ^ 42 = σ ^ 43 := by ring
  linarith

/-- (2.16)–(2.17) of [15] on `S(C)` for almost surely bounded entries, following the proof of
Theorem 2.8 of [15] in §4: the weak law (4.16), the iteration of Lemma 4.2 over the levels
`s_k = φ^ζ (log N)^{2(M+1-k)}`, the last step (4.24)–(4.28), and (2.17) from (3.32), (3.36). -/
private lemma strong_main {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ C ≤ q →
      L.law (localLawEvent N C q)ᶜ ≤ ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  classical
  have hζ3 : 0 < ζ + 3 := by linarith
  obtain ⟨Kw, -, Cw, hCw, cw, hcw, Nw, hW⟩ := weakLocalLaw hζ3 hC0
  obtain ⟨KΩ, -, cΩ, hcΩ, NΩ, hΩ⟩ := weakLocalLaw_omega hζ3 hC0
  obtain ⟨Kf, -, ν0, hν0, hFA⟩ := fluctuation_averaging_level hζ hC0
  obtain ⟨Ks, -, Cs, hCs, cs, hcs, Ns, hSC⟩ := selfConsistent_on_omega hζ hC0
  obtain ⟨Ko, -, Co, hCo, co, hco, No, hO⟩ := lamO_le_on_omega hζ hC0
  obtain ⟨Kd, -, Cd, hCd, cd, hcd, Nd, hD⟩ := norm_resolventC_diag_sub_le_on_omega hζ hC0
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  have hmsc' : WeakMscBd Cm := hmsc
  obtain ⟨C1, -, hdich⟩ := dichotomy 1 (Cm ^ 4) one_pos (one_le_pow₀ hCm) 18 (by norm_num)
  have hdich' : WeakDich 1 (Cm ^ 4) 18 C1 := hdich
  set Cst : ℝ := Cm ^ 8 * (40 + 40 * Cs) with hCst
  have hCst1 : 1 ≤ Cst := by
    have : 1 ≤ Cm ^ 8 := one_le_pow₀ hCm
    nlinarith only [this, hCs]
  set Km : ℝ := max (max (max Kw KΩ) (max Kf Ks)) (max Ko Kd) with hKm
  set n : ℕ := ⌈Km / (ζ + 3)⌉₊ + 100 with hn
  set C : ℝ := (n : ℝ) * (ζ + 3) with hCdef
  have hn100 : 100 ≤ n := by omega
  have hKmC : Km ≤ C := by
    have h1 : Km / (ζ + 3) ≤ (⌈Km / (ζ + 3)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Km / (ζ + 3)⌉₊ : ℝ) ≤ n := by rw [hn]; push_cast; linarith
    have h3 := (div_le_iff₀ hζ3).mp (h1.trans h2)
    rw [hCdef]; linarith
  have hKwC : Kw ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKmC
  have hKΩC : KΩ ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hKmC
  have hKfC : Kf ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKmC
  have hKsC : Ks ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hKmC
  have hKoC : Ko ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hKmC
  have hKdC : Kd ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hKmC
  have hCpos : 0 < C := by positivity
  obtain ⟨Klat, Nlat, hlat⟩ := exists_lattice_specDomain C
  set ν : ℝ := min (min ν0 (min cw cΩ)) (min cs (min co cd)) with hν
  have hνpos : 0 < ν := lt_min (lt_min hν0 (lt_min hcw hcΩ)) (lt_min hcs (lt_min hco hcd))
  have hνν0 : ν ≤ ν0 := (min_le_left _ _).trans (min_le_left _ _)
  have hνcw : ν ≤ cw := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνcΩ : ν ≤ cΩ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνcs : ν ≤ cs := (min_le_right _ _).trans (min_le_left _ _)
  have hνco : ν ≤ co := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνcd : ν ≤ cd := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set A : ℝ := max Klat 0 + 2 with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨Nf, hFAN⟩ := hFA ν hνpos hνν0 A hA0
  set Bσ : ℝ := max (max 2 (max 18 C1 * Cst))
    (max (2 * Cw) ((7 * Co + 7 * Cd + 4) * (64 * Cm ^ 4 * Cst))) with hBσ
  set B6 : ℝ := 2 * (A + 3) / ν with hB6
  set Bl : ℝ := max 2 (4 * Cm ^ 3 * Cs) with hBl
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (strong_eventually hζ Bσ B6 Bl)
  refine ⟨C, hCpos, ν / 2, by positivity,
    max N1 (max Nw (max NΩ (max Nf (max Ns (max No (max Nd Nlat)))))), ?_⟩
  intro N hN L q hL hq hqC
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨hNN1, hNw, hNΩ, hNf, hNs, hNo, hNd, hNlat⟩ := hN
  obtain ⟨hN3, hBσN, hφζN, hB6N, hBlN, hll⟩ := hN1 N hNN1
  -- `N`, `φ`, `σ`
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  set lg : ℝ := Real.log N with hlg
  have hlg2 : 2 ≤ lg := le_trans (le_max_left _ _) hBlN
  have hlg1 : 1 ≤ lg := by linarith
  have hlg0 : 0 < lg := by linarith
  have hφ1 : 1 ≤ phi N := sc_one_le_phi hN3
  have hφ0 : 0 < phi N := by linarith
  set σ : ℝ := phi N ^ (ζ + 3) with hσ
  have hσB : Bσ ≤ σ := by
    have h0 : 0 ≤ Bσ := le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
    have : Bσ ≤ Bσ * (lg + 1) := le_mul_of_one_le_right h0 (by linarith)
    linarith
  have hσ2 : 2 ≤ σ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hσB
  have hσ1 : 1 ≤ σ := by linarith
  have hσ0 : 0 < σ := by linarith
  have hσmax : max 18 C1 * Cst ≤ σ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hσB
  have hσCw : 2 * Cw ≤ σ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hσB
  have hσE : (7 * Co + 7 * Cd + 4) * (64 * Cm ^ 4 * Cst) ≤ σ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hσB
  have hφC : phi N ^ C = σ ^ n := by
    rw [hCdef, hσ, mul_comm, Real.rpow_mul hφ0.le, Real.rpow_natCast]
  have hC1 : 1 ≤ phi N ^ C := by rw [hφC]; exact one_le_pow₀ hσ1
  have hφCpos : 0 < phi N ^ C := by linarith
  have hσn64 : 2 * σ ^ 63 ≤ σ ^ n := by
    have h1 : σ ^ 64 ≤ σ ^ n := pow_le_pow_right₀ hσ1 (by omega)
    have e : σ ^ 64 = σ * σ ^ 63 := by ring
    have : 2 * σ ^ 63 ≤ σ * σ ^ 63 := mul_le_mul_of_nonneg_right hσ2 (by positivity)
    linarith
  have hφζ1 : 1 ≤ phi N ^ ζ := Real.one_le_rpow hφ1 hζ.le
  have hlgφ : lg + 1 ≤ phi N ^ ζ := by linarith
  have hφζσ : phi N ^ ζ ≤ σ := sc_rpow_mono hN3 (by linarith)
  have hσφ3 : σ = phi N ^ ζ * phi N ^ (3 : ℕ) := by
    rw [hσ, Real.rpow_add hφ0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- `q`
  have hσn2 : 2 ≤ σ ^ n := le_trans hσ2 (le_self_pow₀ hσ1 (by omega))
  have hq2 : 2 ≤ q := by rw [hφC] at hqC; linarith
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hqN : q ^ 2 ≤ N := strong_q_sq_le (by omega) hL hq hq0
  have hqK : ∀ K, K ≤ C → phi N ^ K ≤ q := fun K hK => (sc_rpow_mono hN3 hK).trans hqC
  have hSK : ∀ K, K ≤ C → specDomain N C ⊆ specDomain N K :=
    fun K hK z hz => sc_specDomain_mono hN3 hK hz
  -- the lattice
  obtain ⟨Λl, hΛlS, hcard, hdense⟩ := hlat N hNlat
  have hNK0 : 0 ≤ (N : ℝ) ^ Klat := Real.rpow_nonneg hN0.le _
  have hNA : (N : ℝ) ^ A = (N : ℝ) ^ max Klat 0 * (N : ℝ) ^ 2 := by
    rw [hA, Real.rpow_add hN0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hNKA : 4 * (N : ℝ) ^ Klat ≤ (N : ℝ) ^ A := by
    rw [hNA]
    have h1 : (N : ℝ) ^ Klat ≤ (N : ℝ) ^ max Klat 0 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    have h2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNr]
    have h3 : 0 ≤ (N : ℝ) ^ max Klat 0 := Real.rpow_nonneg hN0.le _
    nlinarith only [h1, h2, h3, hNK0]
  have hNA4 : 4 ≤ (N : ℝ) ^ A := by
    rw [hNA]
    have h1 : 1 ≤ (N : ℝ) ^ max Klat 0 := Real.one_le_rpow (by linarith) (le_max_right _ _)
    have h2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNr]
    nlinarith only [h1, h2]
  have hNAexp : (N : ℝ) ^ A ≤ Real.exp (A * lg) := by
    rw [Real.rpow_def_of_pos hN0, hlg, mul_comm]
  -- the levels
  set M : ℕ := Nat.log 2 ⌊lg⌋₊ with hM
  obtain ⟨-, hM2, hM3⟩ := strong_levels hN3 hlg2 hll
  set s : ℕ → ℝ := fun k => phi N ^ ζ * lg ^ (2 * (M + 1 - k)) with hs
  have hs_lo : ∀ k, k ≤ M → phi N ^ ζ * lg ^ 2 ≤ s k := by
    intro k hk
    simp only [hs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlg1 (by omega)) (by positivity)
  have hs_hi : ∀ k, s k ≤ σ := by
    intro k
    simp only [hs]
    rw [hσφ3]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (pow_le_pow_right₀ hlg1 (Nat.mul_le_mul_left 2 (Nat.sub_le (M + 1) k))).trans hM3
  have hφlg : phi N ^ ζ ≤ phi N ^ ζ * lg ^ 2 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlg1)
  have hs_ge : ∀ k, k ≤ M → phi N ^ ζ ≤ s k := fun k hk => hφlg.trans (hs_lo k hk)
  have hs1 : ∀ k, k ≤ M → 1 ≤ s k := fun k hk => hφζ1.trans (hs_ge k hk)
  have hlgs : ∀ k, k ≤ M → lg ≤ s k := fun k hk => by linarith [hs_ge k hk]
  have hs_succ : ∀ k, k ≤ M → s k = s (k + 1) * lg ^ 2 := by
    intro k hk
    simp only [hs]
    have e : 2 * (M + 1 - k) = 2 * (M + 1 - (k + 1)) + 2 := by omega
    rw [e, pow_add]; ring
  have hs_step : ∀ k, k ≤ M → -ν * s k / lg ^ 2 = -ν * s (k + 1) := by
    intro k hk
    rw [hs_succ k hk]
    field_simp
  have hs_M : -ν * s M / lg ^ 2 = -ν * phi N ^ ζ := by
    have e : s M = phi N ^ ζ * lg ^ 2 := by
      simp only [hs]
      rw [show M + 1 - M = 1 by omega]
    rw [e]; field_simp
  have hσinv : ∀ k, (s k)⁻¹ ≥ σ⁻¹ ∨ s k ≤ 0 := fun k => by
    rcases le_or_gt (s k) 0 with h | h
    · exact Or.inr h
    · exact Or.inl (inv_anti₀ h (hs_hi k))
  -- `τ`, `γ`, `x`
  set τ : ℕ → ℝ := fun k => 2 / 3 / 2 ^ k with hτ
  have hτ0 : ∀ k, 0 ≤ τ k := fun k => by simp only [hτ]; positivity
  have hτ23 : ∀ k, τ k ≤ 2 / 3 := fun k => by
    simp only [hτ]; exact div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  have hτ1 : ∀ k, τ k ≤ 1 := fun k => (hτ23 k).trans (by norm_num)
  have hτsucc : ∀ k, τ (k + 1) = τ k / 2 := fun k => by simp only [hτ]; rw [pow_succ]; ring
  have hτzero : 1 - τ 0 = 1 / 3 := by simp only [hτ]; norm_num
  have hτM : τ M * lg ≤ 4 / 3 := by
    simp only [hτ]
    have h2M : (0 : ℝ) < 2 ^ M := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ h2M]
    nlinarith only [hM2]
  have hXb : ∀ z ∈ specDomain N C, 0 < strongX N q z ∧ 1 / q ≤ strongX N q z ∧
      strongX N q z ≤ (σ ^ 63)⁻¹ := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := strong_X_bounds hN3 hφCpos hqC hz
    refine ⟨h1, h2, h3.trans ?_⟩
    rw [hφC, div_le_iff₀ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith
  have hX1 : ∀ z ∈ specDomain N C, strongX N q z ≤ 1 := fun z hz =>
    (hXb z hz).2.2.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hσ1))
  set γ : ℕ → ℂ → ℝ := fun k z => σ ^ 20 * strongX N q z ^ (1 - τ k) with hγ
  have hγσ : ∀ k, ∀ z ∈ specDomain N C, γ k z ≤ σ⁻¹ := fun k z hz =>
    strong_gamma_small (hXb z hz).1 hσ1 (hXb z hz).2.2 (hτ23 k)
  have hγs : ∀ k, ∀ z ∈ specDomain N C, γ k z ≤ (s k)⁻¹ := by
    intro k z hz
    have hsk : 0 < s k := by
      simp only [hs]; positivity
    exact (hγσ k z hz).trans (inv_anti₀ hsk (hs_hi k))
  have hγ2 : ∀ z ∈ specDomain N C, strongX N q z ^ (1 - τ M) ≤ 2 * strongX N q z :=
    fun z hz => strong_gamma_last hq1 hqN (hXb z hz).2.1 (hτ0 M) hτM
  -- the remaining numeric conditions
  have hεq : ∀ k, s k ^ 18 * (1 / (N * (phi N ^ C) ^ 2)) ≤ 1 / q ^ 2 := by
    intro k
    have hsk0 : 0 ≤ s k := by simp only [hs]; positivity
    have h1 : s k ^ 18 ≤ (phi N ^ C) ^ 2 := by
      rw [hφC, ← pow_mul]
      exact (pow_le_pow_left₀ hsk0 (hs_hi k) 18).trans (pow_le_pow_right₀ hσ1 (by omega))
    calc s k ^ 18 * (1 / (N * (phi N ^ C) ^ 2)) ≤ (phi N ^ C) ^ 2 * (1 / (N * (phi N ^ C) ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 / N := by field_simp
      _ ≤ 1 / q ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) hqN
  have hδ : 2 * Cm ^ 3 * Cs / lg ≤ 1 / 2 := by
    rw [div_le_iff₀ hlg0]
    have := le_trans (le_max_right _ _) hBlN
    linarith
  have hP : 64 * Cm ^ 4 * Cst * σ ^ 40 ≤ phi N ^ C := by
    rw [hφC]
    have hQ : 64 * Cm ^ 4 * Cst ≤ σ := by
      refine le_trans ?_ hσE
      have : (0 : ℝ) ≤ 64 * Cm ^ 4 * Cst := by positivity
      nlinarith only [this, hCo, hCd]
    calc 64 * Cm ^ 4 * Cst * σ ^ 40 ≤ σ * σ ^ 40 := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = σ ^ 41 := by ring
      _ ≤ σ ^ n := pow_le_pow_right₀ hσ1 (by omega)
  have hPe : Co + Cd * phi N ^ ζ + (Co + Cd) * (phi N ^ ζ) ^ 2 *
      (4 * (64 * Cm ^ 4 * Cst * σ ^ 40) + 2) + 2 * (64 * Cm ^ 4 * Cst * σ ^ 40) + 2 ≤
      phi N ^ C := by
    rw [hφC]
    have hQ1 : 1 ≤ 64 * Cm ^ 4 * Cst := by
      have : 1 ≤ Cm ^ 4 := one_le_pow₀ hCm
      nlinarith only [this, hCst1]
    exact strong_Pe hCo.le hCd.le (by positivity) hφζσ hσ1 hQ1 hσE (by omega)
  -- the exceptional events
  set B : ℕ → Set (Entries N) := fun k =>
    {ω | ∃ z ∈ specDomain N C, γ k z < lamAvg (symOfEntries ω) z} with hB
  set Wb : Set (Entries N) := {ω | ∃ z ∈ specDomain N Kw,
    Cw * (1 / q + phi N ^ (2 * (ζ + 3)) / Real.sqrt (N * z.im)) < lamO (symOfEntries ω) z ∨
    Cw * (phi N ^ (ζ + 3) / Real.sqrt q + phi N ^ (4 * (ζ + 3) / 3) / (N * z.im) ^ ((1 : ℝ) / 3)) <
      lamAvg (symOfEntries ω) z} with hWb
  set Ωb : Set (Entries N) := {ω | ∃ z ∈ specDomain N KΩ,
    (phi N ^ (ζ + 3))⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} with hΩb
  set FAb : ℕ → Set (Entries N) := fun k => {ω | ∃ p ∈ Λl, ω ∈ {ω' : Entries N |
    s k ^ 14 * (1 / q ^ 2 + 1 / (N * p.im) ^ 2 + s k ^ 4 * ((msc p).im + γ k p) / (N * p.im)) <
      ‖zAvg (symOfEntries ω') p‖}} with hFAb
  set SCb : ℕ → Set (Entries N) := fun k => {ω | ∃ p ∈ Λl, ω ∈ {ω' : Entries N |
    lamD (symOfEntries ω') p + lamO (symOfEntries ω') p ≤ (s k)⁻¹ ∧
      Cs * (s k ^ 2 * Real.log N / q ^ 2 +
        s k ^ 4 * Real.log N * psiCtrl (symOfEntries ω') p ^ 2 +
        lamAvg (symOfEntries ω') p ^ 2 / Real.log N) <
      ‖(1 - msc p ^ 2) * (stieltjesM (symOfEntries ω') p - msc p) -
        msc p ^ 3 * (stieltjesM (symOfEntries ω') p - msc p) ^ 2 -
        msc p ^ 2 * zAvg (symOfEntries ω') p‖}} with hSCb
  set Ob : Set (Entries N) := {ω | ∃ p ∈ Λl, ω ∈ {ω' : Entries N |
    lamD (symOfEntries ω') p + lamO (symOfEntries ω') p ≤ (phi N ^ ζ)⁻¹ ∧
      Co * (1 / q + phi N ^ (2 * ζ) * psiCtrl (symOfEntries ω') p) <
        lamO (symOfEntries ω') p}} with hOb
  set Db : Set (Entries N) := {ω | ∃ p ∈ Λl, ω ∈ {ω' : Entries N |
    lamD (symOfEntries ω') p + lamO (symOfEntries ω') p ≤ (phi N ^ ζ)⁻¹ ∧
      Cd * (phi N ^ ζ / q + (phi N ^ ζ) ^ 2 * psiCtrl (symOfEntries ω') p) <
        ⨆ i, ‖resolventC (symOfEntries ω') p i i - stieltjesM (symOfEntries ω') p‖}} with hDb
  -- their probabilities
  have hPW : L.law Wb ≤ ENNReal.ofReal (Real.exp (-cw * phi N ^ (ζ + 3))) :=
    hW N hNw L q hL hq (hqK Kw hKwC)
  have hPΩ : L.law Ωb ≤ ENNReal.ofReal (Real.exp (-cΩ * phi N ^ (ζ + 3))) :=
    hΩ N hNΩ L q hL hq (hqK KΩ hKΩC)
  have hPSC : ∀ k, k ≤ M → L.law (SCb k) ≤
      ENNReal.ofReal ((N : ℝ) ^ Klat * Real.exp (-cs * s k)) := fun k hk =>
    strong_law_lattice (Real.exp_pos _).le hcard (fun p hp =>
      hSC N hNs L q (s k) p hL hq (hqK Ks hKsC) (hSK Ks hKsC (hΛlS hp)) (hs_ge k hk)
        (hs_hi k))
  have hPO : L.law Ob ≤ ENNReal.ofReal ((N : ℝ) ^ Klat * Real.exp (-co * phi N ^ ζ)) :=
    strong_law_lattice (Real.exp_pos _).le hcard (fun p hp =>
      hO N hNo L q p hL hq (hqK Ko hKoC) (hSK Ko hKoC (hΛlS hp)))
  have hPD : L.law Db ≤ ENNReal.ofReal ((N : ℝ) ^ Klat * Real.exp (-cd * phi N ^ ζ)) :=
    strong_law_lattice (Real.exp_pos _).le hcard (fun p hp =>
      hD N hNd L q (phi N ^ ζ) p hL hq (hqK Kd hKdC) (hSK Kd hKdC (hΛlS hp)) le_rfl hφζσ)
  have hPFA : ∀ k, k ≤ M → L.law (B k) ≤ ENNReal.ofReal ((N : ℝ) ^ A * Real.exp (-ν * s k)) →
      L.law (FAb k) ≤ ENNReal.ofReal ((N : ℝ) ^ Klat * Real.exp (-ν * s k / lg ^ 2)) :=
    fun k hk hin => strong_law_lattice (Real.exp_pos _).le hcard (fun p hp =>
      hFAN N hNf L q (s k) (specDomain N C) (γ k) hL hq (hqK Kf hKfC) (hs_ge k hk) (hs_hi k)
        (hSK Kf hKfC) (hγs k) hin p (hΛlS hp))
  -- the deterministic inclusions
  have hΩσ : ∀ ω, ω ∉ Ωb → ∀ z ∈ specDomain N C,
      lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ σ⁻¹ := by
    intro ω hω z hz
    by_contra h
    exact hω ⟨z, hSK KΩ hKΩC hz, not_le.mp h⟩
  have hgood : ∀ k, k ≤ M → ∀ ω, ω ∉ B k → ω ∉ Ωb → ω ∉ FAb k → ω ∉ SCb k →
      (∀ z ∈ specDomain N C, lamAvg (symOfEntries ω) z ≤ γ k z) ∧
      (∀ p ∈ Λl, ‖(1 - msc p ^ 2) * (stieltjesM (symOfEntries ω) p - msc p) -
        msc p ^ 3 * (stieltjesM (symOfEntries ω) p - msc p) ^ 2 -
          msc p ^ 2 * zAvg (symOfEntries ω) p‖ ≤
        Cs * (s k ^ 2 * Real.log N / q ^ 2 +
          s k ^ 4 * Real.log N * psiCtrl (symOfEntries ω) p ^ 2 +
          lamAvg (symOfEntries ω) p ^ 2 / Real.log N)) ∧
      (∀ p ∈ Λl, ‖zAvg (symOfEntries ω) p‖ ≤ s k ^ 14 * (1 / q ^ 2 + 1 / (N * p.im) ^ 2 +
        s k ^ 4 * ((msc p).im + γ k p) / (N * p.im))) := by
    intro k hk ω hBω hΩω hFAω hSCω
    refine ⟨fun z hz => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · by_contra h
      exact hBω ⟨z, hz, not_le.mp h⟩
    · by_contra h
      have hsk : 0 < s k := by simp only [hs]; positivity
      exact hSCω ⟨p, hp, ((hΩσ ω hΩω p (hΛlS hp)).trans (inv_anti₀ hsk (hs_hi k))),
        not_le.mp h⟩
    · by_contra h
      exact hFAω ⟨p, hp, not_le.mp h⟩
  have hI0 : B 0 ⊆ Wb := by
    rintro ω ⟨z, hz, hlt⟩
    by_contra hWω
    have hzW : z ∈ specDomain N Kw := hSK Kw hKwC hz
    have hle : lamAvg (symOfEntries ω) z ≤ Cw * (phi N ^ (ζ + 3) / Real.sqrt q +
        phi N ^ (4 * (ζ + 3) / 3) / (N * z.im) ^ ((1 : ℝ) / 3)) := by
      by_contra h
      exact hWω ⟨z, hzW, Or.inr (not_le.mp h)⟩
    obtain ⟨-, hzi, -, -⟩ := sc_specDomain hN3 hz
    have ha : phi N ^ (4 * (ζ + 3) / 3) ≤ σ ^ 2 := by
      rw [hσ, sc_rpow_sq hφ0]
      exact sc_rpow_mono hN3 (by linarith)
    have h2 := strong_initial hq1 (n := N * z.im) (by positivity) ha hCw hσCw hσ1
    have e : γ 0 z = σ ^ 20 * (1 / q + 1 / (N * z.im)) ^ ((1 : ℝ) / 3) := by
      simp only [hγ]
      rw [hτzero]
      rfl
    rw [← hσ] at hle
    linarith
  have hIk : ∀ k, k < M → B (k + 1) ⊆ B k ∪ Ωb ∪ FAb k ∪ SCb k := by
    intro k hk ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨⟨⟨hBω, hΩω⟩, hFAω⟩, hSCω⟩ := hc
    obtain ⟨hΛγ, hSCp, hFAp⟩ := hgood k hk.le ω hBω hΩω hFAω hSCω
    have hstep := strong_iter_det hN3 (symOfEntries_isHermitian ω) hCm hmsc' hCs hdich' hΛlS
      hdense hC1 (hs1 k hk.le) hlg1 (hlgs k hk.le) (hs_hi k) hq1 (hεq k) (hτ0 k) (hτ1 k) hX1
      (hγσ k) hδ hσmax hΛγ hSCp hFAp
    obtain ⟨z, hz, hlt⟩ := hω
    have h2 := hstep z hz
    have e : γ (k + 1) z = σ ^ 20 * strongX N q z ^ (1 - τ k / 2) := by
      simp only [hγ]
      rw [hτsucc]
    linarith
  have hIf : (localLawEvent N C q)ᶜ ⊆ (B M ∪ Ωb ∪ FAb M ∪ SCb M) ∪ (Ob ∪ Db) := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨⟨⟨⟨hBω, hΩω⟩, hFAω⟩, hSCω⟩, hOω, hDω⟩ := hc
    obtain ⟨hΛγ, hSCp, hFAp⟩ := hgood M le_rfl ω hBω hΩω hFAω hSCω
    have hΩζ : ∀ p ∈ Λl, lamD (symOfEntries ω) p + lamO (symOfEntries ω) p ≤ (phi N ^ ζ)⁻¹ :=
      fun p hp => (hΩσ ω hΩω p (hΛlS hp)).trans (inv_anti₀ (by positivity) hφζσ)
    have hOp : ∀ p ∈ Λl, lamO (symOfEntries ω) p ≤
        Co * (1 / q + (phi N ^ ζ) ^ 2 * psiCtrl (symOfEntries ω) p) := by
      intro p hp
      by_contra h
      rw [sc_rpow_sq hφ0] at h
      exact hOω ⟨p, hp, hΩζ p hp, not_le.mp h⟩
    have hDp : ∀ p ∈ Λl, (⨆ i, ‖resolventC (symOfEntries ω) p i i -
        stieltjesM (symOfEntries ω) p‖) ≤
        Cd * (phi N ^ ζ / q + (phi N ^ ζ) ^ 2 * psiCtrl (symOfEntries ω) p) := by
      intro p hp
      by_contra h
      exact hDω ⟨p, hp, hΩζ p hp, not_le.mp h⟩
    exact hω (strong_final_det hN3 (symOfEntries_isHermitian ω) hCm hmsc' hCs hCo.le hCd.le
      (by positivity) hΛlS hdense hC1 (hs1 M le_rfl) hlg1 (hlgs M le_rfl) (hs_hi M) hq1
      (hεq M) (hτ0 M) (hτ1 M) (hγσ M) hγ2 hδ hP hPe hΛγ hSCp hFAp hOp hDp)
  -- the induction over the levels
  have hνφ : 2 ≤ ν * phi N ^ ζ := by
    have h1 : B6 * (lg + 1) ≤ phi N ^ ζ := hB6N
    have e : B6 * (lg + 1) * ν = 2 * (A + 3) * (lg + 1) := by
      rw [hB6]; field_simp
    have h2 := mul_le_mul_of_nonneg_right h1 hνpos.le
    nlinarith only [h2, e, hA0, hlg0]
  have hBk : ∀ k, k ≤ M → L.law (B k) ≤ ENNReal.ofReal ((N : ℝ) ^ A * Real.exp (-ν * s k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine (measure_mono hI0).trans (hPW.trans (ENNReal.ofReal_le_ofReal ?_))
      have h1 : Real.exp (-cw * phi N ^ (ζ + 3)) ≤ Real.exp (-ν * s 0) := by
        apply Real.exp_le_exp.mpr
        have := hs_hi 0
        have h0 : 0 ≤ s 0 := by simp only [hs]; positivity
        rw [← hσ]
        nlinarith only [this, h0, hνcw, hνpos]
      have h2 : 0 < Real.exp (-ν * s 0) := Real.exp_pos _
      nlinarith only [h1, h2, hNA4]
    | succ k ih =>
      intro hk
      have hkM : k < M := by omega
      have hin := ih hkM.le
      have hFAk := hPFA k hkM.le hin
      rw [hs_step k hkM.le] at hFAk
      refine (measure_mono (hIk k hkM)).trans ((strong_law_union4 (by positivity)
        (Real.exp_pos _).le (by positivity) (by positivity) hin hPΩ hFAk
        (hPSC k hkM.le)).trans (ENNReal.ofReal_le_ofReal ?_))
      have hk1 := hs_succ k hkM.le
      have hlo := hs_ge (k + 1) hk
      have hgap : 2 ≤ ν * (s k - s (k + 1)) := by
        have h4 : (4 : ℝ) ≤ lg ^ 2 := by nlinarith only [hlg2]
        have h5 : s k - s (k + 1) ≥ phi N ^ ζ := by
          rw [hk1]; nlinarith only [h4, hlo, hφζ1]
        nlinarith only [h5, hνφ, hνpos]
      have hle0 : 0 ≤ s (k + 1) := le_trans (by linarith) hlo
      have hle1 : s (k + 1) ≤ s k := by
        rw [hk1]; exact le_mul_of_one_le_right hle0 (one_le_pow₀ hlg1)
      rw [← hσ]
      exact strong_exp_step (sk := s k) (sk1 := s (k + 1)) hNKA hNA4 hNK0 hνpos hνcΩ hνcs
        (hs_hi k) hle1 hle0 hgap
  -- the final bound
  have hBM := hBk M le_rfl
  have hFAM := hPFA M le_rfl hBM
  rw [hs_M] at hFAM
  have hbig : A * lg + 2 ≤ ν / 2 * phi N ^ ζ := by
    have h1 : B6 * (lg + 1) ≤ phi N ^ ζ := hB6N
    have e : B6 * (lg + 1) * (ν / 2) = (A + 3) * (lg + 1) := by
      rw [hB6]; field_simp
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ν / 2)
    nlinarith only [h2, e, hA0, hlg0]
  calc L.law (localLawEvent N C q)ᶜ ≤ L.law ((B M ∪ Ωb ∪ FAb M ∪ SCb M) ∪ (Ob ∪ Db)) :=
        measure_mono hIf
    _ ≤ L.law (B M ∪ Ωb ∪ FAb M ∪ SCb M) + (L.law Ob + L.law Db) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ A * Real.exp (-ν * s M) + Real.exp (-cΩ * phi N ^ (ζ + 3)) +
          (N : ℝ) ^ Klat * Real.exp (-ν * phi N ^ ζ) + (N : ℝ) ^ Klat * Real.exp (-cs * s M)) +
        (ENNReal.ofReal ((N : ℝ) ^ Klat * Real.exp (-co * phi N ^ ζ)) +
          ENNReal.ofReal ((N : ℝ) ^ Klat * Real.exp (-cd * phi N ^ ζ))) :=
        add_le_add (strong_law_union4 (by positivity) (Real.exp_pos _).le (by positivity)
          (by positivity) hBM hPΩ hFAM (hPSC M le_rfl)) (add_le_add hPO hPD)
    _ = ENNReal.ofReal ((N : ℝ) ^ A * Real.exp (-ν * s M) + Real.exp (-cΩ * phi N ^ (ζ + 3)) +
          (N : ℝ) ^ Klat * Real.exp (-ν * phi N ^ ζ) + (N : ℝ) ^ Klat * Real.exp (-cs * s M) +
          (N : ℝ) ^ Klat * Real.exp (-co * phi N ^ ζ) +
          (N : ℝ) ^ Klat * Real.exp (-cd * phi N ^ ζ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal (Real.exp (-(ν / 2) * phi N ^ ζ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← hσ]
        exact strong_exp_final (by linarith) hNK0 hNAexp hνpos hνcΩ hνcs hνco hνcd
          (hs_ge M le_rfl) hφζσ (by positivity) (by positivity) hbig

/-- The strong law (2.16)–(2.17) of [15] on `S(C)` for almost surely bounded
entries, uniformly in `q` (the per-`q` form behind Lemma 3.1 (1)). -/
theorem localLaw_boundedAS {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ C ≤ q →
      L.law (localLawEvent N C q)ᶜ ≤ ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  exact strong_main hζ hC0

/-! ### Compiled checks -/

/-- At `z = i` the errors of (3.2) and (3.3) with `q = N^{2/5}` are at most `3 N^{-1/5}` once
`φ^C ≤ N^{1/5}`. -/
private lemma strong_err_at_i {N : ℕ} (hN : 1 ≤ N) {C : ℝ} (hC : phi N ^ C ≤ (N : ℝ) ^ (1 / 5 : ℝ))
    (hC0 : 0 ≤ phi N ^ C) :
    avgErr N C ((N : ℝ) ^ (2 / 5 : ℝ)) ⟨0, 1⟩ ≤ 3 / (N : ℝ) ^ (1 / 5 : ℝ) ∧
      entryErr N C ((N : ℝ) ^ (2 / 5 : ℝ)) ⟨0, 1⟩ ≤ 3 / (N : ℝ) ^ (1 / 5 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set a := (N : ℝ) ^ (1 / 5 : ℝ) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have hq : (N : ℝ) ^ (2 / 5 : ℝ) = a * a := by
    rw [ha, ← Real.rpow_add hN0]; norm_num
  have hqpos : 0 < (N : ℝ) ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hqN : (N : ℝ) ^ (2 / 5 : ℝ) ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (2 / 5 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  have hqS : (N : ℝ) ^ (2 / 5 : ℝ) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h1N : 1 / (N : ℝ) ≤ 1 / (N : ℝ) ^ (2 / 5 : ℝ) :=
    div_le_div_of_nonneg_left zero_le_one hqpos hqN
  have hsq : Real.sqrt ((msc ⟨0, 1⟩).im / (N * (⟨0, 1⟩ : ℂ).im)) ≤ 1 / (N : ℝ) ^ (2 / 5 : ℝ) := by
    have hm : (msc ⟨0, 1⟩).im ≤ 1 := by
      have h := (norm_msc_eq_inv_and_lt_one (z := ⟨0, 1⟩) (by norm_num)).2
      exact (Complex.im_le_norm _).trans h.le
    have : (msc ⟨0, 1⟩).im / (N * (⟨0, 1⟩ : ℂ).im) ≤ 1 / N := by
      simp only [mul_one]
      exact div_le_div_of_nonneg_right hm hN0.le
    calc Real.sqrt ((msc ⟨0, 1⟩).im / (N * (⟨0, 1⟩ : ℂ).im)) ≤ Real.sqrt (1 / N) :=
          Real.sqrt_le_sqrt this
      _ = 1 / Real.sqrt N := by rw [Real.sqrt_div' 1 hN0.le, Real.sqrt_one]
      _ ≤ 1 / (N : ℝ) ^ (2 / 5 : ℝ) := div_le_div_of_nonneg_left zero_le_one hqpos hqS
  have hkey : phi N ^ C * (3 * (1 / (N : ℝ) ^ (2 / 5 : ℝ))) ≤ 3 / a := by
    rw [hq]
    have : phi N ^ C * (3 * (1 / (a * a))) ≤ a * (3 * (1 / (a * a))) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    have e : a * (3 * (1 / (a * a))) = 3 / a := by field_simp
    linarith
  have hin : 1 / ((N : ℝ) * (⟨0, 1⟩ : ℂ).im) = 1 / N := by simp
  constructor
  · unfold avgErr
    rw [hin]
    refine le_trans ?_ hkey
    apply mul_le_mul_of_nonneg_left _ hC0
    have := min_le_right (1 / (((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 *
      Real.sqrt (kappa (⟨0, 1⟩ : ℂ).re + (⟨0, 1⟩ : ℂ).im))) (1 / (N : ℝ) ^ (2 / 5 : ℝ))
    have h0 : 0 ≤ 1 / (N : ℝ) ^ (2 / 5 : ℝ) := by positivity
    linarith
  · unfold entryErr
    rw [hin]
    refine le_trans ?_ hkey
    apply mul_le_mul_of_nonneg_left _ hC0
    linarith

/-- (2.16)–(2.17) for the Rademacher laws with `q = N^{2/5}`, `ζ = 1`, `C0 = 1`: for all large
`N` the hypotheses hold, `i ∈ S(C)`, the errors of (3.2) and (3.3) at `i` are below `1` (while
`|m(i) - m_sc(i)| ≤ 2` and `|G_ii(i) - m_sc(i)| ≤ 2` hold for every matrix), and the bound
applies. -/
example : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ C ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧ (⟨0, 1⟩ : ℂ) ∈ specDomain N C ∧
    avgErr N C ((N : ℝ) ^ (2 / 5 : ℝ)) ⟨0, 1⟩ < 1 ∧
    entryErr N C ((N : ℝ) ^ (2 / 5 : ℝ)) ⟨0, 1⟩ < 1 ∧
    (radLaws N).law (localLawEvent N C ((N : ℝ) ^ (2 / 5 : ℝ)))ᶜ ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨C, hC, c, hc, N0, h⟩ := localLaw_boundedAS (ζ := 1) one_pos zero_le_one
  refine ⟨C, hC, c, hc, ?_⟩
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
  exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, e1.trans_lt h31, e2.trans_lt h31,
    h N hN (radLaws N) _ hi.1 hi.2.1 hi.2.2.1⟩

#print axioms localLaw_boundedAS

end WEdgeNS
