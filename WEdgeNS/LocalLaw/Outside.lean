import WEdgeNS.LocalLaw.Strong
import WEdgeNS.Resolvent.Spectral

/-!
# Estimates outside the spectrum for almost surely bounded entries
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- The Lipschitz bounds in `z` of the weak law and elementary bounds on `φ`.
open private weak_lamAvg_le_add weak_norm_stieltjesM_sub_le from WEdgeNS.LocalLaw.Weak
open private sc_phi_pos sc_one_le_phi sc_rad_instance from WEdgeNS.LocalLaw.SelfConsistent

/-- `η = φ^{K+a} N⁻¹ κ^{-1/2}` of (3.7), with the offset `K` in place of `3`. -/
def outEta (N : ℕ) (K a E : ℝ) : ℝ := phi N ^ (K + a) / (N * Real.sqrt (kappa E))

/-- The first two bounds of (3.8) and the eigenvalue-free intervals, at both edges, on the
window `2 + φ^C (q⁻² + N^{-2/3}) ≤ |E| ≤ 3` of (4.36) of [15], at `η = outEta N K a E`. -/
def outsideEvent (N : ℕ) (K a C q : ℝ) : Set (Entries N) :=
  {ω | ∀ E : ℝ, 2 + phi N ^ C * (1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) ≤ |E| → |E| ≤ 3 →
    ‖stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩ - msc ⟨E, outEta N K a E⟩‖ ≤
        (phi N ^ a * N * outEta N K a E)⁻¹ ∧
      (stieltjesM (symOfEntries ω) ⟨E, outEta N K a E⟩).im ≤
        (phi N ^ a * N * outEta N K a E)⁻¹ ∧
      ∀ α, outEta N K a E < |(symOfEntries_isHermitian ω).eigenvalues α - E|}

/-! ### The estimate (4.44) of [15] at one point -/

/-- The arithmetic of (4.40)–(4.45) of [15] at one point: with `1/n = X w v`, `q⁻¹ ≤ X w v²`,
`Im m_sc ≤ C_m X w² v²`, `|1 - m_sc²| ≥ X / C_m`, the a priori bound `Λ ≤ γ`, the self-consistent
equation (3.40) and the fluctuation averaging bound (4.2), one gets `Λ ≤ X w v² / 2`. -/
private lemma outside_core {Cm Csc s l q n X w v g I γ Λ A Z : ℝ}
    (hCm : 1 ≤ Cm) (hCsc : 0 < Csc) (hs : 1 ≤ s) (hl : 1 ≤ l) (hX : 0 < X) (hw : 0 < w)
    (hw1 : w ≤ 1) (hv : 0 < v) (hv1 : v ≤ 1) (hg : 1 ≤ g) (hq : 0 < q)
    (hnX : 1 / n = X * w * v) (hqX : 1 / q ≤ X * w * v ^ 2)
    (hI : I ≤ Cm * X * w ^ 2 * v ^ 2) (hγ : γ = g * (1 / q + 1 / n))
    (hΛ0 : 0 ≤ Λ) (hΛγ : Λ ≤ γ) (hA : X ≤ Cm * A)
    (hε : 4 * Cm * (3 * Csc * l + Csc * Cm * l + 2 * Csc + Cm + 6) * (s ^ 18 * g * w) ≤ 1)
    (hSC : A * Λ ≤ Csc * (s ^ 2 * l / q ^ 2 + s ^ 4 * l * ((Λ + I) / n) + Λ ^ 2 / l) +
      Λ ^ 2 + Z)
    (hZ : Z ≤ s ^ 14 * (1 / q ^ 2 + 1 / n ^ 2 + s ^ 4 * (I + γ) / n)) :
    Λ ≤ X * w * v ^ 2 / 2 := by
  set ε := s ^ 18 * g * w with hεdef
  set T := X ^ 2 * w * v ^ 2 with hT
  have hCm0 : 0 < Cm := by linarith
  have hA0 : 0 < A := by
    by_contra h
    push Not at h
    nlinarith
  have hs2 : s ^ 2 ≤ s ^ 18 := pow_le_pow_right₀ hs (by norm_num)
  have hs4 : s ^ 4 ≤ s ^ 18 := pow_le_pow_right₀ hs (by norm_num)
  have hs14 : s ^ 14 ≤ s ^ 18 := pow_le_pow_right₀ hs (by norm_num)
  have hs0 : 0 < s := by linarith
  have hε0 : 0 < ε := by positivity
  have hk : ∀ k ≤ 18, s ^ k * w ≤ ε := by
    intro k hk18
    calc s ^ k * w ≤ s ^ 18 * w :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs hk18) hw.le
      _ = s ^ 18 * 1 * w := by ring
      _ ≤ s ^ 18 * g * w := by gcongr
  have hwε := hk 4 (by norm_num)
  have hwε' : w ≤ ε := by simpa using hk 0 (by norm_num)
  have hgwε : s ^ 18 * g * w = ε := rfl
  have hs14ε := hk 14 (by norm_num)
  have hs2ε := hk 2 (by norm_num)
  -- the inputs in terms of `X w v`
  have hq2 : 1 / q ^ 2 ≤ X ^ 2 * w ^ 2 * v ^ 4 := by
    have h0 : 0 ≤ 1 / q := by positivity
    have := pow_le_pow_left₀ h0 hqX 2
    rw [div_pow, one_pow] at this
    exact this.trans_eq (by ring)
  have hn2 : 1 / n ^ 2 = X ^ 2 * w ^ 2 * v ^ 2 := by
    rw [show 1 / n ^ 2 = (1 / n) ^ 2 by rw [div_pow, one_pow], hnX]
    ring
  have hv2 : v ^ 2 ≤ v := pow_le_of_le_one hv.le hv1 (by norm_num)
  have hwv : w * v ≤ 1 := by
    calc w * v ≤ 1 * v := mul_le_mul_of_nonneg_right hw1 hv.le
      _ ≤ 1 := by rw [one_mul]; exact hv1
  have hγle : γ ≤ 2 * g * (X * w * v) := by
    rw [hγ, hnX]
    have h1 : X * w * v ^ 2 ≤ X * w * v :=
      mul_le_mul_of_nonneg_left hv2 (by positivity)
    have hg0 : 0 ≤ g := by linarith
    have h2 := mul_le_mul_of_nonneg_left
      (add_le_add (hqX.trans h1) (le_refl (X * w * v))) hg0
    exact h2.trans_eq (by ring)
  have hγ0 : 0 ≤ γ := hΛ0.trans hΛγ
  have hΛ2 : Λ ^ 2 ≤ γ * Λ := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hΛγ hΛ0
  have hΛ2l : Λ ^ 2 / l ≤ Λ ^ 2 := div_le_self (sq_nonneg _) hl
  -- the six terms of the remainder, each at most a multiple of `ε T`
  have hT0 : 0 ≤ T := by positivity
  have hl0 : 0 ≤ l := by linarith
  have t1 : s ^ 2 * l / q ^ 2 ≤ l * (ε * T) := by
    have e : s ^ 2 * l / q ^ 2 = s ^ 2 * l * (1 / q ^ 2) := by ring
    rw [e]
    calc s ^ 2 * l * (1 / q ^ 2) ≤ s ^ 2 * l * (X ^ 2 * w ^ 2 * v ^ 4) :=
          mul_le_mul_of_nonneg_left hq2 (by positivity)
      _ = l * ((s ^ 2 * w) * v ^ 2) * T := by rw [hT]; ring
      _ ≤ l * (ε * 1) * T := by
          gcongr
          exact pow_le_one₀ hv.le hv1
      _ = l * (ε * T) := by ring
  have t2 : s ^ 4 * l * (I / n) ≤ Cm * l * (ε * T) := by
    have e : s ^ 4 * l * (I / n) = s ^ 4 * l * I * (1 / n) := by ring
    rw [e, hnX]
    calc s ^ 4 * l * I * (X * w * v) ≤ s ^ 4 * l * (Cm * X * w ^ 2 * v ^ 2) * (X * w * v) := by
          gcongr
      _ = Cm * l * ((s ^ 4 * w) * (w * v)) * T := by rw [hT]; ring
      _ ≤ Cm * l * (ε * 1) * T := by
          gcongr
      _ = Cm * l * (ε * T) := by ring
  have t3 : s ^ 14 * (1 / q ^ 2) ≤ ε * T := by
    calc s ^ 14 * (1 / q ^ 2) ≤ s ^ 14 * (X ^ 2 * w ^ 2 * v ^ 4) :=
          mul_le_mul_of_nonneg_left hq2 (by positivity)
      _ = ((s ^ 14 * w) * v ^ 2) * T := by rw [hT]; ring
      _ ≤ (ε * 1) * T := by
          gcongr
          exact pow_le_one₀ hv.le hv1
      _ = ε * T := by ring
  have t4 : s ^ 14 * (1 / n ^ 2) ≤ ε * T := by
    rw [hn2]
    calc s ^ 14 * (X ^ 2 * w ^ 2 * v ^ 2) = (s ^ 14 * w) * T := by rw [hT]; ring
      _ ≤ ε * T := by gcongr
  have t5 : s ^ 14 * (s ^ 4 * I / n) ≤ Cm * (ε * T) := by
    have e : s ^ 14 * (s ^ 4 * I / n) = s ^ 18 * I * (1 / n) := by ring
    rw [e, hnX]
    calc s ^ 18 * I * (X * w * v) ≤ s ^ 18 * (Cm * X * w ^ 2 * v ^ 2) * (X * w * v) := by
          gcongr
      _ = Cm * ((s ^ 18 * w) * (w * v)) * T := by rw [hT]; ring
      _ ≤ Cm * (ε * 1) * T := by
          gcongr
          exact hk 18 le_rfl
      _ = Cm * (ε * T) := by ring
  have t6 : s ^ 14 * (s ^ 4 * γ / n) ≤ 2 * (ε * T) := by
    have e : s ^ 14 * (s ^ 4 * γ / n) = s ^ 18 * γ * (1 / n) := by ring
    rw [e, hnX]
    calc s ^ 18 * γ * (X * w * v) ≤ s ^ 18 * (2 * g * (X * w * v)) * (X * w * v) := by
          gcongr
      _ = 2 * ((s ^ 18 * g * w) * T) := by rw [hT]; ring
      _ = 2 * (ε * T) := by rw [hgwε]
  -- the two terms linear in `Λ`
  have u1 : s ^ 4 * l * (Λ / n) ≤ l * ε * X * Λ := by
    have e : s ^ 4 * l * (Λ / n) = s ^ 4 * l * Λ * (1 / n) := by ring
    rw [e, hnX]
    calc s ^ 4 * l * Λ * (X * w * v) = l * ((s ^ 4 * w) * v) * X * Λ := by ring
      _ ≤ l * (ε * 1) * X * Λ := by
          gcongr
      _ = l * ε * X * Λ := by ring
  have u2 : γ * Λ ≤ 2 * ε * X * Λ := by
    calc γ * Λ ≤ (2 * g * (X * w * v)) * Λ := mul_le_mul_of_nonneg_right hγle hΛ0
      _ = 2 * ((s ^ 0 * g * w) * v) * X * Λ := by ring
      _ ≤ 2 * (ε * 1) * X * Λ := by
          gcongr
          rw [hεdef, pow_zero]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (one_le_pow₀ hs) (by linarith)) hw.le
      _ = 2 * ε * X * Λ := by ring
  -- assemble
  set B := 3 * Csc * l + Csc * Cm * l + 2 * Csc + Cm + 6 with hB
  have hBε : 4 * Cm * B * ε ≤ 1 := hε
  have hmain : A * Λ ≤ (Csc * l + Csc * Cm * l + Cm + 4) * (ε * T) +
      (Csc * l + 2 * Csc + 2) * ε * X * Λ := by
    have e1 : s ^ 4 * l * ((Λ + I) / n) = s ^ 4 * l * (Λ / n) + s ^ 4 * l * (I / n) := by ring
    have e2 : s ^ 14 * (1 / q ^ 2 + 1 / n ^ 2 + s ^ 4 * (I + γ) / n) =
        s ^ 14 * (1 / q ^ 2) + s ^ 14 * (1 / n ^ 2) + s ^ 14 * (s ^ 4 * I / n) +
          s ^ 14 * (s ^ 4 * γ / n) := by ring
    rw [e1] at hSC
    rw [e2] at hZ
    have hcl : Csc * (Λ ^ 2 / l) ≤ Csc * (γ * Λ) :=
      mul_le_mul_of_nonneg_left (hΛ2l.trans hΛ2) hCsc.le
    have k1 := mul_le_mul_of_nonneg_left t1 hCsc.le
    have k2 := mul_le_mul_of_nonneg_left t2 hCsc.le
    have k3 := mul_le_mul_of_nonneg_left u1 hCsc.le
    have k4 := mul_le_mul_of_nonneg_left u2 hCsc.le
    have k5 := hΛ2.trans u2
    have e3 : Csc * (s ^ 2 * l / q ^ 2 + (s ^ 4 * l * (Λ / n) + s ^ 4 * l * (I / n)) +
        Λ ^ 2 / l) = Csc * (s ^ 2 * l / q ^ 2) + Csc * (s ^ 4 * l * (Λ / n)) +
        Csc * (s ^ 4 * l * (I / n)) + Csc * (Λ ^ 2 / l) := by ring
    rw [e3] at hSC
    have e4 : (Csc * l + Csc * Cm * l + Cm + 4) * (ε * T) + (Csc * l + 2 * Csc + 2) * ε * X * Λ =
        Csc * (l * (ε * T)) + Csc * (l * ε * X * Λ) + Csc * (Cm * l * (ε * T)) +
          Csc * (2 * ε * X * Λ) + 2 * ε * X * Λ + (ε * T + ε * T + Cm * (ε * T) +
            2 * (ε * T)) := by ring
    rw [e4]
    linarith
  have hεB0 : 0 ≤ Cm * ε := by positivity
  have hb1 : Csc * l + 2 * Csc + 2 ≤ B := by
    rw [hB]
    linarith only [mul_nonneg (mul_nonneg hCsc.le hCm0.le) hl0, mul_nonneg hCsc.le hl0, hCm0]
  have hb2 : Csc * l + Csc * Cm * l + Cm + 4 ≤ B := by
    rw [hB]; linarith only [mul_nonneg hCsc.le hl0, hCsc]
  have hd1 : Cm * ((Csc * l + 2 * Csc + 2) * ε) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hb1 hεB0
    calc Cm * ((Csc * l + 2 * Csc + 2) * ε) = Cm * ε * (Csc * l + 2 * Csc + 2) := by ring
      _ ≤ Cm * ε * B := this
      _ = 4 * Cm * B * ε / 4 := by ring
      _ ≤ 1 / 4 := by linarith only [hBε]
  have hd2 : Cm * ((Csc * l + Csc * Cm * l + Cm + 4) * ε) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hb2 hεB0
    calc Cm * ((Csc * l + Csc * Cm * l + Cm + 4) * ε) =
        Cm * ε * (Csc * l + Csc * Cm * l + Cm + 4) := by ring
      _ ≤ Cm * ε * B := this
      _ = 4 * Cm * B * ε / 4 := by ring
      _ ≤ 1 / 4 := by linarith only [hBε]
  have hlin : (Csc * l + 2 * Csc + 2) * ε * X * Λ ≤ A * Λ / 4 := by
    have h0 : 0 ≤ (Csc * l + 2 * Csc + 2) * ε := by positivity
    calc (Csc * l + 2 * Csc + 2) * ε * X * Λ ≤ (Csc * l + 2 * Csc + 2) * ε * (Cm * A) * Λ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA h0) hΛ0
      _ = (Cm * ((Csc * l + 2 * Csc + 2) * ε)) * (A * Λ) := by ring
      _ ≤ (1 / 4) * (A * Λ) := mul_le_mul_of_nonneg_right hd1 (by positivity)
      _ = A * Λ / 4 := by ring
  have hTle : T ≤ Cm * A * (X * w * v ^ 2) := by
    have h0 : 0 ≤ X * w * v ^ 2 := by positivity
    calc T = X * (X * w * v ^ 2) := by rw [hT]; ring
      _ ≤ (Cm * A) * (X * w * v ^ 2) := mul_le_mul_of_nonneg_right hA h0
  have hrem : (Csc * l + Csc * Cm * l + Cm + 4) * (ε * T) ≤ A * (X * w * v ^ 2) / 4 := by
    have h0 : 0 ≤ (Csc * l + Csc * Cm * l + Cm + 4) * ε := by positivity
    calc (Csc * l + Csc * Cm * l + Cm + 4) * (ε * T)
        = ((Csc * l + Csc * Cm * l + Cm + 4) * ε) * T := by ring
      _ ≤ ((Csc * l + Csc * Cm * l + Cm + 4) * ε) * (Cm * A * (X * w * v ^ 2)) :=
          mul_le_mul_of_nonneg_left hTle h0
      _ = (Cm * ((Csc * l + Csc * Cm * l + Cm + 4) * ε)) * (A * (X * w * v ^ 2)) := by ring
      _ ≤ (1 / 4) * (A * (X * w * v ^ 2)) :=
          mul_le_mul_of_nonneg_right hd2 (by positivity)
      _ = A * (X * w * v ^ 2) / 4 := by ring
  have hfin : A * Λ ≤ A * (X * w * v ^ 2 / 2) := by
    have h0 : 0 ≤ A * (X * w * v ^ 2) := by positivity
    have e : A * (X * w * v ^ 2 / 2) = A * (X * w * v ^ 2) / 2 := by ring
    rw [e]
    linarith only [hmain, hlin, hrem, h0]
  exact le_of_mul_le_mul_left hfin hA0

/-! ### The window (4.36) of [15] -/

/-- On the window `2 + A² V⁴ P² (q⁻² + R) ≤ |E| ≤ 3` (with `R³ N² = 1`, the window of (4.36) of
[15] for `C = 2K + 4a + 2`, `A = φ^K`, `V = φ^a`, `P = φ`), `κ = |E| - 2 ∈ (0, 1]`,
`q⁻¹ ≤ √κ / (A V²)`, `A³ V³ ≤ N κ √κ` and `N⁻¹ ≤ (√κ / (A V²))²`. -/
private lemma outside_window {N : ℕ} {P A V q E R : ℝ} (hN : (0 : ℝ) < N) (hP : 1 ≤ P)
    (hA : 1 ≤ A) (hV : 1 ≤ V) (hq : 0 < q) (hR0 : 0 ≤ R) (hR3 : R ^ 3 * (N : ℝ) ^ 2 = 1)
    (hRN : (N : ℝ)⁻¹ ≤ R) (hwin : 2 + A ^ 2 * V ^ 4 * P ^ 2 * (1 / q ^ 2 + R) ≤ |E|)
    (hE3 : |E| ≤ 3) :
    kappa E = |E| - 2 ∧ 0 < Real.sqrt (kappa E) ∧ Real.sqrt (kappa E) ≤ 1 ∧
      1 / q ≤ Real.sqrt (kappa E) / (A * V ^ 2) ∧
      A ^ 3 * V ^ 3 ≤ N * kappa E * Real.sqrt (kappa E) ∧
      (N : ℝ)⁻¹ ≤ (Real.sqrt (kappa E) / (A * V ^ 2)) ^ 2 := by
  have hq2 : 0 < 1 / q ^ 2 := by positivity
  have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP
  have hV4 : 1 ≤ V ^ 4 := one_le_pow₀ hV
  have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA
  have hAVP : 1 ≤ A ^ 2 * V ^ 4 * P ^ 2 := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hA2 hV4) hP2
  have hW : 0 < A ^ 2 * V ^ 4 * P ^ 2 * (1 / q ^ 2 + R) := by positivity
  have hκ : kappa E = |E| - 2 := by
    unfold kappa
    exact abs_of_nonneg (by linarith)
  set κ := kappa E with hκdef
  have hκW : A ^ 2 * V ^ 4 * P ^ 2 * (1 / q ^ 2 + R) ≤ κ := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : κ ≤ 1 := by linarith
  set X := Real.sqrt κ with hX
  have hX0 : 0 < X := Real.sqrt_pos.mpr hκ0
  have hX2 : X ^ 2 = κ := Real.sq_sqrt hκ0.le
  have hX1 : X ≤ 1 := Real.sqrt_le_one.mpr hκ1
  have hAV : 0 < A * V ^ 2 := by positivity
  -- the two halves of the window
  have hκq : A ^ 2 * V ^ 4 * (1 / q ^ 2) ≤ κ := by
    have h1 : A ^ 2 * V ^ 4 * (1 / q ^ 2) ≤ A ^ 2 * V ^ 4 * P ^ 2 * (1 / q ^ 2) := by
      have : 0 ≤ A ^ 2 * V ^ 4 * (1 / q ^ 2) := by positivity
      nlinarith
    have h2 : A ^ 2 * V ^ 4 * P ^ 2 * (1 / q ^ 2) ≤ A ^ 2 * V ^ 4 * P ^ 2 * (1 / q ^ 2 + R) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hκR : A ^ 2 * V ^ 4 * P ^ 2 * R ≤ κ := by
    have h2 : A ^ 2 * V ^ 4 * P ^ 2 * R ≤ A ^ 2 * V ^ 4 * P ^ 2 * (1 / q ^ 2 + R) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  refine ⟨hκ, hX0, hX1, ?_, ?_, ?_⟩
  · have h0 : 0 ≤ 1 / q := by positivity
    have h1 : 0 ≤ X / (A * V ^ 2) := by positivity
    rw [← pow_le_pow_iff_left₀ h0 h1 (by norm_num : (2 : ℕ) ≠ 0)]
    rw [div_pow, div_pow, one_pow, hX2, le_div_iff₀ (by positivity)]
    calc 1 / q ^ 2 * (A * V ^ 2) ^ 2 = A ^ 2 * V ^ 4 * (1 / q ^ 2) := by ring
      _ ≤ κ := hκq
  · have h0 : 0 ≤ A ^ 3 * V ^ 3 := by positivity
    have h1 : 0 ≤ N * κ * X := by positivity
    rw [← pow_le_pow_iff_left₀ h0 h1 (by norm_num : (2 : ℕ) ≠ 0)]
    have e : (N * κ * X) ^ 2 = (N : ℝ) ^ 2 * κ ^ 3 := by
      rw [mul_pow, hX2, mul_pow]; ring
    rw [e]
    have hc : (A ^ 2 * V ^ 4 * P ^ 2 * R) ^ 3 ≤ κ ^ 3 :=
      pow_le_pow_left₀ (by positivity) hκR 3
    have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
    have e2 : (N : ℝ) ^ 2 * (A ^ 2 * V ^ 4 * P ^ 2 * R) ^ 3 = A ^ 6 * V ^ 12 * P ^ 6 := by
      have : (N : ℝ) ^ 2 * (A ^ 2 * V ^ 4 * P ^ 2 * R) ^ 3 =
          A ^ 6 * V ^ 12 * P ^ 6 * (R ^ 3 * (N : ℝ) ^ 2) := by ring
      rw [this, hR3, mul_one]
    have h3 : (A ^ 3 * V ^ 3) ^ 2 ≤ A ^ 6 * V ^ 12 * P ^ 6 := by
      have hV6 : 1 ≤ V ^ 6 := one_le_pow₀ hV
      have hP6 : 1 ≤ P ^ 6 := one_le_pow₀ hP
      have h0' : 0 ≤ A ^ 6 * V ^ 6 := by positivity
      calc (A ^ 3 * V ^ 3) ^ 2 = A ^ 6 * V ^ 6 * 1 * 1 := by ring
        _ ≤ A ^ 6 * V ^ 6 * V ^ 6 * P ^ 6 := by gcongr
        _ = A ^ 6 * V ^ 12 * P ^ 6 := by ring
    calc (A ^ 3 * V ^ 3) ^ 2 ≤ A ^ 6 * V ^ 12 * P ^ 6 := h3
      _ = (N : ℝ) ^ 2 * (A ^ 2 * V ^ 4 * P ^ 2 * R) ^ 3 := e2.symm
      _ ≤ (N : ℝ) ^ 2 * κ ^ 3 := mul_le_mul_of_nonneg_left hc hN2
  · rw [div_pow, hX2, le_div_iff₀ (by positivity)]
    have h1 : R ≤ A ^ 2 * V ^ 4 * P ^ 2 * R := le_mul_of_one_le_left hR0 hAVP
    calc (N : ℝ)⁻¹ * (A * V ^ 2) ^ 2 = A ^ 2 * V ^ 4 * (N : ℝ)⁻¹ := by ring
      _ ≤ A ^ 2 * V ^ 4 * R := mul_le_mul_of_nonneg_left hRN (by positivity)
      _ ≤ A ^ 2 * V ^ 4 * P ^ 2 * R := by
          have : 0 ≤ A ^ 2 * V ^ 4 * R := by positivity
          nlinarith
      _ ≤ κ := hκR

/-! ### The bound at one point of the window -/

/-- From (3.40) of [15]: `|1 - m_sc²| |v| ≤ |(1 - m_sc²) v - m_sc³ v² - m_sc² [Z]| + |v|² + |[Z]|`
when `|m_sc| ≤ 1`. -/
private lemma outside_sc_norm {α M v Zc : ℂ} {R : ℝ} (hM : ‖M‖ ≤ 1)
    (h : ‖α * v - M ^ 3 * v ^ 2 - M ^ 2 * Zc‖ ≤ R) : ‖α‖ * ‖v‖ ≤ R + ‖v‖ ^ 2 + ‖Zc‖ := by
  have e : α * v = (α * v - M ^ 3 * v ^ 2 - M ^ 2 * Zc) + M ^ 3 * v ^ 2 + M ^ 2 * Zc := by ring
  have h3 : ‖M ^ 3 * v ^ 2‖ ≤ ‖v‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow]
    have : ‖M‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hM
    nlinarith [sq_nonneg ‖v‖, pow_nonneg (norm_nonneg M) 3]
  have h2 : ‖M ^ 2 * Zc‖ ≤ ‖Zc‖ := by
    rw [norm_mul, norm_pow]
    have : ‖M‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hM
    nlinarith [norm_nonneg Zc, pow_nonneg (norm_nonneg M) 2]
  rw [← norm_mul, e]
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (α * v - M ^ 3 * v ^ 2 - M ^ 2 * Zc) (M ^ 3 * v ^ 2)
  linarith

/-- (4.40)–(4.46) of [15] at one point `z = E + iη` of the window, with `η = A V / (N √κ)`:
on `Λ ≤ γ`, the self-consistent equation (3.40) and the fluctuation averaging bound (4.2),
`Λ ≤ τ / 2` and `Im m_sc ≤ τ / 4`, where `τ = √κ / (A V²) = (V N η)⁻¹`. -/
private lemma outside_point {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {Cm Cs s g q A V E η : ℝ}
    (hN3 : 3 ≤ N) (hCm : 1 ≤ Cm) (hCs : 0 < Cs) (hs : 1 ≤ s) (hg : 1 ≤ g)
    (hA : 1 ≤ A) (hV : 1 ≤ V) (hq : 0 < q)
    (hmsc : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 →
      (Cm⁻¹ ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ Cm) ∧
      (Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ ‖1 - msc z ^ 2‖ ∧
        ‖1 - msc z ^ 2‖ ≤ Cm * Real.sqrt (kappa z.re + z.im)) ∧
      (z.im ≤ kappa z.re → 2 ≤ |z.re| →
        Cm⁻¹ * (z.im / Real.sqrt (kappa z.re + z.im)) ≤ (msc z).im ∧
        (msc z).im ≤ Cm * (z.im / Real.sqrt (kappa z.re + z.im))) ∧
      (kappa z.re ≤ z.im ∨ |z.re| ≤ 2 →
        Cm⁻¹ * Real.sqrt (kappa z.re + z.im) ≤ (msc z).im ∧
        (msc z).im ≤ Cm * Real.sqrt (kappa z.re + z.im)))
    (hE2 : 2 ≤ |E|) (hE3 : |E| ≤ 3) (hX0 : 0 < Real.sqrt (kappa E))
    (hX1 : Real.sqrt (kappa E) ≤ 1) (hqX : 1 / q ≤ Real.sqrt (kappa E) / (A * V ^ 2))
    (hNk : A ^ 3 * V ^ 3 ≤ N * kappa E * Real.sqrt (kappa E))
    (hη : η = A * V / (N * Real.sqrt (kappa E)))
    (hε : 4 * Cm * (3 * Cs * Real.log N + Cs * Cm * Real.log N + 2 * Cs + Cm + 6) *
      (s ^ 18 * g * A⁻¹) ≤ 1)
    (hLL : lamAvg H ⟨E, η⟩ ≤ g * (1 / q + 1 / (N * η)))
    (hSC : ‖(1 - msc ⟨E, η⟩ ^ 2) * (stieltjesM H ⟨E, η⟩ - msc ⟨E, η⟩) -
        msc ⟨E, η⟩ ^ 3 * (stieltjesM H ⟨E, η⟩ - msc ⟨E, η⟩) ^ 2 -
        msc ⟨E, η⟩ ^ 2 * zAvg H ⟨E, η⟩‖ ≤
      Cs * (s ^ 2 * Real.log N / q ^ 2 + s ^ 4 * Real.log N * psiCtrl H ⟨E, η⟩ ^ 2 +
        lamAvg H ⟨E, η⟩ ^ 2 / Real.log N))
    (hFA : ‖zAvg H ⟨E, η⟩‖ ≤ s ^ 14 * (1 / q ^ 2 + 1 / (N * η) ^ 2 +
      s ^ 4 * ((msc ⟨E, η⟩).im + g * (1 / q + 1 / (N * η))) / (N * η))) :
    lamAvg H ⟨E, η⟩ ≤ Real.sqrt (kappa E) / (A * V ^ 2) / 2 ∧
      (msc ⟨E, η⟩).im ≤ Real.sqrt (kappa E) / (A * V ^ 2) / 4 := by
  set X := Real.sqrt (kappa E) with hXdef
  set z : ℂ := ⟨E, η⟩ with hz
  have hN : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hl : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    linarith
  have hκ0 : 0 ≤ kappa E := abs_nonneg _
  have hκX : kappa E = X ^ 2 := (Real.sq_sqrt hκ0).symm
  have hA0 : 0 < A := by linarith
  have hV0 : 0 < V := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  -- `η ≤ κ ≤ 1`
  have hAV : A * V ≤ A ^ 3 * V ^ 3 := by
    have h1 : 1 ≤ A ^ 2 * V ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) (one_le_pow₀ hV)
    have h0 : 0 ≤ A * V := by positivity
    calc A * V = A * V * 1 := by ring
      _ ≤ A * V * (A ^ 2 * V ^ 2) := mul_le_mul_of_nonneg_left h1 h0
      _ = A ^ 3 * V ^ 3 := by ring
  have hηκ : η ≤ kappa E := by
    rw [hη, div_le_iff₀ (by positivity)]
    calc A * V ≤ A ^ 3 * V ^ 3 := hAV
      _ ≤ N * kappa E * X := hNk
      _ = kappa E * (N * X) := by ring
  have hκ1 : kappa E ≤ 1 := by
    rw [hκX]; nlinarith
  have hzre : z.re = E := rfl
  have hzim : z.im = η := rfl
  obtain ⟨⟨-, hM⟩, ⟨hα, -⟩, hI3, -⟩ := hmsc z (by rw [hzre]; linarith) (by rw [hzim]; exact hη0)
    (by rw [hzim]; linarith)
  rw [hzre, hzim] at hα hI3
  have hMle : ‖msc z‖ ≤ 1 := (norm_msc_eq_inv_and_lt_one (by rw [hzim]; exact hη0)).2.le
  have hXle : X ≤ Real.sqrt (kappa E + η) := Real.sqrt_le_sqrt (by linarith)
  have hAα : X ≤ Cm * ‖1 - msc z ^ 2‖ := by
    have hCm0 : 0 < Cm := by linarith
    have := mul_le_mul_of_nonneg_left hα hCm0.le
    rw [← mul_assoc, mul_inv_cancel₀ hCm0.ne', one_mul] at this
    linarith
  -- `Im m_sc ≤ C_m η / √κ ≤ C_m X / (A V)²`
  have hI : (msc z).im ≤ Cm * X * A⁻¹ ^ 2 * V⁻¹ ^ 2 := by
    have h1 := (hI3 hηκ hE2).2
    have h2 : η / Real.sqrt (kappa E + η) ≤ η / X := div_le_div_of_nonneg_left hη0.le hX0 hXle
    have h3 : η / X ≤ X * A⁻¹ ^ 2 * V⁻¹ ^ 2 := by
      rw [hη, div_div, div_le_iff₀ (by positivity)]
      have e : X * A⁻¹ ^ 2 * V⁻¹ ^ 2 * (N * X * X) = (N * kappa E * X) / (A ^ 2 * V ^ 2) := by
        rw [hκX]; field_simp
      rw [e, le_div_iff₀ (by positivity)]
      calc A * V * (A ^ 2 * V ^ 2) = A ^ 3 * V ^ 3 := by ring
        _ ≤ N * kappa E * X := hNk
    calc (msc z).im ≤ Cm * (η / Real.sqrt (kappa E + η)) := h1
      _ ≤ Cm * (X * A⁻¹ ^ 2 * V⁻¹ ^ 2) := mul_le_mul_of_nonneg_left (h2.trans h3) (by linarith)
      _ = Cm * X * A⁻¹ ^ 2 * V⁻¹ ^ 2 := by ring
  have hτ : X * A⁻¹ * V⁻¹ ^ 2 = X / (A * V ^ 2) := by field_simp
  have hnX : 1 / (N * η) = X * A⁻¹ * V⁻¹ := by
    rw [hη]; field_simp
  have hqX' : 1 / q ≤ X * A⁻¹ * V⁻¹ ^ 2 := by rw [hτ]; exact hqX
  have hψ : psiCtrl H z ^ 2 = (lamAvg H z + (msc z).im) / (N * η) := by
    unfold psiCtrl
    rw [Real.sq_sqrt]
    have : 0 ≤ (msc z).im := (im_msc_pos (by rw [hzim]; exact hη0)).le
    have : 0 ≤ lamAvg H z := norm_nonneg _
    have : 0 < z.im := hη0
    positivity
  have hSC' := outside_sc_norm hMle hSC
  rw [hψ] at hSC'
  have hcore := outside_core (Cm := Cm) (Csc := Cs) (s := s) (l := Real.log N) (q := q)
    (n := N * η) (X := X) (w := A⁻¹) (v := V⁻¹) (g := g) (I := (msc z).im)
    (γ := g * (1 / q + 1 / (N * η))) (Λ := lamAvg H z) (A := ‖1 - msc z ^ 2‖)
    (Z := ‖zAvg H z‖) hCm hCs hs hl hX0 (by positivity) (inv_le_one_of_one_le₀ hA)
    (by positivity) (inv_le_one_of_one_le₀ hV) hg hq hnX hqX' hI rfl (norm_nonneg _) hLL hAα
    hε (by unfold lamAvg; exact hSC') hFA
  refine ⟨by rw [← hτ]; exact hcore, ?_⟩
  -- `4 C_m ≤ A`
  have h4 : 4 * Cm ≤ A := by
    have hsg : 1 ≤ s ^ 18 * g := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs) hg
    have hB : 4 * Cm * 1 ≤
        4 * Cm * (3 * Cs * Real.log N + Cs * Cm * Real.log N + 2 * Cs + Cm + 6) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have : 0 ≤ Cs * Real.log N := by positivity
      have : 0 ≤ Cs * Cm * Real.log N := by positivity
      linarith
    have h1 : 4 * Cm * (s ^ 18 * g * A⁻¹) ≤ 1 := by
      refine le_trans ?_ hε
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h2 : 4 * Cm * A⁻¹ ≤ 1 := by
      refine le_trans ?_ h1
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      calc A⁻¹ = 1 * 1 * A⁻¹ := by ring
        _ ≤ s ^ 18 * g * A⁻¹ := by
            gcongr
            · exact one_le_pow₀ hs
    rw [mul_inv_le_iff₀ hA0] at h2
    linarith
  calc (msc z).im ≤ Cm * X * A⁻¹ ^ 2 * V⁻¹ ^ 2 := hI
    _ = X / (A * V ^ 2) * (Cm * A⁻¹) := by field_simp
    _ ≤ X / (A * V ^ 2) * (1 / 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_inv_le_iff₀ hA0]; linarith
    _ = X / (A * V ^ 2) / 4 := by ring

/-! ### From the grid to the whole window -/

/-- Points `±(b + k N⁻³)`, `k ≤ N³`, of the window `b ≤ |E| ≤ 3`. -/
private def outsideGrid (N : ℕ) (b : ℝ) : Finset (ℕ × Bool) :=
  ((Finset.range (N ^ 3 + 1)) ×ˢ (Finset.univ : Finset Bool)).filter
    (fun p => b + p.1 * ((N : ℝ) ^ 3)⁻¹ ≤ 3)

/-- The energy of a grid point. -/
private def outsideGridE (N : ℕ) (b : ℝ) (p : ℕ × Bool) : ℝ :=
  if p.2 then b + p.1 * ((N : ℝ) ^ 3)⁻¹ else -(b + p.1 * ((N : ℝ) ^ 3)⁻¹)

private lemma outsideGrid_card (N : ℕ) (b : ℝ) :
    ((outsideGrid N b).card : ℝ) ≤ 2 * ((N : ℝ) ^ 3 + 1) := by
  unfold outsideGrid
  have h := Finset.card_filter_le ((Finset.range (N ^ 3 + 1)) ×ˢ (Finset.univ : Finset Bool))
    (fun p => b + p.1 * ((N : ℝ) ^ 3)⁻¹ ≤ 3)
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool] at h
  have h' : ((Finset.filter (fun p : ℕ × Bool => b + p.1 * ((N : ℝ) ^ 3)⁻¹ ≤ 3)
      ((Finset.range (N ^ 3 + 1)) ×ˢ (Finset.univ : Finset Bool))).card : ℝ) ≤
      (((N ^ 3 + 1) * 2 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

private lemma outsideGridE_abs {N : ℕ} {b : ℝ} (hb : 0 ≤ b) (p : ℕ × Bool) :
    |outsideGridE N b p| = b + p.1 * ((N : ℝ) ^ 3)⁻¹ := by
  have h0 : 0 ≤ b + p.1 * ((N : ℝ) ^ 3)⁻¹ := by positivity
  unfold outsideGridE
  split_ifs
  · exact abs_of_nonneg h0
  · rw [abs_neg]; exact abs_of_nonneg h0

/-- Every point of the window is within `N⁻³` of a grid point closer to the edge. -/
private lemma outside_grid {N : ℕ} (hN : 1 ≤ N) {b E : ℝ} (hb : 2 ≤ b) (hbE : b ≤ |E|)
    (hE3 : |E| ≤ 3) : ∃ p ∈ outsideGrid N b,
      b ≤ |outsideGridE N b p| ∧ |outsideGridE N b p| ≤ 3 ∧ |outsideGridE N b p| ≤ |E| ∧
      |E| - |outsideGridE N b p| ≤ ((N : ℝ) ^ 3)⁻¹ ∧
      |E - outsideGridE N b p| ≤ ((N : ℝ) ^ 3)⁻¹ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set δ : ℝ := ((N : ℝ) ^ 3)⁻¹ with hδ
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have hδ0 : 0 < δ := inv_pos.mpr hN3
  set x := (|E| - b) / δ with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hδ0.le
  set k := ⌊x⌋₊ with hk
  have hkx : (k : ℝ) ≤ x := Nat.floor_le hx0
  have hxk : x < k + 1 := Nat.lt_floor_add_one x
  have hxN : x ≤ (N : ℝ) ^ 3 := by
    rw [hx, div_le_iff₀ hδ0, hδ, mul_inv_cancel₀ hN3.ne']
    linarith
  have hkN : k < N ^ 3 + 1 := by
    have : x < ((N ^ 3 + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact (Nat.floor_lt hx0).mpr this
  have hkδ : (k : ℝ) * δ ≤ |E| - b := by
    have := mul_le_mul_of_nonneg_right hkx hδ0.le
    rwa [hx, div_mul_cancel₀ _ hδ0.ne'] at this
  have hkδ' : |E| - b < (k + 1) * δ := by
    have := mul_lt_mul_of_pos_right hxk hδ0
    rwa [hx, div_mul_cancel₀ _ hδ0.ne'] at this
  let p : ℕ × Bool := (k, decide (0 ≤ E))
  have habs : |outsideGridE N b p| = b + k * δ := outsideGridE_abs (by linarith) p
  have hmem : p ∈ outsideGrid N b := by
    unfold outsideGrid
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨hkN, Finset.mem_univ _⟩, ?_⟩
    change b + (k : ℝ) * δ ≤ 3
    linarith
  refine ⟨p, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [habs]; have : 0 ≤ (k : ℝ) * δ := by positivity
    linarith
  · rw [habs]; linarith
  · rw [habs]; linarith
  · rw [habs]; linarith
  · have hd : |E| - (b + k * δ) ≤ δ := by linarith
    have hd0 : 0 ≤ |E| - (b + k * δ) := by linarith
    unfold outsideGridE
    by_cases hE : 0 ≤ E
    · have h2 : p.2 = true := by simp [p, hE]
      simp only [h2, ↓reduceIte]
      rw [abs_of_nonneg hE] at hd hd0
      rw [abs_le]; constructor <;> linarith
    · have h2 : p.2 = false := by simp [p, hE]
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
      push Not at hE
      rw [abs_of_neg hE] at hd hd0
      rw [abs_le]; constructor <;> linarith

/-- `η = a / (N √κ)` moves by at most `N⁻³` between `κ_p ≤ κ ≤ κ_p + N⁻³` when `a ≤ N κ_p^{3/2}`. -/
private lemma outside_eta_diff {N : ℕ} (hN : (0 : ℝ) < N) {a x y δ : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxy : x ≤ y) (hd : y ^ 2 - x ^ 2 ≤ δ) (haN : a ≤ N * x ^ 2 * x) :
    0 ≤ a / (N * x) - a / (N * y) ∧ a / (N * x) - a / (N * y) ≤ δ := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have e : a / (N * x) - a / (N * y) = a * (y - x) / (N * x * y) := by
    field_simp
  rw [e]
  have hyx : 0 ≤ y - x := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have h1 : x * (y - x) ≤ δ / 2 := by nlinarith
  have h2 : a * (y - x) ≤ N * x ^ 2 * y * (y - x) := by
    apply mul_le_mul_of_nonneg_right _ hyx
    calc a ≤ N * x ^ 2 * x := haN
      _ ≤ N * x ^ 2 * y := by gcongr
  have hδ0 : 0 ≤ δ := by nlinarith
  calc a * (y - x) ≤ N * x ^ 2 * y * (y - x) := h2
    _ = (N * x * y) * (x * (y - x)) := by ring
    _ ≤ (N * x * y) * (δ / 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ δ * (N * x * y) := by nlinarith [mul_pos (mul_pos hN hx) hy]

/-- Transfer from a grid point `z' = E' + iη'` to `z = E + iη` within `N⁻³` in both coordinates,
when `η, η' ≥ N⁻¹`, `N ≥ 256` and `τ'² ≥ N⁻¹`. -/
private lemma outside_transfer {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian)
    (hN : 256 ≤ N) {E E' η η' τ τ' : ℝ} (hη : (N : ℝ)⁻¹ ≤ η) (hη' : (N : ℝ)⁻¹ ≤ η')
    (hdE : |E - E'| ≤ ((N : ℝ) ^ 3)⁻¹) (hdη : |η - η'| ≤ ((N : ℝ) ^ 3)⁻¹)
    (hτ' : (N : ℝ)⁻¹ ≤ τ' ^ 2) (hτ'0 : 0 ≤ τ') (hττ : τ' ≤ τ)
    (hΛ' : lamAvg H ⟨E', η'⟩ ≤ τ' / 2) (hI' : (msc ⟨E', η'⟩).im ≤ τ' / 4) :
    lamAvg H ⟨E, η⟩ ≤ τ ∧ (stieltjesM H ⟨E, η⟩).im ≤ τ := by
  have hN1 : (256 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by omega
  have hη0 : 0 < η := lt_of_lt_of_le (inv_pos.mpr hN0) hη
  have hη'0 : 0 < η' := lt_of_lt_of_le (inv_pos.mpr hN0) hη'
  set z : ℂ := ⟨E, η⟩
  set w : ℂ := ⟨E', η'⟩
  have hzw : ‖z - w‖ ≤ 2 * ((N : ℝ) ^ 3)⁻¹ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [z, w, Complex.sub_re, Complex.sub_im]
    linarith
  have hL : ‖z - w‖ / (z.im * w.im) ≤ 2 / N := by
    have hden : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤ z.im * w.im :=
      mul_le_mul hη hη' (by positivity) hη0.le
    calc ‖z - w‖ / (z.im * w.im) ≤ 2 * ((N : ℝ) ^ 3)⁻¹ / ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) :=
          div_le_div₀ (by positivity) hzw (by positivity) hden
      _ = 2 / N := by field_simp
  have hτN : 16 / (N : ℝ) ≤ τ' := by
    have h1 : (16 / (N : ℝ)) ^ 2 ≤ τ' ^ 2 := by
      refine le_trans ?_ hτ'
      rw [div_pow, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hτ'0 (by norm_num : (2 : ℕ) ≠ 0)).mp h1
  have hL' : ‖z - w‖ / (z.im * w.im) ≤ τ' / 8 := by
    refine hL.trans ?_
    have : 2 / (N : ℝ) = (16 / N) / 8 := by ring
    rw [this]; linarith
  have h1 := weak_lamAvg_le_add hNpos hH (z := z) (w := w) hη0 hη'0
  have h2 := weak_norm_stieltjesM_sub_le hNpos hH (z := z) (w := w) hη0 hη'0
  refine ⟨by linarith, ?_⟩
  have h3 : (stieltjesM H z).im ≤ (stieltjesM H w).im + ‖z - w‖ / (z.im * w.im) := by
    have := Complex.im_le_norm (stieltjesM H z - stieltjesM H w)
    rw [Complex.sub_im] at this
    linarith
  have h4 : (stieltjesM H w).im ≤ (msc w).im + lamAvg H w := by
    have := Complex.im_le_norm (stieltjesM H w - msc w)
    rw [Complex.sub_im] at this
    unfold lamAvg
    linarith
  linarith

/-! ### Large `N` and the union bound -/

/-- The conditions on `N` used below: `N ≥ 256`, `B (log N + 1) ≤ φ`, `3 ≤ φ^a` and
`B' (log N)³ ≤ φ`. -/
private lemma outside_eventually {a : ℝ} (ha : 0 < a) (B B' : ℝ) (hB' : 1 ≤ B') :
    ∀ᶠ N : ℕ in atTop, 256 ≤ N ∧ B * (Real.log N + 1) ≤ phi N ∧ 3 ≤ phi N ^ a ∧
      B' * Real.log N ^ 3 ≤ phi N := by
  filter_upwards [eventually_ge_atTop 256, eventually_mul_log_add_one_le_phi_rpow one_pos B,
    eventually_mul_log_add_one_le_phi_rpow ha 3,
    eventually_mul_log_add_one_le_phi_rpow (by norm_num : (0 : ℝ) < 1 / 3) B'] with N h256 h1 h2 h3
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hφ : 0 < phi N := sc_phi_pos h1.1
  refine ⟨h256, by simpa using h1.2, by nlinarith [h2.2], ?_⟩
  have hc : (phi N ^ ((1 : ℝ) / 3)) ^ 3 = phi N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hφ.le]; norm_num
  have h4 : (B' * (Real.log N + 1)) ^ 3 ≤ (phi N ^ ((1 : ℝ) / 3)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h3.2 3
  rw [hc] at h4
  have h5 : B' * Real.log N ^ 3 ≤ (B' * (Real.log N + 1)) ^ 3 := by
    have hB3 : B' ≤ B' ^ 3 := by nlinarith [one_le_pow₀ hB' (n := 2)]
    have hl3 : Real.log N ^ 3 ≤ (Real.log N + 1) ^ 3 := pow_le_pow_left₀ hl (by linarith) 3
    calc B' * Real.log N ^ 3 ≤ B' ^ 3 * (Real.log N + 1) ^ 3 :=
          mul_le_mul hB3 hl3 (by positivity) (by positivity)
      _ = (B' * (Real.log N + 1)) ^ 3 := by ring
  linarith

/-- `e₁ + e₂ + M (e₃ + e₄) ≤ e^{-c Q}` when every `eᵢ ≤ e^{-c P Q / ℓ²}`, `M ≤ 2 (N³ + 1)`,
`ℓ = log N ≥ 1`, `Q ≥ 1` and `(1 + 6/c) ℓ³ ≤ P`. -/
private lemma outside_union_exp {N : ℕ} (hN : 1 ≤ N) {c P Q M e1 e2 e3 e4 : ℝ} (hc : 0 < c)
    (hl : 1 ≤ Real.log N) (hQ : 1 ≤ Q) (hP : (1 + 6 / c) * Real.log N ^ 3 ≤ P)
    (hM : M ≤ 2 * ((N : ℝ) ^ 3 + 1)) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4)
    (h1 : e1 ≤ Real.exp (-c * (P * Q) / Real.log N ^ 2))
    (h2 : e2 ≤ Real.exp (-c * (P * Q) / Real.log N ^ 2))
    (h3 : e3 ≤ Real.exp (-c * (P * Q) / Real.log N ^ 2))
    (h4 : e4 ≤ Real.exp (-c * (P * Q) / Real.log N ^ 2)) :
    e1 + e2 + M * (e3 + e4) ≤ Real.exp (-c * Q) := by
  set l := Real.log N with hl_def
  set x := Real.exp (-c * (P * Q) / l ^ 2) with hx
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hsum : e1 + e2 + M * (e3 + e4) ≤ 10 * (N : ℝ) ^ 3 * x := by
    have hN3 : 1 ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
    have : M * (e3 + e4) ≤ (2 * ((N : ℝ) ^ 3 + 1)) * (2 * x) :=
      mul_le_mul hM (by linarith) (by linarith) (by positivity)
    nlinarith
  refine (hsum.trans ?_)
  have e10 : (10 : ℝ) * (N : ℝ) ^ 3 = Real.exp (Real.log 10 + 3 * l) := by
    rw [Real.exp_add, hl_def, show (3 : ℝ) * Real.log N = ((3 : ℕ) : ℝ) * Real.log N by norm_num,
      Real.exp_nat_mul, Real.exp_log hN0, Real.exp_log (by norm_num)]
  rw [e10, hx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl10 : Real.log 10 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e3]
    have h2 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    norm_num at h2
    linarith
  have hl0 : 0 < l := by linarith
  have hl2 : 0 < l ^ 2 := by positivity
  -- `c Q (P / l² - 1) ≥ 6 l`
  have hPl : (1 + 6 / c) * l ≤ P / l ^ 2 := by
    rw [le_div_iff₀ hl2]
    calc (1 + 6 / c) * l * l ^ 2 = (1 + 6 / c) * l ^ 3 := by ring
      _ ≤ P := hP
  have hkey : 6 * l ≤ c * (P / l ^ 2 - 1) := by
    have h6 : 6 / c * l * c = 6 * l := by field_simp
    have : 1 + 6 / c * l ≤ (1 + 6 / c) * l := by
      have : 0 ≤ 6 / c := by positivity
      nlinarith
    nlinarith
  have hkey2 : 6 * l ≤ c * Q * (P / l ^ 2 - 1) := by
    have h0 : 0 ≤ c * (P / l ^ 2 - 1) := by nlinarith
    nlinarith
  have e : -c * (P * Q) / l ^ 2 = -(c * Q * (P / l ^ 2 - 1)) - c * Q := by
    field_simp
    ring
  rw [e]
  nlinarith

/-- `η = A V / (N X)` with `X = √κ ≤ 1` and `A³ V³ ≤ N κ X`: `0 < η ≤ κ`, `N⁻¹ ≤ η`,
`Y / N < η` for `Y ≤ A`, and `A V ≤ N X³`. -/
private lemma outside_eta_facts {N : ℕ} {A V X κ Y : ℝ} (hN0 : (0 : ℝ) < N) (hA : 1 ≤ A)
    (hV : 1 < V) (hX0 : 0 < X) (hX1 : X ≤ 1) (hκX : κ = X ^ 2) (hNk : A ^ 3 * V ^ 3 ≤ N * κ * X)
    (hY : Y ≤ A) :
    0 < A * V / (N * X) ∧ A * V / (N * X) ≤ κ ∧ (N : ℝ)⁻¹ ≤ A * V / (N * X) ∧
      Y / N < A * V / (N * X) ∧ A * V ≤ N * X ^ 2 * X := by
  have hA0 : 0 < A := by linarith
  have hV0 : 0 < V := by linarith
  have hAV : A * V ≤ A ^ 3 * V ^ 3 := by
    have h1 : 1 ≤ A ^ 2 * V ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) (one_le_pow₀ hV.le)
    have h0 : 0 ≤ A * V := by positivity
    calc A * V = A * V * 1 := by ring
      _ ≤ A * V * (A ^ 2 * V ^ 2) := mul_le_mul_of_nonneg_left h1 h0
      _ = A ^ 3 * V ^ 3 := by ring
  have hAVN : A * V ≤ N * X ^ 2 * X := by rw [← hκX]; linarith
  refine ⟨by positivity, ?_, ?_, ?_, hAVN⟩
  · rw [div_le_iff₀ (by positivity)]
    calc A * V ≤ N * κ * X := hAV.trans hNk
      _ = κ * (N * X) := by ring
  · rw [le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hN0]
    have h1 : 1 ≤ A * V := one_le_mul_of_one_le_of_one_le hA hV.le
    nlinarith
  · rw [div_lt_div_iff₀ hN0 (by positivity)]
    have h1 : Y * X ≤ A * 1 := mul_le_mul hY hX1 hX0.le (by linarith)
    have h2 : A < A * V := lt_mul_of_one_lt_right hA0 hV
    nlinarith

/-- `γ = g (q⁻¹ + n⁻¹) ≤ s⁻¹` when `q⁻¹, n⁻¹ ≤ A⁻¹` and `s^18 g / A ≤ 1/24`. -/
private lemma outside_gamma {A s g q n : ℝ} (hA0 : 0 < A) (hs1 : 1 ≤ s) (hg : 0 ≤ g)
    (hsg : s ^ 18 * g * A⁻¹ ≤ 1 / 24) (hqA : 1 / q ≤ A⁻¹) (hnA : 1 / n ≤ A⁻¹) :
    g * (1 / q + 1 / n) ≤ s⁻¹ := by
  have hs0 : 0 < s := by linarith
  have h1 : g * (1 / q + 1 / n) ≤ 2 * (g * A⁻¹) := by
    have := mul_le_mul_of_nonneg_left (add_le_add hqA hnA) hg
    linarith
  have h2 : s * (g * A⁻¹) ≤ s ^ 18 * g * A⁻¹ := by
    have hgA : 0 ≤ g * A⁻¹ := by positivity
    have : s ≤ s ^ 18 := by
      calc s = s ^ 1 := (pow_one s).symm
        _ ≤ s ^ 18 := pow_le_pow_right₀ hs1 (by norm_num)
    calc s * (g * A⁻¹) ≤ s ^ 18 * (g * A⁻¹) := mul_le_mul_of_nonneg_right this hgA
      _ = s ^ 18 * g * A⁻¹ := by ring
  rw [← one_div, le_div_iff₀ hs0]
  have h3 : g * (1 / q + 1 / n) * s ≤ 2 * (g * A⁻¹) * s := mul_le_mul_of_nonneg_right h1 hs0.le
  have e : 2 * (g * A⁻¹) * s = 2 * (s * (g * A⁻¹)) := by ring
  linarith only [h3, e, h2, hsg]

/-! ### The theorem -/

/-- (4.31)–(4.46) of [15] with the offset `K` and the exponent `a` (first two parts of (3.8) and
the eigenvalue exclusion), for almost surely bounded entries. -/
theorem outside_boundedAS {ζ C0 : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) :
    ∃ K > 0, ∀ a > 0, ∃ C > 0, ∃ c > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ (L : EntryLaws N) (q : ℝ),
      L.IsGenWigner C0 → L.BoundedSupportAS q → phi N ^ C ≤ q →
      L.law (outsideEvent N K a C q)ᶜ ≤ ENNReal.ofReal (Real.exp (-c * phi N ^ ζ)) := by
  classical
  have hζ1 : 0 < ζ + 1 := by linarith
  obtain ⟨Cl, hCl, cl, hcl, Nl, hLL⟩ := localLaw_boundedAS hζ1 hC0
  obtain ⟨Kw, hKw, cw, hcw, Nw, hW⟩ := weakLocalLaw_omega hζ1 hC0
  obtain ⟨Ks, hKs, Cs, hCs, cs, hcs, Ns, hSC⟩ := selfConsistent_on_omega hζ1 hC0
  obtain ⟨Kf, hKf, hFA0⟩ := fluctuation_averaging hζ1 hC0
  obtain ⟨cf, hcf, Nf, hFA⟩ := hFA0 cl hcl
  obtain ⟨Cm, hCm, hmsc⟩ := msc_bounds
  set K : ℝ := Cl + Kw + Ks + Kf + 18 * (ζ + 1) + 1 with hK
  refine ⟨K, by rw [hK]; linarith, fun a ha => ?_⟩
  set C : ℝ := 2 * K + 4 * a + 2 with hC
  set c0 : ℝ := min (min cl cw) (min cs cf) with hc0
  have hc00 : 0 < c0 := lt_min (lt_min hcl hcw) (lt_min hcs hcf)
  set B : ℝ := 4 * Cm * (3 * Cs + Cs * Cm + 2 * Cs + Cm + 6) with hB
  have hB' : 1 ≤ 1 + 6 / c0 := by
    have : 0 ≤ 6 / c0 := by positivity
    linarith
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (outside_eventually ha B (1 + 6 / c0) hB')
  have hK0 : 0 < K := by rw [hK]; linarith
  refine ⟨C, by rw [hC]; linarith, c0, hc00, max N1 (max (max Nl Nw) (max Ns Nf)), ?_⟩
  intro N hN L q hL hqBS hqC
  obtain ⟨h256, hBφ, h3a, hφl⟩ := hN1 N (le_of_max_le_left hN)
  have hNl : Nl ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_of_max_le_right hN))
  have hNw : Nw ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_of_max_le_right hN))
  have hNs : Ns ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_of_max_le_right hN))
  have hNf : Nf ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_of_max_le_right hN))
  have hN3 : 3 ≤ N := by omega
  have hN1' : 1 ≤ N := by omega
  have hNr : (256 : ℝ) ≤ N := by exact_mod_cast h256
  have hN0 : (0 : ℝ) < N := by linarith
  have hl : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    linarith
  set l := Real.log N with hl_def
  set P := phi N with hP_def
  have hP1 : 1 ≤ P := sc_one_le_phi hN3
  have hP0 : 0 < P := by linarith
  have hCm0 : 0 < Cm := by linarith
  have hB24 : 24 ≤ B := by
    have h1 : 6 ≤ 3 * Cs + Cs * Cm + 2 * Cs + Cm + 6 := by
      have : 0 ≤ Cs * Cm := by positivity
      linarith only [this, hCs, hCm0]
    have h2 : 4 * 1 * 6 ≤ 4 * Cm * (3 * Cs + Cs * Cm + 2 * Cs + Cm + 6) :=
      mul_le_mul (by linarith only [hCm]) h1 (by norm_num) (by positivity)
    rw [hB]; linarith only [h2]
  have hP24 : 24 ≤ P := by
    have : B * 1 ≤ B * (Real.log N + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hl]) (by linarith only [hB24])
    linarith only [this, hBφ, hB24]
  -- the powers of `φ`
  set A := P ^ K with hA_def
  set V := P ^ a with hV_def
  set s := P ^ (ζ + 1) with hs_def
  set g := P ^ Cl with hg_def
  have hA1 : 1 ≤ A := Real.one_le_rpow hP1 hK0.le
  have hV3 : 3 ≤ V := h3a
  have hV1 : 1 < V := by linarith
  have hs1 : 1 ≤ s := Real.one_le_rpow hP1 hζ1.le
  have hg1 : 1 ≤ g := Real.one_le_rpow hP1 hCl.le
  have hpow : ∀ (x : ℝ) (k : ℕ), P ^ ((k : ℝ) * x) = (P ^ x) ^ k := by
    intro x k
    rw [mul_comm, Real.rpow_mul hP0.le, Real.rpow_natCast]
  have hPC : P ^ C = A ^ 2 * V ^ 4 * P ^ 2 := by
    rw [hC, Real.rpow_add hP0, Real.rpow_add hP0, show (2 : ℝ) * K = ((2 : ℕ) : ℝ) * K by norm_num,
      hpow, show (4 : ℝ) * a = ((4 : ℕ) : ℝ) * a by norm_num, hpow,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hCpos : 0 < C := by rw [hC]; linarith
  have hq0 : 0 < q := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 C) hqC
  have hKC : K ≤ C := by rw [hC]; linarith
  have hqle : ∀ K', K' ≤ K → P ^ K' ≤ q := fun K' h =>
    (Real.rpow_le_rpow_of_exponent_le hP1 (h.trans hKC)).trans hqC
  have hClK : Cl ≤ K := by rw [hK]; linarith
  have hKwK : Kw ≤ K := by rw [hK]; linarith
  have hKsK : Ks ≤ K := by rw [hK]; linarith
  have hKfK : Kf ≤ K := by rw [hK]; linarith
  -- `R = N^{-2/3}`
  set R : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3) with hR
  have hR0 : 0 ≤ R := Real.rpow_nonneg hN0.le _
  have hR3 : R ^ 3 * (N : ℝ) ^ 2 = 1 := by
    rw [hR, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (N : ℝ) 2,
      ← Real.rpow_add hN0]
    norm_num
  have hRN : (N : ℝ)⁻¹ ≤ R := by
    rw [hR, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  -- `s^18 g / A ≤ φ⁻¹` and the smallness condition of the point estimate
  have hsgA : s ^ 18 * g * A⁻¹ ≤ P⁻¹ := by
    have e1 : s ^ 18 * g = P ^ (18 * (ζ + 1) + Cl) := by
      rw [Real.rpow_add hP0, show (18 : ℝ) * (ζ + 1) = ((18 : ℕ) : ℝ) * (ζ + 1) by norm_num, hpow]
    have e2 : A = P ^ (18 * (ζ + 1) + Cl) * P ^ (Kw + Ks + Kf + 1) := by
      rw [hA_def, ← Real.rpow_add hP0, hK]; ring_nf
    have h3 : P ≤ P ^ (Kw + Ks + Kf + 1) := by
      conv_lhs => rw [← Real.rpow_one P]
      exact Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
    have hY : 0 < P ^ (18 * (ζ + 1) + Cl) := Real.rpow_pos_of_pos hP0 _
    rw [e1, e2, mul_inv, ← mul_assoc, mul_inv_cancel₀ hY.ne', one_mul]
    exact inv_anti₀ hP0 h3
  have hε : 4 * Cm * (3 * Cs * l + Cs * Cm * l + 2 * Cs + Cm + 6) * (s ^ 18 * g * A⁻¹) ≤ 1 := by
    have h1 : 4 * Cm * (3 * Cs * l + Cs * Cm * l + 2 * Cs + Cm + 6) ≤ P := by
      refine le_trans ?_ hBφ
      have hin : 3 * Cs * l + Cs * Cm * l + 2 * Cs + Cm + 6 ≤
          (3 * Cs + Cs * Cm + 2 * Cs + Cm + 6) * (l + 1) := by
        have e : (3 * Cs + Cs * Cm + 2 * Cs + Cm + 6) * (l + 1) =
            3 * Cs * l + Cs * Cm * l + 2 * Cs * l + Cm * l + 6 * l + 3 * Cs + Cs * Cm + 2 * Cs +
              Cm + 6 := by ring
        rw [e]
        have h1 : 0 ≤ Cs * l := by positivity
        have h2 : 0 ≤ Cm * l := by positivity
        have h3 : 0 ≤ Cs * Cm := by positivity
        linarith only [h1, h2, h3, hCs, hl]
      calc 4 * Cm * (3 * Cs * l + Cs * Cm * l + 2 * Cs + Cm + 6)
          ≤ 4 * Cm * ((3 * Cs + Cs * Cm + 2 * Cs + Cm + 6) * (l + 1)) :=
            mul_le_mul_of_nonneg_left hin (by positivity)
        _ = B * (l + 1) := by rw [hB]; ring
    have h0 : 0 ≤ s ^ 18 * g * A⁻¹ := by positivity
    calc 4 * Cm * (3 * Cs * l + Cs * Cm * l + 2 * Cs + Cm + 6) * (s ^ 18 * g * A⁻¹)
        ≤ P * P⁻¹ := mul_le_mul h1 hsgA h0 hP0.le
      _ = 1 := mul_inv_cancel₀ hP0.ne'
  -- `η` and the window
  have heta : ∀ E, outEta N K a E = A * V / (N * Real.sqrt (kappa E)) := by
    intro E
    unfold outEta
    rw [Real.rpow_add hP0]
  set b : ℝ := 2 + P ^ C * (1 / q ^ 2 + R) with hb
  have hb2 : 2 ≤ b := by
    have : 0 ≤ P ^ C * (1 / q ^ 2 + R) := by positivity
    linarith
  have hwin : ∀ E, b ≤ |E| → |E| ≤ 3 →
      kappa E = |E| - 2 ∧ 0 < Real.sqrt (kappa E) ∧ Real.sqrt (kappa E) ≤ 1 ∧
      1 / q ≤ Real.sqrt (kappa E) / (A * V ^ 2) ∧
      A ^ 3 * V ^ 3 ≤ N * kappa E * Real.sqrt (kappa E) ∧
      (N : ℝ)⁻¹ ≤ (Real.sqrt (kappa E) / (A * V ^ 2)) ^ 2 := fun E h1 h2 =>
    outside_window hN0 hP1 hA1 hV1.le hq0 hR0 hR3 hRN (by rw [← hPC]; exact h1) h2
  have hetaf : ∀ E, b ≤ |E| → |E| ≤ 3 → ∀ K', K' ≤ K →
      0 < outEta N K a E ∧ outEta N K a E ≤ kappa E ∧ (N : ℝ)⁻¹ ≤ outEta N K a E ∧
      P ^ K' / N < outEta N K a E ∧ A * V ≤ N * Real.sqrt (kappa E) ^ 2 * Real.sqrt (kappa E) := by
    intro E h1 h2 K' hK'
    obtain ⟨hκ, hX0, hX1, -, hNk, -⟩ := hwin E h1 h2
    rw [heta]
    exact outside_eta_facts hN0 hA1 hV1 hX0 hX1 (Real.sq_sqrt (abs_nonneg _)).symm hNk
      (Real.rpow_le_rpow_of_exponent_le hP1 hK')
  have hdom : ∀ E, b ≤ |E| → |E| ≤ 3 → ∀ K', K' ≤ K →
      (⟨E, outEta N K a E⟩ : ℂ) ∈ specDomain N K' := by
    intro E h1 h2 K' hK'
    obtain ⟨hη0, hηκ, -, hlt, -⟩ := hetaf E h1 h2 K' hK'
    obtain ⟨hκ, -⟩ := hwin E h1 h2
    refine ⟨by change |E| ≤ 5; linarith, hlt, ?_⟩
    change outEta N K a E ≤ 10
    linarith
  -- the grid and the exceptional events
  have hb0 : 0 ≤ b := by linarith
  set G := outsideGrid N b with hG
  set Ep := outsideGridE N b with hEp
  have hGw : ∀ p ∈ G, b ≤ |Ep p| ∧ |Ep p| ≤ 3 := by
    intro p hp
    have habs : |Ep p| = b + p.1 * ((N : ℝ) ^ 3)⁻¹ := outsideGridE_abs hb0 p
    rw [hG, outsideGrid, Finset.mem_filter] at hp
    rw [habs]
    refine ⟨?_, hp.2⟩
    have : 0 ≤ (p.1 : ℝ) * ((N : ℝ) ^ 3)⁻¹ := by positivity
    linarith
  set zp : ℕ × Bool → ℂ := fun p => ⟨Ep p, outEta N K a (Ep p)⟩ with hzp
  set γf : ℂ → ℝ := fun z => g * (1 / q + 1 / (N * z.im)) with hγf
  set D : Set ℂ := {z | ∃ p ∈ G, z = zp p} with hD
  set Bll : Set (Entries N) := (localLawEvent N Cl q)ᶜ with hBll
  set Bw : Set (Entries N) := {ω | ∃ z ∈ specDomain N Kw,
    (P ^ (ζ + 1))⁻¹ < lamD (symOfEntries ω) z + lamO (symOfEntries ω) z} with hBw
  set Bsc : ℕ × Bool → Set (Entries N) := fun p =>
    {ω | lamD (symOfEntries ω) (zp p) + lamO (symOfEntries ω) (zp p) ≤ s⁻¹ ∧
      Cs * (s ^ 2 * l / q ^ 2 + s ^ 4 * l * psiCtrl (symOfEntries ω) (zp p) ^ 2 +
          lamAvg (symOfEntries ω) (zp p) ^ 2 / l) <
        ‖(1 - msc (zp p) ^ 2) * (stieltjesM (symOfEntries ω) (zp p) - msc (zp p)) -
          msc (zp p) ^ 3 * (stieltjesM (symOfEntries ω) (zp p) - msc (zp p)) ^ 2 -
          msc (zp p) ^ 2 * zAvg (symOfEntries ω) (zp p)‖} with hBsc
  set Bfa : ℕ × Bool → Set (Entries N) := fun p =>
    {ω | P ^ (14 * (ζ + 1)) * (1 / q ^ 2 + 1 / (N * (zp p).im) ^ 2 +
        P ^ (4 * (ζ + 1)) * ((msc (zp p)).im + γf (zp p)) / (N * (zp p).im)) <
      ‖zAvg (symOfEntries ω) (zp p)‖} with hBfa
  -- the probabilities of the exceptional events
  have hPll : L.law Bll ≤ ENNReal.ofReal (Real.exp (-cl * s)) :=
    hLL N hNl L q hL hqBS (hqle Cl hClK)
  have hPw : L.law Bw ≤ ENNReal.ofReal (Real.exp (-cw * s)) :=
    hW N hNw L q hL hqBS (hqle Kw hKwK)
  have hPsc : ∀ p ∈ G, L.law (Bsc p) ≤ ENNReal.ofReal (Real.exp (-cs * s)) := fun p hp =>
    hSC N hNs L q s (zp p) hL hqBS (hqle Ks hKsK) (hdom _ (hGw p hp).1 (hGw p hp).2 Ks hKsK)
      le_rfl (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith))
  have hDsub : D ⊆ specDomain N Kf := by
    rintro z ⟨p, hp, rfl⟩
    exact hdom _ (hGw p hp).1 (hGw p hp).2 Kf hKfK
  have hsg24 : s ^ 18 * g * A⁻¹ ≤ 1 / 24 := by
    refine hsgA.trans ?_
    rw [inv_le_comm₀ hP0 (by norm_num)]
    linarith
  have hγD : ∀ z ∈ D, γf z ≤ (P ^ (ζ + 1))⁻¹ := by
    rintro z ⟨p, hp, rfl⟩
    obtain ⟨-, hX0, hX1, hqX, -, -⟩ := hwin _ (hGw p hp).1 (hGw p hp).2
    have hA0 : 0 < A := by linarith
    have hAV2 : A ≤ A * V ^ 2 := le_mul_of_one_le_right hA0.le (one_le_pow₀ hV1.le)
    have hqA : 1 / q ≤ A⁻¹ := by
      refine hqX.trans ?_
      rw [div_le_iff₀ (by positivity)]
      calc Real.sqrt (kappa (Ep p)) ≤ 1 := hX1
        _ = A⁻¹ * A := (inv_mul_cancel₀ hA0.ne').symm
        _ ≤ A⁻¹ * (A * V ^ 2) := mul_le_mul_of_nonneg_left hAV2 (by positivity)
    have hnA : 1 / (N * (zp p).im) ≤ A⁻¹ := by
      change 1 / (N * outEta N K a (Ep p)) ≤ A⁻¹
      rw [heta]
      have e : 1 / ((N : ℝ) * (A * V / (N * Real.sqrt (kappa (Ep p))))) =
          Real.sqrt (kappa (Ep p)) / (A * V) := by field_simp
      rw [e, div_le_iff₀ (by positivity)]
      calc Real.sqrt (kappa (Ep p)) ≤ 1 := hX1
        _ = A⁻¹ * A := (inv_mul_cancel₀ hA0.ne').symm
        _ ≤ A⁻¹ * (A * V) := mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_right hA0.le hV1.le) (by positivity)
    exact outside_gamma hA0 hs1 (by linarith) hsg24 hqA hnA
  have hin : L.law {ω | ∃ z ∈ D, γf z < lamAvg (symOfEntries ω) z} ≤
      ENNReal.ofReal (Real.exp (-cl * P ^ (ζ + 1))) := by
    refine le_trans (measure_mono ?_) hPll
    rintro ω ⟨z, ⟨p, hp, rfl⟩, hlt⟩ hω
    have hz := hdom _ (hGw p hp).1 (hGw p hp).2 Cl hClK
    have h1 := (hω (zp p) hz).1
    have h2 : avgErr N Cl q (zp p) ≤ γf (zp p) := by
      unfold avgErr
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (min_le_right _ _) le_rfl
    exact lt_irrefl _ (hlt.trans_le (h1.trans h2))
  have hPfa : ∀ p ∈ G, L.law (Bfa p) ≤
      ENNReal.ofReal (Real.exp (-cf * P ^ (ζ + 1) / l ^ 2)) := fun p hp =>
    hFA N hNf L q D γf hL hqBS (hqle Kf hKfK) hDsub hγD hin (zp p) ⟨p, hp, rfl⟩
  -- outside the exceptional events, the bounds hold on the whole window
  have hsub : (outsideEvent N K a C q)ᶜ ⊆ Bll ∪ Bw ∪ ⋃ p ∈ G, (Bsc p ∪ Bfa p) := by
    intro ω hω
    by_contra hcon
    apply hω
    have hll : ω ∈ localLawEvent N Cl q := by
      by_contra h
      exact hcon (Or.inl (Or.inl h))
    have hw : ∀ z ∈ specDomain N Kw,
        lamD (symOfEntries ω) z + lamO (symOfEntries ω) z ≤ s⁻¹ := by
      intro z hz
      by_contra h
      push Not at h
      exact hcon (Or.inl (Or.inr ⟨z, hz, h⟩))
    have hsc : ∀ p ∈ G, ω ∉ Bsc p := fun p hp h =>
      hcon (Or.inr (Set.mem_biUnion hp (Or.inl h)))
    have hfa : ∀ p ∈ G, ω ∉ Bfa p := fun p hp h =>
      hcon (Or.inr (Set.mem_biUnion hp (Or.inr h)))
    set H := symOfEntries ω with hH_def
    have hH : H.IsHermitian := symOfEntries_isHermitian ω
    intro E hE1 hE3
    have hE1' : b ≤ |E| := hE1
    obtain ⟨p, hp, hpb, hp3, hpE, hpE', hdE⟩ := outside_grid hN1' hb2 hE1' hE3
    obtain ⟨hκE, hXE0, hXE1, hqXE, hNkE, hτE⟩ := hwin E hE1' hE3
    obtain ⟨hκp, hXp0, hXp1, hqXp, hNkp, hτp⟩ := hwin (Ep p) hpb hp3
    -- the estimate at the grid point
    have hLLp : lamAvg H (zp p) ≤ g * (1 / q + 1 / (N * outEta N K a (Ep p))) := by
      have h1 := (hll (zp p) (hdom _ hpb hp3 Cl hClK)).1
      have h2 : avgErr N Cl q (zp p) ≤ γf (zp p) := by
        unfold avgErr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (min_le_right _ _) le_rfl
      exact h1.trans h2
    have hSCp := not_lt.mp (fun h => hsc p hp ⟨hw (zp p) (hdom _ hpb hp3 Kw hKwK), h⟩)
    have hFAp : ‖zAvg H (zp p)‖ ≤ P ^ (14 * (ζ + 1)) * (1 / q ^ 2 + 1 / (N * (zp p).im) ^ 2 +
        P ^ (4 * (ζ + 1)) * ((msc (zp p)).im + γf (zp p)) / (N * (zp p).im)) :=
      not_lt.mp (hfa p hp)
    have e14 : P ^ (14 * (ζ + 1)) = s ^ 14 := by
      rw [show (14 : ℝ) * (ζ + 1) = ((14 : ℕ) : ℝ) * (ζ + 1) by norm_num, hpow]
    have e4 : P ^ (4 * (ζ + 1)) = s ^ 4 := by
      rw [show (4 : ℝ) * (ζ + 1) = ((4 : ℕ) : ℝ) * (ζ + 1) by norm_num, hpow]
    rw [e14, e4] at hFAp
    obtain ⟨hΛp, hIp⟩ := outside_point (H := H) (η := outEta N K a (Ep p)) hN3 hCm hCs hs1 hg1
      hA1 hV1.le hq0 hmsc (by linarith) hp3 hXp0 hXp1 hqXp hNkp (heta (Ep p)) hε hLLp hSCp hFAp
    -- transfer to `E`
    obtain ⟨hηE0, -, hηEN, -, -⟩ := hetaf E hE1' hE3 K le_rfl
    obtain ⟨-, -, hηpN, -, hAVp⟩ := hetaf (Ep p) hpb hp3 K le_rfl
    have hXle : Real.sqrt (kappa (Ep p)) ≤ Real.sqrt (kappa E) :=
      Real.sqrt_le_sqrt (by rw [hκp, hκE]; linarith)
    have hdiff := outside_eta_diff hN0 (a := A * V) (x := Real.sqrt (kappa (Ep p)))
      (y := Real.sqrt (kappa E)) (δ := ((N : ℝ) ^ 3)⁻¹) (by positivity) hXp0 hXle
      (by rw [Real.sq_sqrt (show 0 ≤ kappa E from abs_nonneg _),
        Real.sq_sqrt (show 0 ≤ kappa (Ep p) from abs_nonneg _), hκE, hκp]; linarith)
      hAVp
    have hdη : |outEta N K a E - outEta N K a (Ep p)| ≤ ((N : ℝ) ^ 3)⁻¹ := by
      rw [heta, heta, abs_sub_comm, abs_of_nonneg hdiff.1]
      exact hdiff.2
    have hτle : Real.sqrt (kappa (Ep p)) / (A * V ^ 2) ≤ Real.sqrt (kappa E) / (A * V ^ 2) :=
      div_le_div_of_nonneg_right hXle (by positivity)
    obtain ⟨hΛE, hImE⟩ := outside_transfer hH h256 hηEN hηpN hdE hdη hτp (by positivity) hτle
      hΛp hIp
    have hτeq : (phi N ^ a * N * outEta N K a E)⁻¹ = Real.sqrt (kappa E) / (A * V ^ 2) := by
      rw [heta]
      change (V * N * (A * V / (N * Real.sqrt (kappa E))))⁻¹ = _
      field_simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hτeq]; exact hΛE
    · rw [hτeq]; exact hImE
    · intro α
      apply lt_abs_eigenvalues_sub_of_im_stieltjesM_lt hH hηE0
      have e : (E : ℂ) + outEta N K a E * Complex.I = ⟨E, outEta N K a E⟩ := by
        apply Complex.ext <;> simp
      rw [e]
      refine hImE.trans_lt ?_
      rw [heta]
      have e2 : 1 / (2 * (N : ℝ) * (A * V / (N * Real.sqrt (kappa E)))) =
          Real.sqrt (kappa E) / (A * V) / 2 := by field_simp
      rw [e2, div_lt_iff₀ (by positivity : (0 : ℝ) < A * V ^ 2)]
      have e3 : Real.sqrt (kappa E) / (A * V) / 2 * (A * V ^ 2) =
          Real.sqrt (kappa E) * (V / 2) := by field_simp
      rw [e3]
      have : 1 < V / 2 := by linarith
      exact lt_mul_of_one_lt_right hXE0 this
  -- the union bound
  have hmeas : L.law (outsideEvent N K a C q)ᶜ ≤
      L.law Bll + L.law Bw + ∑ p ∈ G, L.law (Bsc p ∪ Bfa p) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le G _)))
  set e1 := Real.exp (-cl * s) with he1
  set e2 := Real.exp (-cw * s) with he2
  set e3 := Real.exp (-cs * s) with he3
  set e4 := Real.exp (-cf * P ^ (ζ + 1) / l ^ 2) with he4
  have hsum : ∑ p ∈ G, L.law (Bsc p ∪ Bfa p) ≤ ENNReal.ofReal (G.card * (e3 + e4)) := by
    calc ∑ p ∈ G, L.law (Bsc p ∪ Bfa p) ≤ ∑ p ∈ G, ENNReal.ofReal (e3 + e4) :=
          Finset.sum_le_sum fun p hp => (measure_union_le _ _).trans (by
            rw [ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
            exact add_le_add (hPsc p hp) (hPfa p hp))
      _ = ENNReal.ofReal (G.card * (e3 + e4)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  set Q := P ^ ζ with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hP1 hζ.le
  have hsPQ : s = P * Q := by
    rw [hs_def, Real.rpow_add hP0, Real.rpow_one, mul_comm]
  have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ hl
  have hexp : ∀ c' : ℝ, c0 ≤ c' → Real.exp (-c' * s) ≤ Real.exp (-c0 * (P * Q) / l ^ 2) := by
    intro c' hc'
    apply Real.exp_le_exp.mpr
    rw [← hsPQ]
    have hs0 : 0 ≤ s := by linarith
    have h1 : c0 * s / l ^ 2 ≤ c0 * s := div_le_self (by positivity) hl2
    have h2 : c0 * s ≤ c' * s := mul_le_mul_of_nonneg_right hc' hs0
    have e : -c0 * s / l ^ 2 = -(c0 * s / l ^ 2) := by ring
    rw [e]; linarith
  have hc0l : c0 ≤ cl := (min_le_left _ _).trans (min_le_left _ _)
  have hc0w : c0 ≤ cw := (min_le_left _ _).trans (min_le_right _ _)
  have hc0s : c0 ≤ cs := (min_le_right _ _).trans (min_le_left _ _)
  have hc0f : c0 ≤ cf := (min_le_right _ _).trans (min_le_right _ _)
  have h4 : e4 ≤ Real.exp (-c0 * (P * Q) / l ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [← hsPQ]
    have hs0 : 0 ≤ s := by linarith
    have : c0 * s / l ^ 2 ≤ cf * s / l ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc0f hs0) (by positivity)
    have e : ∀ c' : ℝ, -c' * s / l ^ 2 = -(c' * s / l ^ 2) := fun c' => by ring
    rw [e, e]; linarith
  calc L.law (outsideEvent N K a C q)ᶜ
      ≤ L.law Bll + L.law Bw + ∑ p ∈ G, L.law (Bsc p ∪ Bfa p) := hmeas
    _ ≤ ENNReal.ofReal e1 + ENNReal.ofReal e2 + ENNReal.ofReal (G.card * (e3 + e4)) :=
        add_le_add (add_le_add hPll hPw) hsum
    _ = ENNReal.ofReal (e1 + e2 + G.card * (e3 + e4)) := by
        have p1 : 0 ≤ e1 := (Real.exp_pos _).le
        have p2 : 0 ≤ e2 := (Real.exp_pos _).le
        have p3 : 0 ≤ (G.card : ℝ) * (e3 + e4) :=
          mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        rw [ENNReal.ofReal_add (add_nonneg p1 p2) p3, ENNReal.ofReal_add p1 p2]
    _ ≤ ENNReal.ofReal (Real.exp (-c0 * Q)) :=
        ENNReal.ofReal_le_ofReal (outside_union_exp hN1' hc00 hl hQ1 hφl (outsideGrid_card N b)
          (Real.exp_pos _).le (Real.exp_pos _).le (hexp cl hc0l) (hexp cw hc0w) (hexp cs hc0s) h4)

/-! ### Compiled checks -/

/-- For `q = N^{2/5}` the window `2 + φ^C (q⁻² + N^{-2/3}) ≤ |E| ≤ 3` contains `E = ±5/2` for all
large `N`. -/
private lemma outside_window_rad (C : ℝ) : ∀ᶠ N : ℕ in atTop,
    2 + phi N ^ C * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) ≤ 5 / 2 := by
  filter_upwards [phi_rpow_le_rpow C (by norm_num : (0 : ℝ) < 1 / 6), eventually_ge_atTop 16]
    with N h6 h16
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have e1 : 1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 = (N : ℝ) ^ (-(4 / 5 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.rpow_neg hN0.le, one_div]
    norm_num
  have hsq : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 4 := by
    rw [Real.rpow_neg hN0.le, inv_le_comm₀ (Real.rpow_pos_of_pos hN0 _) (by norm_num)]
    have h4 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (1 / 4 : ℝ)⁻¹ = (16 : ℝ) ^ (1 / 2 : ℝ) := by rw [h4]; norm_num
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hN16 (by norm_num)
  have hterm : ∀ x : ℝ, x ≤ -(1 / 2 + 1 / 6) → phi N ^ C * (N : ℝ) ^ x ≤ 1 / 4 := by
    intro x hx
    calc phi N ^ C * (N : ℝ) ^ x ≤ (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ x :=
          mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hN0.le _)
      _ = (N : ℝ) ^ (1 / 6 + x) := (Real.rpow_add hN0 _ _).symm
      _ ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ 1 / 4 := hsq
  rw [e1, mul_add]
  have h1 := hterm (-(4 / 5 : ℝ)) (by norm_num)
  have h2 := hterm (-(2 : ℝ) / 3) (by norm_num)
  linarith

/-- (4.31)–(4.46) for the Rademacher laws with `C0 = 1`, `q = N^{2/5}`, `ζ = 1`, `a = 1`: for all
large `N` the hypotheses hold, the window contains `E = ±5/2`, the bound `(φ^a N η)⁻¹` of
(3.8) at `E = 5/2` is below `1`, and the probability bound applies. -/
example : ∃ K > (0 : ℝ), ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧ (radLaws N).BoundedSupportAS ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    phi N ^ C ≤ (N : ℝ) ^ (2 / 5 : ℝ) ∧
    2 + phi N ^ C * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) ≤
      |(5 / 2 : ℝ)| ∧
    2 + phi N ^ C * (1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) ≤
      |(-5 / 2 : ℝ)| ∧
    0 < outEta N K 1 (5 / 2) ∧ (phi N ^ (1 : ℝ) * N * outEta N K 1 (5 / 2))⁻¹ < 1 ∧
    (radLaws N).law (outsideEvent N K 1 C ((N : ℝ) ^ (2 / 5 : ℝ)))ᶜ ≤
      ENNReal.ofReal (Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨K, hK, h⟩ := outside_boundedAS (ζ := 1) one_pos zero_le_one
  obtain ⟨C, hC, c, hc, N0, hN0⟩ := h 1 one_pos
  refine ⟨K, hK, C, hC, c, hc, ?_⟩
  filter_upwards [sc_rad_instance C 1, eventually_ge_atTop N0, outside_window_rad C,
    eventually_ge_atTop 3] with N hi hN hw h3
  have hφ1 : 1 ≤ phi N := sc_one_le_phi h3
  have hκ : kappa (5 / 2) = 1 / 2 := by unfold kappa; norm_num [abs_of_pos]
  have hsq0 : 0 < Real.sqrt (kappa (5 / 2)) := by rw [hκ]; positivity
  have hsq1 : Real.sqrt (kappa (5 / 2)) < 1 := by
    rw [hκ, Real.sqrt_lt' one_pos]; norm_num
  have hpK : 1 ≤ phi N ^ (K + 1) := Real.one_le_rpow hφ1 (by linarith)
  have hp1 : 1 ≤ phi N ^ (1 : ℝ) := Real.one_le_rpow hφ1 zero_le_one
  have hη : 0 < outEta N K 1 (5 / 2) := by unfold outEta; positivity
  refine ⟨hi.1, hi.2.1, hi.2.2.1, by rw [abs_of_pos (by norm_num)]; exact hw,
    by rw [abs_of_neg (by norm_num)]; linarith, hη, ?_, hN0 N hN (radLaws N) _ hi.1 hi.2.1 hi.2.2.1⟩
  have e : phi N ^ (1 : ℝ) * N * outEta N K 1 (5 / 2) =
      phi N ^ (1 : ℝ) * phi N ^ (K + 1) / Real.sqrt (kappa (5 / 2)) := by
    unfold outEta; field_simp
  rw [e, inv_lt_one₀ (by positivity), lt_div_iff₀ hsq0]
  have := one_le_mul_of_one_le_of_one_le hp1 hpK
  linarith

#print axioms outside_boundedAS

end WEdgeNS
