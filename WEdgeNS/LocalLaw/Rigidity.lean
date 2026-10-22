import WEdgeNS.LocalLaw.CountingQ
import WEdgeNS.LocalLaw.RigidityDet
import WEdgeNS.LocalLaw.Norm

/-!
# Rigidity of eigenvalues (Lemma 3.1 (4))
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- A private lemma of an imported file: the Rademacher instance.
open private sc_rad_instance from WEdgeNS.LocalLaw.SelfConsistent

/-- The event (3.6); `j : Fin N` is the paper's index `j + 1`. -/
def rigidityEvent (N : ℕ) (C q : ℝ) : Set (Entries N) :=
  {ω | ∀ j : Fin N, |eigAsc (symOfEntries_isHermitian ω) j - gammaLoc N ((j : ℕ) + 1)| ≤
    phi N ^ C * ((min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
      (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / q ^ 2)}

/-! ### The deterministic step -/

/-- The product of the constants of the counting step: `3 C_c U^{C_c} (log N) U ≤ φ^{M C_c + M + 2}`
for `U = φ^M`, `log N ≤ φ` and `3 C_c ≤ φ`. -/
private lemma rigidity_count_const {Cc M P L : ℝ} (hCc : 0 < Cc) (hL : L ≤ P)
    (hCP : 3 * Cc ≤ P) (hL0 : 0 ≤ L) :
    3 * (Cc * (P ^ M) ^ Cc * L) * P ^ M ≤ P ^ (M * Cc + M + 2) := by
  have hP0 : 0 < P := by linarith
  have h1 : (P ^ M) ^ Cc = P ^ (M * Cc) := (Real.rpow_mul hP0.le M Cc).symm
  have h2 : P ^ (M * Cc + M + 2) = P ^ (M * Cc) * P ^ M * P * P := by
    have : M * Cc + M + 2 = M * Cc + M + 1 + 1 := by ring
    rw [this, Real.rpow_add hP0, Real.rpow_add hP0, Real.rpow_add hP0, Real.rpow_one]
  rw [h1, h2]
  have hA : 0 ≤ P ^ (M * Cc) := Real.rpow_nonneg hP0.le _
  have hB : 0 ≤ P ^ M := Real.rpow_nonneg hP0.le _
  have hAB : 0 ≤ P ^ (M * Cc) * P ^ M := mul_nonneg hA hB
  calc 3 * (Cc * P ^ (M * Cc) * L) * P ^ M
      = (3 * Cc) * L * (P ^ (M * Cc) * P ^ M) := by ring
    _ ≤ P * P * (P ^ (M * Cc) * P ^ M) := by
        apply mul_le_mul_of_nonneg_right _ hAB
        exact mul_le_mul hCP hL hL0 hP0.le
    _ = P ^ (M * Cc) * P ^ M * P * P := by ring

/-- From the local law (3.2) on `S(A)`, the norm bound (3.4) and `q ≥ N^{φs}`, `φs > 1/3`, to the
event (3.6), for all large `N`. -/
private lemma rigidity_det {A B φs : ℝ} (hA : 0 ≤ A) (hφs : 1 / 3 < φs) :
    ∃ C > 0, ∃ N1 : ℕ, ∀ N ≥ N1, ∀ (q : ℝ) (ω : Entries N), (N : ℝ) ^ φs ≤ q →
      ω ∈ localLawEvent N A q → ω ∈ normEvent N B q → ω ∈ rigidityEvent N C q := by
  obtain ⟨Cc, hCc, hcount⟩ := abs_countFn_sub_nsc_le_q
  obtain ⟨Cr, hCr, hrig⟩ := abs_eigAsc_sub_gammaLoc_le_q
  have hM0 : 0 ≤ max A B := le_max_of_le_left hA
  have hM1 : 0 < max A B * Cc + max A B + 2 := by positivity
  refine ⟨(max A B * Cc + max A B + 2) * Cr + 1, by positivity, ?_⟩
  have hev := (eventually_ge_atTop 16).and <|
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max (max (3 * Cc) Cr) 5)).and <|
    (phi_rpow_le_rpow A (by norm_num : (0 : ℝ) < 1 / 2)).and (eventually_ge_atTop 4)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  refine ⟨N1, fun N hN q ω hq hll hne => ?_⟩
  obtain ⟨h16, hlog, hAφ, h4⟩ := hN1 N hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogφ : Real.log N ≤ phi N := log_le_phi h16
  have hφ3 : 3 * Cc ≤ phi N :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (hlog.trans' le_rfl) |>.trans hlogφ
  have hφr : Cr ≤ phi N :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (hlog.trans' le_rfl) |>.trans hlogφ
  have hφ5 : 5 ≤ phi N := (le_max_right _ _).trans hlog |>.trans hlogφ
  have hφ1 : 1 ≤ phi N := by linarith
  have hφ0 : 0 < phi N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1r
  -- the bracket of (3.4) and (3.6)
  have hbr : 0 ≤ 1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    have := Real.rpow_nonneg hNr.le (-(2 : ℝ) / 3)
    positivity
  have hq1 : 1 ≤ q := (Real.one_le_rpow hN1r (by linarith)).trans hq
  have hq3 : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ q :=
    (Real.rpow_le_rpow_of_exponent_le hN1r hφs.le).trans hq
  -- the norm bound with the unordered eigenvalues
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues (symOfEntries_isHermitian ω)
  have hnormK : ∀ K, B ≤ K → ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤
      2 + phi N ^ K * (1 / q ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3)) := fun K hK α => by
    rw [hσ α]
    refine (hne (σ α)).trans ?_
    gcongr
  -- the constants
  set M : ℝ := max A B with hMdef
  have hBM : B ≤ M := le_max_right _ _
  set U : ℝ := phi N ^ M with hUdef
  have hU : 1 ≤ U := Real.one_le_rpow hφ1 hM0
  have hAU : phi N ^ A ≤ U := Real.rpow_le_rpow_of_exponent_le hφ1 (le_max_left _ _)
  have hA1 : 1 ≤ phi N ^ A := Real.one_le_rpow hφ1 hA
  -- the counting step
  have hy0a : 1 / (N : ℝ) ≤ 2 * phi N ^ A / N := by
    gcongr
    linarith
  have hy0b : 2 * phi N ^ A / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNr]
    have hs : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add hNr]; norm_num
    have hs0 : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hNr.le _
    have h4r : (4 : ℝ) ≤ N := by exact_mod_cast h4
    have hs2 : 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
    nlinarith
  have hst : ∀ x y : ℝ, |x| ≤ 5 → 2 * phi N ^ A / N ≤ y → y ≤ 1 →
      ‖stieltjesM (symOfEntries ω) ⟨x, y⟩ - msc ⟨x, y⟩‖ ≤
        U * (min (1 / (q ^ 2 * Real.sqrt (kappa x + y))) (1 / q) + 1 / (N * y)) := by
    intro x y hx hy0 hy1
    have hApos : 0 < phi N ^ A / N := by positivity
    have hyA : phi N ^ A / N < y := by
      refine lt_of_lt_of_le ?_ hy0
      rw [mul_div_assoc]
      linarith
    have hypos : 0 < y := hApos.trans hyA
    have hz : (⟨x, y⟩ : ℂ) ∈ specDomain N A := ⟨hx, hyA, by linarith⟩
    refine (hll _ hz).1.trans ?_
    unfold avgErr
    dsimp only
    refine mul_le_mul_of_nonneg_right hAU ?_
    have : 0 ≤ 1 / (N * y) := by positivity
    have : 0 ≤ min (1 / (q ^ 2 * Real.sqrt (kappa x + y))) (1 / q) :=
      le_min (by positivity) (by positivity)
    linarith
  have hcnt := hcount N hN2 (symOfEntries ω) (symOfEntries_isHermitian ω) U q
    (2 * phi N ^ A / N) hU hq1 hy0a hy0b (hnormK M hBM) hst
  -- the counting bound in the form of the rigidity lemma
  have hconst := rigidity_count_const (M := M) hCc hlogφ hφ3 hlog0
  have hcnt' : ∀ E, |countFn (symOfEntries_isHermitian ω) E - nsc E| ≤
      phi N ^ (M * Cc + M + 2) *
        (1 / N + 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2) := by
    intro E
    refine (hcnt E).trans ?_
    have hR : 0 ≤ 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2 := by positivity
    have hP : 0 ≤ 1 / (N : ℝ) := by positivity
    have hy0U : 2 * phi N ^ A / (N : ℝ) ≤ 2 * U * (1 / N) := by
      rw [mul_one_div]
      gcongr
    have hD : 0 ≤ Cc * U ^ Cc * Real.log N := by positivity
    calc Cc * U ^ Cc * Real.log N *
          (1 / N + 2 * phi N ^ A / N + 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2)
        ≤ Cc * U ^ Cc * Real.log N *
            (3 * U * (1 / N + (1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ hD
          nlinarith
      _ = (3 * (Cc * U ^ Cc * Real.log N) * U) *
            (1 / N + 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2) := by ring
      _ ≤ phi N ^ (M * Cc + M + 2) * (1 / N + 1 / q ^ 3 + Real.sqrt (kappa E) / q ^ 2) := by
          apply mul_le_mul_of_nonneg_right hconst
          positivity
  -- the deterministic rigidity lemma
  have ht : 1 ≤ phi N ^ (M * Cc + M + 2) := Real.one_le_rpow hφ1 hM1.le
  have hB' : B ≤ M * Cc + M + 2 := by nlinarith
  have hfin := hrig N hN2 (symOfEntries ω) (symOfEntries_isHermitian ω) _ q ht hq3 hcnt'
    (hnormK _ hB')
  intro j
  refine (hfin j).trans ?_
  have hj : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  have hmin : 0 ≤ min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ)) :=
    le_min (by positivity) (by linarith)
  have hbk : 0 ≤ (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
      (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / q ^ 2 := by
    have := Real.rpow_nonneg hmin (-(1 : ℝ) / 3)
    have := Real.rpow_nonneg hNr.le (-(2 : ℝ) / 3)
    positivity
  apply mul_le_mul_of_nonneg_right _ hbk
  rw [← Real.rpow_mul hφ0.le, Real.rpow_add hφ0, Real.rpow_one]
  have hpr : 0 ≤ phi N ^ ((M * Cc + M + 2) * Cr) := Real.rpow_nonneg hφ0.le _
  calc Cr * phi N ^ ((M * Cc + M + 2) * Cr) ≤ phi N * phi N ^ ((M * Cc + M + 2) * Cr) :=
        mul_le_mul_of_nonneg_right hφr hpr
    _ = phi N ^ ((M * Cc + M + 2) * Cr) * phi N := mul_comm _ _

/-! ### The theorem -/

/-- Lemma 3.1 (4) with Remark 3.2. -/
theorem rigidity {ζ C0 c φs : ℝ} (hζ : 0 < ζ) (hC0 : 0 ≤ C0) (hc : 0 < c)
    (hφs : 1 / 3 < φs) :
    ∃ C > 0, HighProbOn ζ (fun _ L => L.IsGenWigner C0)
      (fun N L => {ω | ∀ q, L.SupportParam ((N : ℝ) ^ φs) c q → ω ∈ rigidityEvent N C q}) := by
  obtain ⟨A, hA, hlaw⟩ := localLaw hζ hC0 hc
  obtain ⟨B, hB, hnorm⟩ := norm_le_two_add hζ hC0 hc
  obtain ⟨C, hC, N1, hdet⟩ := rigidity_det (A := A) (B := B) hA.le hφs
  obtain ⟨c', hc', C', hC', N0, h⟩ := hlaw.inter hnorm
  have hφs0 : 0 < φs := by linarith
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 ((phi_rpow_le_rpow A hφs0).and (phi_rpow_le_rpow B hφs0))
  refine ⟨C, hC, c', hc', C', hC', max N0 (max N1 N2), fun N hN L hL => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  refine (measure_mono (Set.compl_subset_compl.mpr ?_)).trans (h N hN0 L hL)
  intro ω hω q hq
  obtain ⟨hAφ, hBφ⟩ := hN2 N hN2'
  exact hdet N hN1 q ω hq.1 (hω.1 q ⟨hAφ.trans hq.1, hq.2.1, hq.2.2⟩)
    (hω.2 q ⟨hBφ.trans hq.1, hq.2.1, hq.2.2⟩)

/-! ### Compiled check -/

/-- The allowed deviation in (3.6) is below `1/2` at every index for the exponents of the
Rademacher instance, once `N` is large. -/
private lemma rigidity_window_rad (C : ℝ) : ∀ᶠ N : ℕ in atTop, ∀ j : Fin N,
    phi N ^ C * ((min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
      (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2) < 1 / 2 := by
  filter_upwards [phi_rpow_le_rpow C (by norm_num : (0 : ℝ) < 1 / 6), eventually_ge_atTop 32]
    with N hφ hN j
  have hN32 : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hj : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  have hmin : 1 ≤ min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ)) :=
    le_min (by have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) (by linarith)
  have h1 : (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hmin (by norm_num)
  have ht0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hNr.le _
  have h2 : 1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    have e : ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 = (N : ℝ) ^ (4 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]; norm_num
    have e2 : (N : ℝ) ^ (-(2 : ℝ) / 3) = 1 / (N : ℝ) ^ (2 / 3 : ℝ) := by
      rw [show -(2 : ℝ) / 3 = -(2 / 3 : ℝ) by ring, Real.rpow_neg hNr.le, one_div]
    rw [e, e2]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNr _)
      (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
  have hbr : (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
      (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 ≤
        2 * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    have : (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
        (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right h1 ht0
    linarith
  have hbr0 : 0 ≤ (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
      (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2 := by
    have := Real.rpow_nonneg (zero_le_one.trans hmin) (-(1 : ℝ) / 3)
    positivity
  have h3 : (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) = ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hNr, ← Real.rpow_neg hNr.le]; norm_num
  have hs : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hNr]; norm_num
  have hs0 : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNr _
  have hs5 : 5 < (N : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
  have hinv : ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ < 1 / 5 := by
    rw [inv_lt_comm₀ hs0 (by norm_num)]
    simpa using hs5
  calc phi N ^ C * ((min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
        (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2)
      ≤ (N : ℝ) ^ (1 / 6 : ℝ) * (2 * (N : ℝ) ^ (-(2 : ℝ) / 3)) :=
        mul_le_mul hφ hbr hbr0 (Real.rpow_nonneg hNr.le _)
    _ = 2 * ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [← h3]; ring
    _ < 1 / 2 := by linarith

/-- Lemma 3.1 (4) for the Rademacher laws with `ζ = 1`, `C0 = 1`, `c = 1/2`, `φs = 2/5`: for all
large `N` the laws are generalized Wigner laws, `q = N^{2/5}` is an admissible support parameter,
the deviation allowed by (3.6) is below `1/2` at every index, and the conclusion of `rigidity`
applies. -/
example : ∃ C > (0 : ℝ), ∃ c' > (0 : ℝ), ∃ C' : ℕ, ∀ᶠ N : ℕ in atTop,
    (radLaws N).IsGenWigner 1 ∧
    (radLaws N).SupportParam ((N : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) ((N : ℝ) ^ (2 / 5 : ℝ)) ∧
    (∀ j : Fin N, phi N ^ C * ((min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
      (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / ((N : ℝ) ^ (2 / 5 : ℝ)) ^ 2) < 1 / 2) ∧
    (radLaws N).law {ω | ∀ q, (radLaws N).SupportParam ((N : ℝ) ^ (2 / 5 : ℝ)) (1 / 2) q →
        ω ∈ rigidityEvent N C q}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c' * phi N ^ (1 : ℝ))) := by
  obtain ⟨C, hC, c', hc', C', hC', N0, h⟩ :=
    rigidity (ζ := 1) (C0 := 1) (c := 1 / 2) (φs := 2 / 5) one_pos zero_le_one (by norm_num)
      (by norm_num)
  refine ⟨C, hC, c', hc', C', ?_⟩
  filter_upwards [sc_rad_instance 0 0, eventually_ge_atTop N0, rigidity_window_rad C] with N hi hN
    hw
  exact ⟨hi.1, ⟨le_rfl, hi.2.1.boundedSupport _, hi.2.1.tailVarOff _⟩, hw,
    h N hN (radLaws N) hi.1⟩

#print axioms rigidityEvent
#print axioms rigidity

end WEdgeNS
