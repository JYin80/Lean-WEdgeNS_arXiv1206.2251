import WEdgeNS.EdgeUniv.LargeQClass
import WEdgeNS.EdgeUniv.EdgeSandwich
import WEdgeNS.LocalLaw.Interface
import WEdgeNS.LocalLaw.Norm
import WEdgeNS.LocalLaw.Rigidity

/-!
# The edge event for the class of Lemma 3.5 and for the GOE
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- The GOE off-diagonal law is a centered Gaussian.
open private goeLaws_off from WEdgeNS.Model.Transfer
open private sc_one_le_phi from WEdgeNS.LocalLaw.SelfConsistent

/-! ### Elementary bounds on `φ` -/

/-- `φ^a ≥ B` for large `N`, when `a > 0`. -/
private lemma largeQ_eventually_phi_rpow {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, B ≤ phi N ^ a :=
  ((tendsto_rpow_atTop ha).comp tendsto_phi_atTop).eventually_ge_atTop B

/-- `q⁻² ≤ N^{-2/3}` for `q = N^φs` with `φs ≥ 1/3`. -/
private lemma largeQ_inv_sq_le {N : ℕ} {φs : ℝ} (hN : 1 ≤ N) (hφs : 1 / 3 ≤ φs) :
    1 / ((N : ℝ) ^ φs) ^ 2 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, one_div, ← Real.rpow_neg hNpos.le]
  exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)

/-! ### The deterministic inclusions -/

/-- `φ^K N^{-2/3} ≤ 1/2` once `φ^K ≤ N^{1/6}` and `N ≥ 4`. -/
private lemma largeQ_phi_mul_small {K : ℝ} {N : ℕ} (hN : 4 ≤ N)
    (h : phi N ^ K ≤ (N : ℝ) ^ (1 / 6 : ℝ)) : phi N ^ K * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 / 2 := by
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h3 : (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) = ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_neg hNpos.le]; norm_num
  have hs : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hs0 : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hs2 : 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
  have hinv : ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hs0 (by norm_num)]
    simpa using hs2
  calc phi N ^ K * (N : ℝ) ^ (-(2 : ℝ) / 3)
      ≤ (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hNpos.le _)
    _ ≤ 1 / 2 := by rw [h3]; exact hinv

/-- The norm bound `‖H‖ ≤ 3` from (3.4) at `q = N^φs`. -/
private lemma largeQ_norm_le_three {Cn φs : ℝ} (hφs : 1 / 3 ≤ φs) {N : ℕ} (hN : 4 ≤ N)
    (hφ : phi N ^ Cn ≤ (N : ℝ) ^ (1 / 6 : ℝ)) {ω : Entries N}
    (hn : ω ∈ normEvent N Cn ((N : ℝ) ^ φs)) :
    ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3 := by
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues (symOfEntries_isHermitian ω)
  intro α
  rw [hσ α]
  refine (hn (σ α)).trans ?_
  have h1 := largeQ_inv_sq_le (N := N) (by omega) hφs
  have hs := largeQ_phi_mul_small hN hφ
  have hφ0 : 0 ≤ phi N ^ Cn :=
    Real.rpow_nonneg (by linarith [sc_one_le_phi (N := N) (by omega)]) _
  calc 2 + phi N ^ Cn * (1 / ((N : ℝ) ^ φs) ^ 2 + (N : ℝ) ^ (-(2 : ℝ) / 3))
      ≤ 2 + phi N ^ Cn * ((N : ℝ) ^ (-(2 : ℝ) / 3) + (N : ℝ) ^ (-(2 : ℝ) / 3)) := by gcongr
    _ = 2 + 2 * (phi N ^ Cn * (N : ℝ) ^ (-(2 : ℝ) / 3)) := by ring
    _ ≤ 3 := by linarith

/-- The local law (3.2) at `q = N^φs` with `η ≤ N^{-2/3}` gives (5.24) with the constant `Cl + 1`
(and any larger constant), when `φ ≥ 2`. -/
private lemma largeQ_524 {Cl C φs : ℝ} (hCl : 0 ≤ Cl) (hC : Cl + 1 ≤ C) (hφs : 1 / 3 ≤ φs)
    {N : ℕ} (hN : 3 ≤ N) (hφ2 : 2 ≤ phi N) {ω : Entries N}
    (hll : ω ∈ localLawEvent N Cl ((N : ℝ) ^ φs)) :
    ∀ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) →
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ C / (N * z.im) := by
  intro z hz hzle
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hφ1 : 1 ≤ phi N := by linarith
  obtain ⟨hre, hzim, hz10⟩ := hz
  have hCl1 : 1 ≤ phi N ^ Cl := Real.one_le_rpow hφ1 hCl
  have hCC : phi N ^ Cl ≤ phi N ^ C := Real.rpow_le_rpow_of_exponent_le hφ1 (by linarith)
  have hηpos : 0 < z.im := lt_of_le_of_lt (by positivity) hzim
  have hz' : z ∈ specDomain N Cl :=
    ⟨hre, lt_of_le_of_lt (div_le_div_of_nonneg_right hCC hNpos.le) hzim, hz10⟩
  refine ((hll z hz').1).trans ?_
  unfold avgErr
  set η := z.im with hη
  set q : ℝ := (N : ℝ) ^ φs with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hNpos _
  set s := Real.sqrt (kappa z.re + η) with hs
  have hκ : 0 ≤ kappa z.re := abs_nonneg _
  have hsη : Real.sqrt η ≤ s := Real.sqrt_le_sqrt (by linarith)
  have hsη0 : 0 < Real.sqrt η := Real.sqrt_pos.mpr hηpos
  -- `N η ≤ q² s`
  have hsq : Real.sqrt η ≤ (N : ℝ) ^ (-(1 : ℝ) / 3) := by
    rw [Real.sqrt_le_left (Real.rpow_nonneg hNpos.le _)]
    have : ((N : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 = (N : ℝ) ^ (-(2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
    rw [this]; exact hzle
  have hNe : (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3) = (N : ℝ) ^ ((2 : ℝ) / 3) := by
    have := Real.rpow_add hNpos 1 (-(1 : ℝ) / 3)
    rw [Real.rpow_one] at this
    rw [← this]; norm_num
  have hq2 : (N : ℝ) ^ ((2 : ℝ) / 3) ≤ q ^ 2 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hNη : (N : ℝ) * η ≤ q ^ 2 * s := by
    have h1 : η = Real.sqrt η * Real.sqrt η := (Real.mul_self_sqrt hηpos.le).symm
    calc (N : ℝ) * η = (N : ℝ) * Real.sqrt η * Real.sqrt η := by rw [mul_assoc, ← h1]
      _ ≤ (N : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 3) * Real.sqrt η := by gcongr
      _ = (N : ℝ) ^ ((2 : ℝ) / 3) * Real.sqrt η := by rw [hNe]
      _ ≤ q ^ 2 * Real.sqrt η := by gcongr
      _ ≤ q ^ 2 * s := by gcongr
  have hmin : min (1 / (q ^ 2 * s)) (1 / q) ≤ 1 / (N * η) :=
    (min_le_left _ _).trans (one_div_le_one_div_of_le (by positivity) hNη)
  have hw0 : 0 ≤ 1 / ((N : ℝ) * η) := by positivity
  calc phi N ^ Cl * (min (1 / (q ^ 2 * s)) (1 / q) + 1 / (N * η))
      ≤ phi N ^ Cl * (1 / (N * η) + 1 / (N * η)) := by gcongr
    _ = (2 * phi N ^ Cl) * (1 / (N * η)) := by ring
    _ ≤ phi N ^ C * (1 / (N * η)) := by
        apply mul_le_mul_of_nonneg_right _ hw0
        have hpow : phi N ^ C = phi N ^ Cl * phi N ^ (C - Cl) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
        have h1 : 1 ≤ phi N ^ (C - Cl) := Real.one_le_rpow hφ1 (by linarith)
        have h2 : phi N ^ (C - Cl) ≥ 2 := by
          have : phi N ^ (C - Cl) ≥ phi N ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hφ1 (by linarith)
          rw [Real.rpow_one] at this; linarith
        rw [hpow]; nlinarith
    _ = phi N ^ C / (N * η) := by ring

/-- The deviation allowed by (3.6) at `q = N^φs` is at most `2 φ^C N^{-2/3}` at every index. -/
private lemma largeQ_rig_dev {Cr φs : ℝ} (hφs : 1 / 3 ≤ φs) {N : ℕ} (hN : 3 ≤ N)
    {ω : Entries N} (hr : ω ∈ rigidityEvent N Cr ((N : ℝ) ^ φs)) (j : Fin N) :
    |eigAsc (symOfEntries_isHermitian ω) j - gammaLoc N ((j : ℕ) + 1)| ≤
      2 * phi N ^ Cr * (N : ℝ) ^ (-(2 : ℝ) / 3) := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hφ0 : 0 ≤ phi N ^ Cr := Real.rpow_nonneg (by linarith [sc_one_le_phi hN]) _
  refine (hr j).trans ?_
  have hj : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  have hmin : 1 ≤ min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ)) :=
    le_min (by have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) (by linarith)
  have h1 : (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hmin (by norm_num)
  have h2 := largeQ_inv_sq_le (N := N) (by omega) hφs
  have ht0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hNpos.le _
  calc phi N ^ Cr * ((min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
        (N : ℝ) ^ (-(2 : ℝ) / 3) + 1 / ((N : ℝ) ^ φs) ^ 2)
      ≤ phi N ^ Cr * (1 * (N : ℝ) ^ (-(2 : ℝ) / 3) + (N : ℝ) ^ (-(2 : ℝ) / 3)) := by
        gcongr
    _ = 2 * phi N ^ Cr * (N : ℝ) ^ (-(2 : ℝ) / 3) := by ring

/-- (5.25) from (3.6) at the last index, where `γ_N = 2`. -/
private lemma largeQ_525 {Cr C φs : ℝ} (hC : Cr + 1 ≤ C) (hφs : 1 / 3 ≤ φs)
    {N : ℕ} (hN : 3 ≤ N) (hφ2 : 2 ≤ phi N) {ω : Entries N}
    (hr : ω ∈ rigidityEvent N Cr ((N : ℝ) ^ φs)) :
    |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C := by
  have : NeZero N := ⟨by omega⟩
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hφ1 : 1 ≤ phi N := by linarith
  rw [lambdaMax_eq_eigAsc_last (symOfEntries_isHermitian ω)]
  have hdev := largeQ_rig_dev hφs hN hr
    ⟨N - 1, Nat.sub_lt (Nat.pos_of_neZero N) one_pos⟩
  have e : N - 1 + 1 = N := Nat.sub_add_cancel (by omega)
  simp only [e, gammaLoc_self (by omega : 1 ≤ N)] at hdev
  have hpos : 0 < (N : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hNpos _
  have hprod : (N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hNpos]; norm_num
  rw [abs_mul, abs_of_pos hpos]
  calc (N : ℝ) ^ ((2 : ℝ) / 3) * |eigAsc (symOfEntries_isHermitian ω)
        ⟨N - 1, Nat.sub_lt (Nat.pos_of_neZero N) one_pos⟩ - 2|
      ≤ (N : ℝ) ^ ((2 : ℝ) / 3) * (2 * phi N ^ Cr * (N : ℝ) ^ (-(2 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left hdev hpos.le
    _ = 2 * phi N ^ Cr := by
        rw [show (N : ℝ) ^ ((2 : ℝ) / 3) * (2 * phi N ^ Cr * (N : ℝ) ^ (-(2 : ℝ) / 3)) =
          2 * phi N ^ Cr * ((N : ℝ) ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-(2 : ℝ) / 3)) by ring, hprod,
          mul_one]
    _ ≤ phi N ^ C := by
        have hpow : phi N ^ C = phi N ^ Cr * phi N ^ (C - Cr) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
        have h2 : phi N ^ (C - Cr) ≥ 2 := by
          have : phi N ^ (C - Cr) ≥ phi N ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hφ1 (by linarith)
          rw [Real.rpow_one] at this; linarith
        have h0 : 0 ≤ phi N ^ Cr := Real.rpow_nonneg (by linarith) _
        rw [hpow]; nlinarith

/-- (5.26) from (3.6) and the edge behaviour `n_sc(x) ≤ Cs (x + 2)^{3/2}` of (5.13): the
eigenvalues within `2 φ^C N^{-2/3}` of `2` have increasing index at least `N - 1 - 8 Cs φ^{3C/2}`,
so there are at most `φ^{2C}` of them once `φ^{C/2} ≥ 8 Cs + 1`. -/
private lemma largeQ_526 {Cr C φs Cs : ℝ} (hCr : Cr ≤ C) (hC0 : 0 < C) (hφs : 1 / 3 ≤ φs)
    (hCs0 : 0 ≤ Cs) (hCs : ∀ x ∈ Set.Icc (-2 : ℝ) 1, nsc x ≤ Cs * (x + 2) ^ ((3 : ℝ) / 2))
    {N : ℕ} (hN : 3 ≤ N) (hφ2 : 2 ≤ phi N)
    (hδ : 4 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 3)
    (hbig : 8 * Cs + 1 ≤ phi N ^ (C / 2)) {ω : Entries N}
    (hr : ω ∈ rigidityEvent N Cr ((N : ℝ) ^ φs)) :
    ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
        2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C) := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hφ1 : 1 ≤ phi N := by linarith
  have hφ0 : 0 < phi N := by linarith
  have hPC : 0 ≤ phi N ^ C := Real.rpow_nonneg hφ0.le _
  have hNt : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hNpos _
  obtain ⟨σ, hσ⟩ := exists_perm_eigenvalues (symOfEntries_isHermitian ω)
  set r : ℝ := 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) with hr_def
  set δ : ℝ := 4 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) with hδ_def
  have hδ0 : 0 ≤ δ := by positivity
  have hδ2r : δ = 2 * r := by rw [hδ_def, hr_def]; ring
  set P : ℝ := phi N ^ (3 * C / 2) with hP_def
  have hP1 : 1 ≤ P := Real.one_le_rpow hφ1 (by linarith)
  set M : ℝ := 8 * Cs * P with hM_def
  have hM0 : 0 ≤ M := by positivity
  -- `δ^{3/2} = 8 P / N`
  have hδ32 : δ ^ ((3 : ℝ) / 2) = 8 * P / N := by
    have e4 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    have e1 : (phi N ^ C) ^ ((3 : ℝ) / 2) = P := by
      rw [← Real.rpow_mul hφ0.le, hP_def]; congr 1; ring
    have e2 : ((N : ℝ) ^ (-(2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = (N : ℝ)⁻¹ := by
      rw [← Real.rpow_mul hNpos.le, ← Real.rpow_neg_one]; congr 1; norm_num
    rw [hδ_def, Real.mul_rpow (by positivity) hNt.le, Real.mul_rpow (by norm_num) hPC, e4, e1, e2]
    ring
  -- every eigenvalue near `2` has a large increasing index
  have key : ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤ r →
      (N : ℝ) - 1 - ((σ α : Fin N) : ℕ) ≤ M := by
    intro α hα
    rw [hσ α] at hα
    set j : Fin N := σ α with hj
    have hdev := largeQ_rig_dev hφs hN hr j
    have hCC : phi N ^ Cr ≤ phi N ^ C := Real.rpow_le_rpow_of_exponent_le hφ1 hCr
    have hdev' : |eigAsc (symOfEntries_isHermitian ω) j - gammaLoc N ((j : ℕ) + 1)| ≤ r := by
      refine hdev.trans ?_
      rw [hr_def]
      gcongr
    have hγ : 2 - δ ≤ gammaLoc N ((j : ℕ) + 1) := by
      have h1 := (abs_le.mp hα).1
      have h2 := (abs_le.mp hdev').2
      linarith
    have hjN : (j : ℕ) + 1 ≤ N := j.isLt
    have hnsc := nsc_gammaLoc (N := N) (j := (j : ℕ) + 1) (by omega) hjN
    have hmono : nsc (2 - δ) ≤ nsc (gammaLoc N ((j : ℕ) + 1)) := monotone_nsc hγ
    have hneg := nsc_neg (2 - δ)
    have hup := hCs (-(2 - δ)) ⟨by linarith, by linarith⟩
    rw [show -(2 - δ) + 2 = δ by ring, hδ32] at hup
    have hfin : 1 - ((j : ℕ) + 1 : ℝ) / N ≤ Cs * (8 * P / N) := by
      have : ((((j : ℕ) + 1 : ℕ) : ℝ)) / N = ((j : ℕ) + 1 : ℝ) / N := by push_cast; ring
      rw [this] at hnsc
      linarith
    have h3 : (N : ℝ) - ((j : ℕ) + 1) ≤ Cs * (8 * P) := by
      have := mul_le_mul_of_nonneg_left hfin hNpos.le
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hNpos.ne', ← mul_div_assoc,
        mul_div_cancel₀ _ hNpos.ne'] at this
      linarith
    rw [hM_def]
    linarith
  -- counting
  have hcard : (Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
      r).card ≤ ⌊M⌋₊ + 1 := by
    have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun α =>
        |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤ r) (t := Finset.range (⌊M⌋₊ + 1))
      (fun α => N - 1 - ((σ α : Fin N) : ℕ)) (fun α hα => ?_) (fun a _ b _ hab => ?_)
    · simpa using h
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hα
      simp only [Finset.coe_range, Set.mem_Iio]
      have hlt : ((σ α : Fin N) : ℕ) < N := (σ α).isLt
      have hk := key α hα
      have : N - 1 - ((σ α : Fin N) : ℕ) ≤ ⌊M⌋₊ := by
        apply Nat.le_floor
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        linarith
      omega
    · have h1 : ((σ a : Fin N) : ℕ) < N := (σ a).isLt
      have h2 : ((σ b : Fin N) : ℕ) < N := (σ b).isLt
      have h3 : ((σ a : Fin N) : ℕ) = ((σ b : Fin N) : ℕ) := by
        simp only at hab
        omega
      exact σ.injective (Fin.ext h3)
  have hcardR : ((Finset.univ.filter fun α =>
      |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤ r).card : ℝ) ≤ M + 1 := by
    have h1 : ((⌊M⌋₊ : ℕ) : ℝ) ≤ M := Nat.floor_le hM0
    calc _ ≤ ((⌊M⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (⌊M⌋₊ : ℝ) + 1 := by push_cast; ring
      _ ≤ M + 1 := by linarith
  refine hcardR.trans ?_
  have hpow : phi N ^ (2 * C) = P * phi N ^ (C / 2) := by
    rw [hP_def, ← Real.rpow_add hφ0]; congr 1; ring
  rw [hpow, hM_def]
  nlinarith

/-- The three events (3.2), (3.4), (3.6) at `q = N^φs` imply the event of Lemma 5.6 with the
constant `C ≥ max(Cl, Cn, Cr) + 1`, for all large `N`. -/
private lemma largeQ_det {Cl Cn Cr φs C : ℝ} (hCl : 0 < Cl) (hφs : 1 / 3 < φs)
    (hC : max (max Cl Cn) Cr + 1 ≤ C) :
    ∃ N1 : ℕ, ∀ N ≥ N1, ∀ ω : Entries N, ω ∈ localLawEvent N Cl ((N : ℝ) ^ φs) →
      ω ∈ normEvent N Cn ((N : ℝ) ^ φs) → ω ∈ rigidityEvent N Cr ((N : ℝ) ^ φs) →
      ω ∈ edgeInputEvent N C := by
  obtain ⟨Cs, hCs1, hcomp⟩ := nsc_rhoSc_comparable
  have hClC : Cl + 1 ≤ C := by
    have := le_max_left Cl Cn
    have := le_max_left (max Cl Cn) Cr
    linarith
  have hCrC : Cr + 1 ≤ C := by
    have := le_max_right (max Cl Cn) Cr
    linarith
  have hC0 : 0 < C := by linarith
  have hev := (eventually_ge_atTop 16).and <|
    (tendsto_phi_atTop.eventually_ge_atTop 2).and <|
    (phi_rpow_le_rpow Cn (by norm_num : (0 : ℝ) < 1 / 6)).and <|
    (phi_rpow_le_rpow C (by norm_num : (0 : ℝ) < 1 / 6)).and <|
    largeQ_eventually_phi_rpow (half_pos hC0) (8 * Cs + 1)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  refine ⟨N1, fun N hN ω hll hn hr => ?_⟩
  obtain ⟨h16, hφ2, hφn, hφC, hbig⟩ := hN1 N hN
  have hφs' : 1 / 3 ≤ φs := hφs.le
  refine ⟨largeQ_norm_le_three hφs' (by omega) hφn hn,
    largeQ_524 hCl.le hClC hφs' (by omega) hφ2 hll,
    largeQ_525 hCrC hφs' (by omega) hφ2 hr, largeQ_526 (by linarith) hC0 hφs' (by linarith)
      (fun x hx => (hcomp x hx).1.2) (by omega) hφ2 ?_ hbig hr⟩
  have := largeQ_phi_mul_small (K := C) (by omega) hφC
  linarith

/-- The GOE entry laws have the support parameter `N^{2/5}` with one constant `c > 0`, for every
lower bound `Q ≤ N^{2/5}` and all large `N`. -/
private lemma largeQ_goe_support : ∃ c > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ Q : ℝ,
    Q ≤ (N : ℝ) ^ (2 / 5 : ℝ) → (goeLaws N).SupportParam Q c ((N : ℝ) ^ (2 / 5 : ℝ)) := by
  obtain ⟨cb, hcb, Nb, hb⟩ := goeLaws_boundedSupport (φs := 2 / 5) (by norm_num) (by norm_num)
  obtain ⟨ct, hct, Nt, ht⟩ := gaussianReal_tailVar (φs := 2 / 5) (by norm_num) (by norm_num)
  refine ⟨min cb ct, lt_min hcb hct, max Nb (max Nt 1), fun N hN Q hQ => ⟨hQ, ?_, ?_⟩⟩
  · have hNb : Nb ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hmono : Real.exp (-(N : ℝ) ^ cb) ≤ Real.exp (-(N : ℝ) ^ (min cb ct)) :=
      Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)))
    exact ⟨fun i => ((hb N hNb).1 i).trans (ENNReal.ofReal_le_ofReal hmono),
      fun p => ((hb N hNb).2 p).trans (ENNReal.ofReal_le_ofReal hmono)⟩
  · intro p
    have hNt : Nt ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hmono : Real.exp (-(N : ℝ) ^ ct) ≤ Real.exp (-(N : ℝ) ^ (min cb ct)) :=
      Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)))
    rw [goeLaws_off]
    refine (ht N hNt _ ?_).trans hmono
    have hNpos : (0 : ℝ) < N := by linarith
    push_cast
    rw [mul_one, div_eq_mul_inv]
    have : 0 ≤ (N : ℝ)⁻¹ := by positivity
    linarith

/-- A high-probability bound passes to a smaller class and to larger events from some `N` on. -/
private lemma largeQ_highProb_mono {ζ : ℝ} {Cls Cls' : ∀ N : ℕ, EntryLaws N → Prop}
    {Ω Ω' : ∀ N : ℕ, EntryLaws N → Set (Entries N)} (h : HighProbOn ζ Cls Ω)
    (hcls : ∀ N L, Cls' N L → Cls N L)
    (hsub : ∃ N1 : ℕ, ∀ N ≥ N1, ∀ L, Cls' N L → Ω N L ⊆ Ω' N L) :
    HighProbOn ζ Cls' Ω' := by
  obtain ⟨c, hc, C, hC, N0, h⟩ := h
  obtain ⟨N1, hsub⟩ := hsub
  exact ⟨c, hc, C, hC, max N0 N1, fun N hN L hL =>
    (measure_mono (Set.compl_subset_compl.mpr
      (hsub N (le_trans (le_max_right _ _) hN) L hL))).trans
      (h N (le_trans (le_max_left _ _) hN) L (hcls N L hL))⟩

/-- The event of Lemma 5.6 for the class of Lemma 3.5 (from Lemma 3.1 (2), (4) and
(3.2)), for every `C ≥ C0`. -/
theorem edgeInput_largeQ {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) :
    ∃ C₀ > (0 : ℝ), ∀ C ≥ C₀, HighProbOn 1 (LargeQClass C0 φs) (fun N _ => edgeInputEvent N C) := by
  have _ := hφs'
  obtain ⟨Cl, hCl, hll⟩ := localLaw (ζ := 1) (C0 := C0) (c := 1) one_pos hC0 one_pos
  obtain ⟨Cn, hCn, hn⟩ := norm_le_two_add (ζ := 1) (C0 := C0) (c := 1) one_pos hC0 one_pos
  obtain ⟨Cr, hCr, hr⟩ :=
    rigidity (ζ := 1) (C0 := C0) (c := 1) (φs := φs) one_pos hC0 one_pos hφs
  refine ⟨max (max Cl Cn) Cr + 1, by positivity, fun C hC => ?_⟩
  obtain ⟨N1, hN1⟩ := largeQ_det (Cr := Cr) (Cn := Cn) hCl hφs hC
  have hφs0 : 0 < φs := by linarith
  obtain ⟨N2, hN2⟩ :=
    eventually_atTop.1 ((phi_rpow_le_rpow Cl hφs0).and (phi_rpow_le_rpow Cn hφs0))
  refine largeQ_highProb_mono ((hll.inter hn).inter hr) (fun N L h => h.1)
    ⟨max N1 N2, fun N hN L hL ω hω => ?_⟩
  obtain ⟨⟨hωl, hωn⟩, hωr⟩ := hω
  obtain ⟨hl, hnn⟩ := hN2 N (le_trans (le_max_right _ _) hN)
  exact hN1 N (le_trans (le_max_left _ _) hN) ω
    (hωl _ ⟨hl, hL.2.boundedSupport 1, hL.2.tailVarOff 1⟩)
    (hωn _ ⟨hnn, hL.2.boundedSupport 1, hL.2.tailVarOff 1⟩)
    (hωr _ ⟨le_rfl, hL.2.boundedSupport 1, hL.2.tailVarOff 1⟩)

/-- The event of Lemma 5.6 for the GOE, for every `C ≥ C0`. -/
theorem edgeInput_goe :
    ∃ C₀ > (0 : ℝ), ∀ C ≥ C₀,
      HighProbOn 1 (fun N L => L = goeLaws N) (fun N _ => edgeInputEvent N C) := by
  obtain ⟨c, hc, Ng, hg⟩ := largeQ_goe_support
  obtain ⟨Cl, hCl, hll⟩ := localLaw (ζ := 1) (C0 := 1) (c := c) one_pos zero_le_one hc
  obtain ⟨Cn, hCn, hn⟩ := norm_le_two_add (ζ := 1) (C0 := 1) (c := c) one_pos zero_le_one hc
  obtain ⟨Cr, hCr, hr⟩ := rigidity (ζ := 1) (C0 := 1) (c := c) (φs := 2 / 5) one_pos zero_le_one
    hc (by norm_num)
  refine ⟨max (max Cl Cn) Cr + 1, by positivity, fun C hC => ?_⟩
  obtain ⟨N1, hN1⟩ := largeQ_det (Cr := Cr) (Cn := Cn) (φs := 2 / 5) hCl (by norm_num) hC
  obtain ⟨N2, hN2⟩ := eventually_atTop.1
    ((phi_rpow_le_rpow Cl (by norm_num : (0 : ℝ) < 2 / 5)).and
      (phi_rpow_le_rpow Cn (by norm_num : (0 : ℝ) < 2 / 5)))
  refine largeQ_highProb_mono ((hll.inter hn).inter hr)
    (fun N L h => by rw [h]; exact goeLaws_isGenWigner N)
    ⟨max (max N1 N2) Ng, fun N hN L hL ω hω => ?_⟩
  subst hL
  obtain ⟨⟨hωl, hωn⟩, hωr⟩ := hω
  have hN12 : max N1 N2 ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨hl, hnn⟩ := hN2 N (le_trans (le_max_right _ _) hN12)
  have hNg : Ng ≤ N := le_trans (le_max_right _ _) hN
  exact hN1 N (le_trans (le_max_left _ _) hN12) ω (hωl _ (hg N hNg _ hl)) (hωn _ (hg N hNg _ hnn))
    (hωr _ (hg N hNg _ le_rfl))

/-! ### Checks -/

/-- A high-probability bound for the event of Lemma 5.6 and laws `Ls N` of the class and of
total mass one, for all large `N`, give a point of the event for all large `N`: the complement
has probability at most `ε_N → 0`, while the whole space has probability `1`. -/
private lemma largeQ_nonempty_of_highProb {Cls : ∀ N : ℕ, EntryLaws N → Prop} {C : ℝ}
    (h : HighProbOn 1 Cls (fun N _ => edgeInputEvent N C)) (Ls : ∀ N : ℕ, EntryLaws N)
    (hL : ∀ᶠ N : ℕ in atTop, Cls N (Ls N) ∧ (Ls N).IsProb) :
    ∀ᶠ N : ℕ in atTop, (edgeInputEvent N C).Nonempty := by
  obtain ⟨ε, hε, hev⟩ := h.tendstoOneOn one_pos
  filter_upwards [hev, hε.eventually (gt_mem_nhds one_pos), hL] with N hN hεN ⟨hcls, hprob⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have := EntryLaws.isProbabilityMeasure_law hprob
  have h1 := hN (Ls N) hcls
  rw [hne, Set.compl_empty, measure_univ] at h1
  exact absurd (h1.trans_lt (ENNReal.ofReal_lt_one.mpr hεN)) (lt_irrefl _)

/-- For the GOE and the constants of `edgeInput_goe`, the event of Lemma 5.6 is nonempty for all
large `N`. -/
private lemma largeQ_goe_nonempty :
    ∃ C₀ > (0 : ℝ), ∀ C ≥ C₀, ∀ᶠ N : ℕ in atTop, (edgeInputEvent N C).Nonempty := by
  obtain ⟨C₀, hC₀, h⟩ := edgeInput_goe
  exact ⟨C₀, hC₀, fun C hC => largeQ_nonempty_of_highProb (h C hC) goeLaws
    (Eventually.of_forall fun N => ⟨rfl, (goeLaws_isGenWigner N).isProb⟩)⟩

/-- The class of Lemma 3.5 at `C0 = 1`, `φs = 2/5` contains the Rademacher laws for every
`N ≥ 32` (generalized Wigner with diagonal variance `2/N` and entries bounded by `N^{-2/5}`),
so the hypotheses of `edgeInput_largeQ` hold together at this point and its class is nonempty. -/
example : ∀ᶠ N : ℕ in atTop, LargeQClass 1 (2 / 5) N (radLaws N) := by
  filter_upwards [eventually_ge_atTop 32] with N hN
  exact ⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS hN⟩

/-- `edgeInput_largeQ` at `C0 = 1`, `φs = 2/5` and the Rademacher laws: the event of Lemma 5.6 is
nonempty for all large `N`, at every `C ≥ C₀`. -/
example : ∃ C₀ > (0 : ℝ), ∀ C ≥ C₀, ∀ᶠ N : ℕ in atTop, (edgeInputEvent N C).Nonempty := by
  obtain ⟨C₀, hC₀, h⟩ := edgeInput_largeQ (C0 := 1) (φs := 2 / 5) zero_le_one (by norm_num)
    (by norm_num)
  refine ⟨C₀, hC₀, fun C hC => largeQ_nonempty_of_highProb (h C hC) radLaws ?_⟩
  filter_upwards [eventually_ge_atTop 32] with N hN
  exact ⟨⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS hN⟩,
    (radLaws_isGenWigner (by omega)).isProb⟩

/-- The event of `edgeInput_goe` is nonempty for all large `N`, at every `C ≥ C₀`. -/
example : ∃ C₀ > (0 : ℝ), ∀ C ≥ C₀, ∀ᶠ N : ℕ in atTop, (edgeInputEvent N C).Nonempty :=
  largeQ_goe_nonempty

/-- Full witness for the event of Lemma 5.6: for the constants of `edgeInput_goe` and all large
`N` there is an `ω` with `‖H‖ ≤ 3`, (5.24) on `S(C) ∩ {Im z ≤ N^{-2/3}}` (a nonempty domain),
(5.25) and (5.26), and for this `ω` the conclusion of `abs_countIcc_sub_smoothCount_le'` holds
at `E = 2`, `ε = 1/20`, with `η = N^{-2/3-9/20}`, `ℓ₁ = N^{-2/3-3/20}`. -/
example : ∃ C₀ > (0 : ℝ), ∀ C ≥ C₀, ∃ C' > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∃ ω : Entries N,
    (∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3) ∧
    (∀ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) →
      ‖stieltjesM (symOfEntries ω) z - msc z‖ ≤ phi N ^ C / (N * z.im)) ∧
    (∃ z ∈ specDomain N C, z.im ≤ (N : ℝ) ^ (-(2 : ℝ) / 3)) ∧
    |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C ∧
    ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
        2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C) ∧
    |(countIcc (symOfEntries_isHermitian ω) 2 (edgeEL N C) : ℝ) -
        smoothCount (symOfEntries_isHermitian ω) ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * (1 / 20))) 2
          (edgeEL N C)| ≤
      C' * ((N : ℝ) ^ (-(2 : ℝ) * (1 / 20)) + countIcc (symOfEntries_isHermitian ω)
        (2 - (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * (1 / 20)))
        (2 + (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * (1 / 20)))) := by
  obtain ⟨C₀, hC₀, hne⟩ := largeQ_goe_nonempty
  refine ⟨C₀, hC₀, fun C hC => ?_⟩
  have hC0 : 0 < C := lt_of_lt_of_le hC₀ hC
  obtain ⟨C', hC', h'⟩ := abs_countIcc_sub_smoothCount_le' hC0
  obtain ⟨N0, hN0⟩ := h' (1 / 20) (by norm_num) (by norm_num)
  refine ⟨C', hC', ?_⟩
  filter_upwards [hne C hC, eventually_ge_atTop (max N0 3),
    window_scales hC0.le (ε := 1 / 20) (by norm_num) (by norm_num)] with N ⟨ω, hω⟩ hN hws
  obtain ⟨⟨h1, h2, h3, -⟩, -⟩ := hws
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hφ0 : 0 ≤ phi N ^ C := Real.rpow_nonneg (by linarith [sc_one_le_phi hN3]) _
  have hX : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hX23 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
  refine ⟨ω, hω.1, hω.2.1, ⟨⟨0, (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * (1 / 20))⟩, ⟨by simp, h1, by
      change (N : ℝ) ^ (-(2 : ℝ) / 3 - 3 * (1 / 20)) ≤ 10
      linarith⟩, h2⟩, hω.2.2.1, hω.2.2.2, ?_⟩
  exact hN0 N (le_trans (le_max_left _ _) hN) ω hω.1 hω.2.1 hω.2.2.1 hω.2.2.2 2
    (by rw [sub_self, abs_zero]; positivity)

#print axioms edgeInput_largeQ
#print axioms edgeInput_goe

end WEdgeNS
