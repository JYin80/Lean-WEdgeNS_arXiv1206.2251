import WEdgeNS.Comparison.NormSmallQ
import WEdgeNS.Comparison.LocalSmallQ
import WEdgeNS.Semicircle.Rigidity
import WEdgeNS.Semicircle.Counting

/-!
# Rigidity and the edge inputs for small support (Theorem 3.6)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

-- `1 ≤ φ`, the Rademacher laws in the class, and the smallness of `φ^C N^{-2/3}`.
open private one_le_phi from WEdgeNS.Model.HighProb
open private nsq_radLaws_class from WEdgeNS.Comparison.NormSmallQ
open private oos_window_inst from WEdgeNS.LocalLaw.OutOfSpectrum

/-! ### Elementary facts on `φ` -/

/-- `φ` is eventually at least any given constant. -/
private lemma rsq_eventually_phi_ge (X : ℝ) : ∀ᶠ N : ℕ in atTop, X ≤ phi N := by
  have h : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually_ge_atTop X, eventually_ge_atTop 16] with N h1 h2
  exact h1.trans (log_le_phi h2)

/-- `φ^y` is eventually at least any given constant, for `y > 0`. -/
private lemma rsq_eventually_phi_rpow_ge (X : ℝ) {y : ℝ} (hy : 0 < y) :
    ∀ᶠ N : ℕ in atTop, X ≤ phi N ^ y := by
  have h : Tendsto (fun N : ℕ => phi N) atTop atTop :=
    tendsto_atTop_mono' atTop
      (by filter_upwards [eventually_ge_atTop 16] with N hN using log_le_phi hN)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact ((tendsto_rpow_atTop hy).comp h).eventually_ge_atTop X

/-- `N^{1/2} = √N ≥ 4` for `N ≥ 16`. -/
private lemma rsq_four_le_rpow_half {N : ℕ} (hN : 16 ≤ N) : (4 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
  have h16 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le (by linarith)

/-! ### The counting bound (3.13) from the norm bound and the local law -/

/-- On the events of the norm bound and the local law, the counting bound (3.13) holds with
exponent `C_b + 2`, for all large `N`. -/
private lemma rsq_count_det {Ca Cb : ℝ} (hCb : 0 < Cb) :
    ∃ N1 : ℕ, ∀ N ≥ N1, ∀ (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian),
      (∀ α, |hH.eigenvalues α| ≤ 2 + phi N ^ Ca * (N : ℝ) ^ (-(2 : ℝ) / 3)) →
      (∀ z ∈ specDomain N Cb, ‖stieltjesM H z - msc z‖ ≤ phi N ^ Cb / (N * z.im)) →
      ∀ E : ℝ, |countFn hH E - nsc E| ≤ phi N ^ (Cb + 2) / N := by
  obtain ⟨Cc, hCc, hcount⟩ := abs_countFn_sub_nsc_le
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((phi_rpow_le_rpow Ca (c := 2 / 3) (by norm_num)).and
      ((phi_rpow_le_rpow Cb (c := 1 / 2) (by norm_num)).and
        ((rsq_eventually_phi_ge (3 * Cc)).and (eventually_ge_atTop 16))))
  refine ⟨N1, fun N hN H hH hnorm hlocal E => ?_⟩
  obtain ⟨h1, h2, h3, h16⟩ := hN1 N hN
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hNpos : (0 : ℝ) < N := by linarith
  have hφ1 : 1 ≤ phi N := one_le_phi (by omega)
  have hφpos : 0 < phi N := by linarith
  set U := phi N ^ Cb with hUdef
  have hU : 1 ≤ U := Real.one_le_rpow hφ1 hCb.le
  have hy0a : 1 / (N : ℝ) ≤ 2 * U / N := by
    apply div_le_div_of_nonneg_right _ hNpos.le
    linarith
  have hy0b : 2 * U / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]
    have h4 := rsq_four_le_rpow_half h16
    have hs : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add hNpos]; norm_num
    nlinarith
  have hev : ∀ α, |hH.eigenvalues α| ≤ 3 := by
    intro α
    have hm : phi N ^ Ca * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 := by
      calc phi N ^ Ca * (N : ℝ) ^ (-(2 : ℝ) / 3)
          ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hNpos.le _)
        _ = 1 := by rw [← Real.rpow_add hNpos]; norm_num
    linarith [hnorm α]
  have hyp : ∀ x y : ℝ, |x| ≤ 4 → 2 * U / N ≤ y → y ≤ 1 →
      ‖stieltjesM H (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤ U / (N * y) := by
    intro x y hx hy hy1
    have hre : ((x : ℂ) + y * Complex.I).re = x := by simp
    have him : ((x : ℂ) + y * Complex.I).im = y := by simp
    have hUN : U / N < 2 * U / N := by
      apply div_lt_div_of_pos_right _ hNpos
      linarith
    have hxx := abs_le.mp hx
    have := hlocal _ ⟨by rw [hre, abs_le]; constructor <;> linarith [hxx.1, hxx.2],
      by rw [him]; linarith, by rw [him]; linarith⟩
    rwa [him] at this
  have key := hcount N (by omega) H hH U (2 * U / N) hU hy0a hy0b hev hyp E
  have hNy : (N : ℝ) * (2 * U / N) = 2 * U := by field_simp
  rw [hNy] at key
  have hlog : Real.log N ≤ phi N := log_le_phi h16
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hexp : phi N ^ (Cb + 2) = U * phi N ^ 2 := by
    rw [Real.rpow_add hφpos, Real.rpow_two]
  rw [hexp]
  refine key.trans ?_
  apply div_le_div_of_nonneg_right _ hNpos.le
  have hU0 : 0 ≤ U := by linarith
  calc Cc * (U + 2 * U) * Real.log N = U * (3 * Cc) * Real.log N := by ring
    _ ≤ U * phi N * phi N := by gcongr
    _ = U * phi N ^ 2 := by ring

/-! ### Rigidity (3.12) and the counting bound (3.13) -/

/-- On the events of the norm bound and the local law, rigidity (3.12) and the counting bound
(3.13) hold with exponent `2 max(C_b + 2, C_a) + 1`, for all large `N`. -/
private lemma rsq_rig_det {Ca Cb : ℝ} (hCb : 0 < Cb) :
    ∃ N1 : ℕ, ∀ N ≥ N1, ∀ (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian),
      (∀ α, |hH.eigenvalues α| ≤ 2 + phi N ^ Ca * (N : ℝ) ^ (-(2 : ℝ) / 3)) →
      (∀ z ∈ specDomain N Cb, ‖stieltjesM H z - msc z‖ ≤ phi N ^ Cb / (N * z.im)) →
      (∀ j : Fin N, |eigAsc hH j - gammaLoc N ((j : ℕ) + 1)| ≤
          phi N ^ (2 * max (Cb + 2) Ca + 1) *
            (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
              (N : ℝ) ^ (-(2 : ℝ) / 3)) ∧
        ∀ E : ℝ, |countFn hH E - nsc E| ≤ phi N ^ (2 * max (Cb + 2) Ca + 1) / N := by
  obtain ⟨Ne, hNe⟩ := rsq_count_det (Ca := Ca) hCb
  obtain ⟨Ce, hCe, hrig⟩ := abs_eigAsc_sub_gammaLoc_le
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((rsq_eventually_phi_ge Ce).and (eventually_ge_atTop (max Ne 16)))
  refine ⟨N1, fun N hN H hH hnorm hlocal => ?_⟩
  obtain ⟨hCeφ, hNmax⟩ := hN1 N hN
  have hNe' : Ne ≤ N := le_trans (le_max_left _ _) hNmax
  have h16 : 16 ≤ N := le_trans (le_max_right _ _) hNmax
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hNpos : (0 : ℝ) < N := by linarith
  have hφ1 : 1 ≤ phi N := one_le_phi (by omega)
  have hφpos : 0 < phi N := by linarith
  have hcount := hNe N hNe' H hH hnorm hlocal
  set Ct := max (Cb + 2) Ca with hCt
  have hCt1 : Cb + 2 ≤ Ct := le_max_left _ _
  have hCt2 : Ca ≤ Ct := le_max_right _ _
  have ht : 1 ≤ phi N ^ Ct := Real.one_le_rpow hφ1 (by linarith)
  have hcount' : ∀ E, |countFn hH E - nsc E| ≤ phi N ^ Ct / N := fun E =>
    (hcount E).trans (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hφ1 hCt1) hNpos.le)
  have hnorm' : ∀ α, |hH.eigenvalues α| ≤ 2 + phi N ^ Ct * (N : ℝ) ^ (-(2 : ℝ) / 3) := fun α =>
    (hnorm α).trans (by
      have := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hφ1 hCt2)
        (Real.rpow_nonneg hNpos.le (-(2 : ℝ) / 3))
      linarith)
  have hexp : phi N ^ (2 * Ct + 1) = phi N * (phi N ^ Ct) ^ 2 := by
    rw [Real.rpow_add hφpos, Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul hφpos.le]
    push_cast
    ring_nf
  refine ⟨fun j => ?_, fun E => ?_⟩
  · have h := hrig N (by omega) H hH (phi N ^ Ct) ht hcount' hnorm' j
    have hmin : 0 ≤ (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) := by
      apply Real.rpow_nonneg
      have : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
      exact le_min (by positivity) (by linarith)
    have hn : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hNpos.le _
    rw [hexp]
    refine h.trans ?_
    have hq : 0 ≤ (phi N ^ Ct) ^ 2 := by positivity
    have h1 : Ce * (phi N ^ Ct) ^ 2 ≤ phi N * (phi N ^ Ct) ^ 2 :=
      mul_le_mul_of_nonneg_right hCeφ hq
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hmin) hn
  · refine (hcount' E).trans (div_le_div_of_nonneg_right ?_ hNpos.le)
    exact Real.rpow_le_rpow_of_exponent_le hφ1 (by linarith)

/-- Theorem 3.6: rigidity (3.12) for every `j` and the counting bound (3.13) for
every `E`, with high probability; `C` and the constants of `HighProbOn` depend only on
`(C1, φs)`. -/
theorem rigidity_smallQ {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ C > (0 : ℝ), HighProbOn 1 (SmallQClass C1 φs)
      (fun N _ => {ω | (∀ j : Fin N,
          |eigAsc (symOfEntries_isHermitian ω) j - gammaLoc N ((j : ℕ) + 1)| ≤
            phi N ^ C * (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
              (N : ℝ) ^ (-(2 : ℝ) / 3)) ∧
        ∀ E : ℝ, |countFn (symOfEntries_isHermitian ω) E - nsc E| ≤ phi N ^ C / N}) := by
  obtain ⟨Ca, hCa, ha⟩ := abs_eigenvalues_le_smallQ (C1 := C1) hφs
  obtain ⟨Cb, hCb, hb⟩ := stieltjes_local_smallQ (C1 := C1) hφs
  obtain ⟨N1, hN1⟩ := rsq_rig_det (Ca := Ca) hCb
  refine ⟨2 * max (Cb + 2) Ca + 1, by positivity, ?_⟩
  refine (ha.inter hb).mono_eventually (fun _ _ h => h) ⟨N1, fun N hN L _ ω hω => ?_⟩
  exact hN1 N hN (symOfEntries ω) (symOfEntries_isHermitian ω) hω.1 hω.2

/-! ### The edge inputs (5.25)–(5.26) -/

/-- Rigidity at the last index and the counting bound at two energies near the edge give (5.25)
and (5.26) for every exponent `C ≥ C_r`, for all large `N`. -/
private lemma rsq_edge_det {Cr C : ℝ} (hCr : 0 < Cr) (hC : Cr ≤ C) :
    ∃ N1 : ℕ, ∀ N ≥ N1, ∀ (H : Matrix (Fin N) (Fin N) ℝ) (hH : H.IsHermitian),
      (∀ j : Fin N, |eigAsc hH j - gammaLoc N ((j : ℕ) + 1)| ≤
          phi N ^ Cr * (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
            (N : ℝ) ^ (-(2 : ℝ) / 3)) →
      (∀ E : ℝ, |countFn hH E - nsc E| ≤ phi N ^ Cr / N) →
      |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax H - 2)| ≤ phi N ^ C ∧
        ((Finset.univ.filter fun α => |hH.eigenvalues α - 2| ≤
            2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C) := by
  obtain ⟨Cs, hCs1, hcomp⟩ := nsc_rhoSc_comparable
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((phi_rpow_le_rpow C (c := 1 / 6) (by norm_num)).and
      ((rsq_eventually_phi_rpow_ge (8 * Cs + 2) (y := C / 2) (by linarith)).and
        (eventually_ge_atTop 16)))
  refine ⟨N1, fun N hN H hH hrigj hcount => ?_⟩
  obtain ⟨h6, hCs, h16⟩ := hN1 N hN
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hNpos : (0 : ℝ) < N := by linarith
  have hφ1 : 1 ≤ phi N := one_le_phi (by omega)
  have hφpos : 0 < phi N := by linarith
  have : NeZero N := ⟨by omega⟩
  have hn0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hNpos _
  have hC0 : 0 < C := by linarith
  have hφC : 0 < phi N ^ C := Real.rpow_pos_of_pos hφpos _
  refine ⟨?_, ?_⟩
  · -- (5.25): rigidity at the last index, `γ_N = 2`
    have hj : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h1 := hrigj ⟨N - 1, by omega⟩
    have hγ : gammaLoc N ((⟨N - 1, by omega⟩ : Fin N).val + 1) = 2 := by
      have : (⟨N - 1, by omega⟩ : Fin N).val + 1 = N := by simp only; omega
      rw [this]
      exact gammaLoc_self (by omega)
    have hmin : min ((((⟨N - 1, by omega⟩ : Fin N) : ℕ) : ℝ) + 1)
        ((N : ℝ) - (((⟨N - 1, by omega⟩ : Fin N) : ℕ) : ℝ)) = 1 := by
      simp only [hj]
      rw [show (N : ℝ) - 1 + 1 = N by ring, show (N : ℝ) - ((N : ℝ) - 1) = 1 by ring]
      exact min_eq_right (by linarith)
    rw [hγ, hmin, Real.one_rpow, mul_one, ← lambdaMax_eq_eigAsc_last hH] at h1
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hNpos _)]
    calc (N : ℝ) ^ ((2 : ℝ) / 3) * |lambdaMax H - 2|
        ≤ (N : ℝ) ^ ((2 : ℝ) / 3) * (phi N ^ Cr * (N : ℝ) ^ (-(2 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hNpos.le _)
      _ = phi N ^ Cr := by
          rw [mul_left_comm, ← Real.rpow_add hNpos]; norm_num
      _ ≤ phi N ^ C := Real.rpow_le_rpow_of_exponent_le hφ1 hC
  · -- (5.26): the count between `2 - 2w` and `2 + w`
    set w := 2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) with hw
    have hw0 : 0 < w := by positivity
    have hx1 : 2 * w ≤ 1 := by
      have h46 : phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        calc phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)
            ≤ (N : ℝ) ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
              mul_le_mul_of_nonneg_right h6 hn0.le
          _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hNpos]; norm_num
      have h4 := rsq_four_le_rpow_half h16
      have hsq : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 4 := by
        rw [Real.rpow_neg hNpos.le, inv_le_comm₀ (Real.rpow_pos_of_pos hNpos _) (by norm_num)]
        linarith
      have : 2 * w = 4 * (phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) := by rw [hw]; ring
      linarith
    -- the set of eigenvalue indices in the window lies between the two counting levels
    set A := Finset.univ.filter fun α => hH.eigenvalues α ≤ 2 + w with hA
    set B := Finset.univ.filter fun α => hH.eigenvalues α ≤ 2 - 2 * w with hB
    set S := Finset.univ.filter fun α => |hH.eigenvalues α - 2| ≤ w with hS
    have hdisj : Disjoint S B := by
      rw [Finset.disjoint_left]
      intro α hαS hαB
      simp only [hS, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hαS hαB
      have := (abs_le.mp hαS).1
      linarith
    have hsub : S ∪ B ⊆ A := by
      intro α hα
      rcases Finset.mem_union.mp hα with h | h
      · simp only [hS, hA, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
        linarith [(abs_le.mp h).2]
      · simp only [hB, hA, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
        linarith
    have hcardN : S.card + B.card ≤ A.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hsub
    have hcardR : (S.card : ℝ) + B.card ≤ A.card := by exact_mod_cast hcardN
    have hcA : (A.card : ℝ) = N * countFn hH (2 + w) := by
      unfold countFn; rw [← hA]; field_simp
    have hcB : (B.card : ℝ) = N * countFn hH (2 - 2 * w) := by
      unfold countFn; rw [← hB]; field_simp
    have hcE2 := (abs_le.mp (hcount (2 + w))).2
    have hcE1 := (abs_le.mp (hcount (2 - 2 * w))).1
    have hn2 : nsc (2 + w) = 1 := nsc_eq_one (by linarith)
    have hn1 : nsc (2 - 2 * w) = 1 - nsc (2 * w - 2) := by
      rw [← nsc_neg]; congr 1; ring
    have htail : nsc (2 * w - 2) ≤ Cs * (2 * w) ^ ((3 : ℝ) / 2) := by
      have := (hcomp (2 * w - 2) ⟨by linarith, by linarith⟩).1.2
      rwa [show 2 * w - 2 + 2 = 2 * w by ring] at this
    have hx32 : (2 * w) ^ ((3 : ℝ) / 2) = 8 * phi N ^ (3 * C / 2) / N := by
      have e : 2 * w = 4 * (phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)) := by rw [hw]; ring
      have h4 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [e, Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hφC.le hn0.le,
        h4, ← Real.rpow_mul hφpos.le, ← Real.rpow_mul hNpos.le]
      have : (-(2 : ℝ) / 3) * ((3 : ℝ) / 2) = -1 := by norm_num
      rw [this, Real.rpow_neg_one, show C * ((3 : ℝ) / 2) = 3 * C / 2 by ring]
      field_simp
    have hNc : (N : ℝ) * (Cs * (8 * phi N ^ (3 * C / 2) / N)) = 8 * Cs * phi N ^ (3 * C / 2) := by
      field_simp
    have hmain : (S.card : ℝ) ≤ 8 * Cs * phi N ^ (3 * C / 2) + 2 * phi N ^ Cr := by
      have hcAB : (S.card : ℝ) ≤ N * (countFn hH (2 + w) - countFn hH (2 - 2 * w)) := by
        rw [mul_sub, ← hcA, ← hcB]; linarith
      have hd : countFn hH (2 + w) - countFn hH (2 - 2 * w) ≤
          nsc (2 * w - 2) + 2 * (phi N ^ Cr / N) := by linarith
      calc (S.card : ℝ) ≤ N * (nsc (2 * w - 2) + 2 * (phi N ^ Cr / N)) :=
            hcAB.trans (mul_le_mul_of_nonneg_left hd hNpos.le)
        _ = N * nsc (2 * w - 2) + 2 * phi N ^ Cr := by field_simp
        _ ≤ N * (Cs * (8 * phi N ^ (3 * C / 2) / N)) + 2 * phi N ^ Cr := by
            rw [← hx32]
            have := mul_le_mul_of_nonneg_left htail hNpos.le
            linarith
        _ = _ := by rw [hNc]
    have hCr32 : phi N ^ Cr ≤ phi N ^ (3 * C / 2) :=
      Real.rpow_le_rpow_of_exponent_le hφ1 (by linarith)
    have h2C : phi N ^ (2 * C) = phi N ^ (3 * C / 2) * phi N ^ (C / 2) := by
      rw [← Real.rpow_add hφpos]; congr 1; ring
    have hpos32 : 0 < phi N ^ (3 * C / 2) := Real.rpow_pos_of_pos hφpos _
    rw [h2C]
    calc (S.card : ℝ) ≤ 8 * Cs * phi N ^ (3 * C / 2) + 2 * phi N ^ Cr := hmain
      _ ≤ (8 * Cs + 2) * phi N ^ (3 * C / 2) := by nlinarith
      _ ≤ phi N ^ (C / 2) * phi N ^ (3 * C / 2) :=
          mul_le_mul_of_nonneg_right hCs hpos32.le
      _ = _ := mul_comm _ _

/-- The inputs (5.25)–(5.26) of Lemma 5.6, for every `C ≥ C0`:
`|N^{2/3}(λ_N - 2)| ≤ φ^C` and at most `φ^{2C}` eigenvalues in
`[2 - 2φ^C N^{-2/3}, 2 + 2φ^C N^{-2/3}]`. -/
theorem edge_inputs_smallQ {C1 φs : ℝ} (hφs : 0 < φs) :
    ∃ C0 > (0 : ℝ), ∀ C ≥ C0, HighProbOn 1 (SmallQClass C1 φs)
      (fun N _ => {ω | |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C ∧
        ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
            2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C)}) := by
  obtain ⟨Cr, hCr, hrig⟩ := rigidity_smallQ (C1 := C1) hφs
  refine ⟨Cr, hCr, fun C hC => ?_⟩
  obtain ⟨N1, hN1⟩ := rsq_edge_det hCr hC
  refine hrig.mono_eventually (fun _ _ h => h) ⟨N1, fun N hN L _ ω hω => ?_⟩
  exact hN1 N hN (symOfEntries ω) (symOfEntries_isHermitian ω) hω.1 hω.2

/-! ### Compiled checks -/

/-- The class of both theorems is nonempty for all large `N`: it contains the Rademacher laws,
with `C1 = 2` and `φs = 1/4`. -/
example : ∀ᶠ N : ℕ in atTop, ∃ L : EntryLaws N, SmallQClass 2 (1 / 4) N L := by
  filter_upwards [nsq_radLaws_class] with N h
  exact ⟨_, h⟩

/-- `rigidity_smallQ` at `C1 = 2`, `φs = 1/4` for the Rademacher laws: for all large `N` the laws
lie in the class, the rigidity radius `φ^C N^{-2/3}` at the edge indices and the counting radius
`φ^C / N` lie in `(0, 1/2]`, and the probability bound of the theorem applies to them. -/
example : ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C' : ℕ, ∀ᶠ N : ℕ in atTop,
    SmallQClass 2 (1 / 4) N (radLaws N) ∧
    0 < phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ∧
    phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 / 2 ∧
    0 < phi N ^ C / N ∧ phi N ^ C / N ≤ 1 / 2 ∧
    (radLaws N).law {ω | (∀ j : Fin N,
          |eigAsc (symOfEntries_isHermitian ω) j - gammaLoc N ((j : ℕ) + 1)| ≤
            phi N ^ C * (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
              (N : ℝ) ^ (-(2 : ℝ) / 3)) ∧
        ∀ E : ℝ, |countFn (symOfEntries_isHermitian ω) E - nsc E| ≤ phi N ^ C / N}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨C, hC, c, hc, C', -, N0, h⟩ := rigidity_smallQ (C1 := 2) (φs := 1 / 4) (by norm_num)
  refine ⟨C, hC, c, hc, C', ?_⟩
  filter_upwards [nsq_radLaws_class, eventually_ge_atTop N0, oos_window_inst C,
    eventually_ge_atTop 3] with N hcl hN hw h3
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have h1 : 0 < phi N ^ C := Real.rpow_pos_of_pos (by rw [phi_eq_exp h3]; exact Real.exp_pos _) C
  have h2 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hNpos _
  have h4 : phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 / 2 := by linarith
  have h5 : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  refine ⟨hcl, mul_pos h1 h2, h4, div_pos h1 hNpos, ?_, h N hN _ hcl⟩
  calc phi N ^ C / N = phi N ^ C * (1 / N) := by ring
    _ ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) := mul_le_mul_of_nonneg_left h5 h1.le
    _ ≤ 1 / 2 := h4

/-- `edge_inputs_smallQ` at `C1 = 2`, `φs = 1/4` for the Rademacher laws and `C = C0`: for all
large `N` the laws lie in the class, the window half-width `2 φ^C N^{-2/3}` lies in `(0, 1]`, the
permitted count `φ^{2C}` is at least `1`, and the probability bound of the theorem applies to
them. -/
example : ∃ C0 > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C' : ℕ, ∀ᶠ N : ℕ in atTop,
    SmallQClass 2 (1 / 4) N (radLaws N) ∧
    0 < 2 * phi N ^ C0 * (N : ℝ) ^ (-(2 : ℝ) / 3) ∧
    2 * phi N ^ C0 * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 ∧ 1 ≤ phi N ^ (2 * C0) ∧
    (radLaws N).law {ω | |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤
          phi N ^ C0 ∧
        ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
            2 * phi N ^ C0 * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C0)}ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨C0, hC0, h⟩ := edge_inputs_smallQ (C1 := 2) (φs := 1 / 4) (by norm_num)
  obtain ⟨c, hc, C', -, N0, h⟩ := h C0 le_rfl
  refine ⟨C0, hC0, c, hc, C', ?_⟩
  filter_upwards [nsq_radLaws_class, eventually_ge_atTop N0, oos_window_inst C0,
    eventually_ge_atTop 3] with N hcl hN hw h3
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hφ1 : 1 ≤ phi N := one_le_phi h3
  have h1 : 0 < phi N ^ C0 := Real.rpow_pos_of_pos (by linarith) C0
  have h2 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hNpos _
  exact ⟨hcl, by positivity, by linarith, Real.one_le_rpow hφ1 (by linarith), h N hN _ hcl⟩

#print axioms rigidity_smallQ
#print axioms edge_inputs_smallQ

end WEdgeNS
