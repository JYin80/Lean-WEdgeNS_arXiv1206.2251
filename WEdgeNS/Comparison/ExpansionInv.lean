import WEdgeNS.Comparison.Expansion

/-!
# The inverse expectation expansion of one entry (Lemma 6.5)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

open private expU expU_apply expA expansion_identity expA_bound expansion_mem_highIdx
  expansion_evalW_wordP_zero expansion_abs_moment_le expansion_moments expansion_coeff_le
  expansion_rpow_pow expansion_eventually_le_phi expansion_eventually_log_le expansion_poly
  expansion_err_le expansion_good_le expansion_bad_le expansion_final
  expansion_matchedPair_radLaws from WEdgeNS.Comparison.Expansion

/-- (6.25) for the interpolations of a matched pair, with the threshold `0` of (6.24): the
coefficients `Ã_α` are bounded by `N^{-|α|φq/10}`, and by `(ξ + 1)² M log N (Λ/q)^{|α|}` with
`Λ = 2 M (s + 1)(ξ + 1)`, `M = max(C1, 1)`. -/
private lemma expansionInv_coeffs {N : ℕ} {C1 q φq : ℝ} {Lv Lw : EntryLaws N}
    (hmp : MatchedPair C1 q Lv Lw) (γ : ℕ) (hq0 : 0 < q) (hqsq : q ^ 2 ≤ N)
    (hqN : (N : ℝ) ^ φq ≤ q) (hφq : 0 < φq) (hN1 : 1 ≤ (N : ℝ)) (hlog1 : 1 ≤ Real.log N)
    (e : Fin N ⊕ OffDiag N) (s ξ : ℕ)
    (hP0 : ((ξ : ℝ) + 1) ^ 2 * (max C1 1 * Real.log N) *
      (2 * max C1 1 * ((s : ℝ) + 1) * ((ξ : ℝ) + 1)) ≤ (N : ℝ) ^ (φq / 12)) (α : Fin s → ℕ) :
    |expA s ξ 0 ((interp (lexPos N) γ Lv Lw).entryMoment e) α| ≤
        (N : ℝ) ^ (-((∑ t, α t : ℕ) : ℝ) * φq / 10) ∧
      |expA s ξ 0 ((interp (lexPos N) γ Lv Lw).entryMoment e) α| ≤
        ((ξ : ℝ) + 1) ^ 2 * (max C1 1 * Real.log N) *
          ((2 * max C1 1 * ((s : ℝ) + 1) * ((ξ : ℝ) + 1)) * q⁻¹) ^ (∑ t, α t) := by
  set M := max C1 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.2 hq0.le
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hξ0 : (0 : ℝ) ≤ ξ := Nat.cast_nonneg _
  have hmpL := hmp.interp γ
  obtain ⟨_, hn1, hnk⟩ := expansion_moments hmpL hq0 e
  set n := (interp (lexPos N) γ Lv Lw).entryMoment e with hndef
  have hNinv : (N : ℝ)⁻¹ ≤ q⁻¹ ^ 2 := by
    rw [inv_pow]; exact inv_anti₀ (by positivity) hqsq
  have hnM : ∀ k, 0 < k → |n k| ≤ M * q⁻¹ ^ k := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      rw [hn1, abs_zero]; positivity
    · refine (hnk k hk2).trans ?_
      calc M / N * q⁻¹ ^ (k - 2) = M * (N : ℝ)⁻¹ * q⁻¹ ^ (k - 2) := by ring
        _ ≤ M * q⁻¹ ^ 2 * q⁻¹ ^ (k - 2) := by gcongr
        _ = M * q⁻¹ ^ k := by rw [mul_assoc, ← pow_add]; congr 2; omega
  set Λ : ℝ := 2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1) with hΛdef
  have hΛ1 : 1 ≤ Λ := by
    have h1 : (1 : ℝ) ≤ ((s : ℝ) + 1) * ((ξ : ℝ) + 1) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have h2 : (1 : ℝ) ≤ 2 * M := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 * M * (((s : ℝ) + 1) * ((ξ : ℝ) + 1)) := mul_le_mul h2 h1 (by norm_num) (by linarith)
      _ = Λ := by rw [hΛdef]; ring
  have hnθ : ∀ c : ℕ, |n (c + 1)| * ((s : ℝ) * ξ) ^ (c + 1) ≤ (Λ * q⁻¹ / 2) ^ (c + 1) := by
    intro c
    have h1 := hnM (c + 1) (by omega)
    calc |n (c + 1)| * ((s : ℝ) * ξ) ^ (c + 1) ≤ M * q⁻¹ ^ (c + 1) * ((s : ℝ) * ξ) ^ (c + 1) := by
          gcongr
      _ = M * ((s : ℝ) * ξ * q⁻¹) ^ (c + 1) := by ring
      _ ≤ M ^ (c + 1) * (((s : ℝ) + 1) * ((ξ : ℝ) + 1) * q⁻¹) ^ (c + 1) := by
          gcongr
          · calc M = M ^ 1 := (pow_one M).symm
              _ ≤ M ^ (c + 1) := pow_le_pow_right₀ hM1 (by omega)
          · linarith
          · linarith
      _ = (Λ * q⁻¹ / 2) ^ (c + 1) := by rw [hΛdef, ← mul_pow]; ring_nf
  have hsρ : (s : ℝ) * q⁻¹ ≤ Λ * q⁻¹ := by
    refine mul_le_mul_of_nonneg_right ?_ hqi0
    calc (s : ℝ) = 1 * ((s : ℝ) + 0) * 1 := by ring
      _ ≤ 2 * M * ((s : ℝ) + 1) * ((ξ : ℝ) + 1) := by gcongr <;> linarith
      _ = Λ := by rw [hΛdef]
  have hθ0 : 0 ≤ Λ * q⁻¹ := by positivity
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hAθ := expA_bound s ξ 0 n hθ0 hM0 hqi0 hsρ hnθ hnM α
  have hMlog : M ≤ M * Real.log N := le_mul_of_one_le_right hM0 hlog1
  refine ⟨?_, hAθ.trans (by gcongr)⟩
  by_cases hα : α ∈ highIdx s 0 ξ
  · have hK1 : 1 ≤ ∑ t, α t := ((expansion_mem_highIdx α).1 hα).1
    have hx : 1 ≤ ((ξ : ℝ) + 1) ^ 2 * M :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hM1
    have hP' : ((ξ : ℝ) + 1) ^ 2 * M * Λ ≤ (N : ℝ) ^ (φq / 12) := by
      refine le_trans ?_ hP0
      gcongr
    have hβ : M ≤ M * (N : ℝ) ^ (-(0 : ℝ)) := by rw [neg_zero, Real.rpow_zero, mul_one]
    have hexp : ((∑ t, α t : ℕ) : ℝ) / 12 - (((∑ t, α t : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) ≤
        -((∑ t, α t : ℕ) : ℝ) / 10 := by
      have : (0 : ℝ) ≤ ((∑ t, α t : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [Nat.cast_zero, sub_zero]
      linarith
    have h := expansion_coeff_le (ξ := ξ) (K := ∑ t, α t) (m := 0) (β := M) (x := M) (Λ := Λ)
      (q := q) (φq := φq) (r := 0) (d := 10) hN1 (Nat.zero_le _) hK1 hβ hx hΛ1 hP' hq0 hqN
      hφq hexp
    have e1 : ((ξ : ℝ) + 1) ^ 2 * (M * q ^ 0) * (Λ * q⁻¹) ^ (∑ t, α t) =
        ((ξ : ℝ) + 1) ^ 2 * M * (Λ * q⁻¹) ^ (∑ t, α t) := by ring
    have e2 : -(0 : ℝ) - ((∑ t, α t : ℕ) : ℝ) * φq / 10 = -((∑ t, α t : ℕ) : ℝ) * φq / 10 := by
      ring
    rw [e1, e2] at h
    exact hAθ.trans h
  · simp only [expA, hα, ↓reduceIte, abs_zero]
    positivity

/-- Lemma 6.5, (6.24)–(6.25): `E ∏ S = E ∏ R + Σ_{1 ≤ |α| ≤ ξ} Ã_α E P_{γ,α} ∏ S`
up to `4^s N^{-ζ}`, with `|Ã_α| ≤ N^{-|α|φq/10}`. -/
theorem expectation_expansion_inv {C1 φq Ks : ℝ} (hφq : 0 < φq) (hKs : 0 < Ks) :
    ∃ C0 > (0 : ℝ), ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, PairInterpClass C1 φq N L →
      ∀ (e : Fin N ⊕ OffDiag N) (ζ : ℝ), 1 ≤ ζ → ζ ≤ phi N ^ 2 →
      ∀ s : ℕ, (s : ℝ) ≤ Ks * phi N ^ 2 →
      ∃ A : (Fin s → ℕ) → ℝ, (∀ α, |A α| ≤ (N : ℝ) ^ (-((∑ t, α t : ℕ) : ℝ) * φq / 10)) ∧
        ∀ z ∈ specDomain N C0, ∀ w : Word N, w.length = s →
          ‖(∫ ω, evalWord (resS z ω) (msc z) w ∂L.law)
            - (∫ ω, evalWord (resR e z ω) (msc z) w ∂L.law)
            - ∑ α ∈ highIdx s 0 (xiOf ζ φq),
                (A α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w) ∂L.law‖
            ≤ 4 ^ s * (N : ℝ) ^ (-ζ) := by
  obtain ⟨C0, hC0, c, hc, C', hC', N1, hN1⟩ := highProb_goodEvent (C1 := C1) hφq
  set M : ℝ := max C1 1 with hMdef
  set a : ℝ := Ks + 2 / φq + 2 with hadef
  have hM1 : 1 ≤ M := le_max_right _ _
  have h2φ : 0 < 2 / φq := by positivity
  have ha1 : 1 ≤ a := by linarith
  have hev := ((eventually_ge_atTop N1).and (eventually_ge_atTop 16)).and
    (((expansion_eventually_le_phi (64 * M ^ 2 * a ^ 4)).and
      (phi_rpow_le_rpow 10 (by positivity : (0 : ℝ) < φq / 12))).and
      (expansion_eventually_log_le ((6 * a + 4 + C') / c)))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨C0, hC0, N0, fun N hN L hL e ζ hζ1 hζ2 s hs => ?_⟩
  obtain ⟨⟨hNN1, hN16⟩, ⟨hAφ, hφ10⟩, hDlog⟩ := hN0 N hN
  have hbad := hN1 N hNN1 L hL
  obtain ⟨Lv, Lw, q, γ, hmp, hqN, rfl⟩ := hL
  clear hev hN0 hN1
  -- facts on `N`, `φ` and `q`
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0r : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    have h1 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    have h2 : (1 : ℝ) < Real.log 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    linarith
  have hφlog : Real.log N ≤ phi N := log_le_phi hN16
  have hφ1 : 1 ≤ phi N := hlog1.trans hφlog
  have hq1 : 1 ≤ q := le_trans (Real.one_le_rpow hN1r hφq.le) hqN
  have hq0 : 0 < q := by linarith
  have hmpL := hmp.interp γ
  have hLp := hmpL.isProb_v
  have hn0 := (expansion_moments hmpL hq0 e).1
  -- `q² ≤ N` and `2 φq ≤ 1`
  have hqsq : q ^ 2 ≤ N := by
    let p0 : OffDiag N := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
    have := hLp.off p0
    have h := expansion_abs_moment_le (hmpL.supp_v.2 p0) 0 2 (by decide) (by norm_num)
    have h2 : ∫ x, (-x) ^ 2 ∂((interp (lexPos N) γ Lv Lw).off p0) = (N : ℝ)⁻¹ := by
      simp_rw [neg_sq]; exact hmpL.var_off p0
    rw [h2, abs_of_nonneg (by positivity)] at h
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one, Nat.sub_zero,
      inv_pow] at h
    exact (inv_le_inv₀ hN0r (by positivity)).1 h
  have hφq2 : 2 * φq ≤ 1 := by
    have h1 : (N : ℝ) ^ (φq * (2 : ℕ)) ≤ (N : ℝ) ^ (1 : ℝ) := by
      rw [← expansion_rpow_pow hN0r.le, Real.rpow_one]
      exact (pow_le_pow_left₀ (by positivity) hqN 2).trans hqsq
    have := (Real.rpow_le_rpow_left_iff (by linarith : (1 : ℝ) < N)).1 h1
    push_cast at this
    linarith
  -- the truncation order `ξ`
  have hξge : 2 * ζ / φq ≤ xiOf ζ φq := Nat.le_ceil _
  set ξ := xiOf ζ φq with hξdef
  have hφξ : 2 * ζ ≤ φq * ξ := by
    rw [div_le_iff₀ hφq] at hξge; linarith
  have hZa : (s : ℝ) + ξ + 1 ≤ a * phi N ^ 2 := by
    have hξlt : (ξ : ℝ) < 2 * ζ / φq + 1 := Nat.ceil_lt_add_one (by positivity)
    have hφ2 : 1 ≤ phi N ^ 2 := one_le_pow₀ hφ1
    have hξR : (ξ : ℝ) ≤ 2 / φq * phi N ^ 2 + 1 := by
      have : 2 * ζ / φq ≤ 2 / φq * phi N ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hφq]; linarith
      linarith
    have : (s : ℝ) + ξ + 1 ≤ Ks * phi N ^ 2 + 2 / φq * phi N ^ 2 + 2 * phi N ^ 2 := by
      linarith
    calc (s : ℝ) + ξ + 1 ≤ Ks * phi N ^ 2 + 2 / φq * phi N ^ 2 + 2 * phi N ^ 2 := this
      _ = a * phi N ^ 2 := by rw [hadef]; ring
  have hT : 64 * M ^ 2 * a ^ 4 * phi N ^ 9 ≤ (N : ℝ) ^ (φq / 12) := by
    have h10 : phi N ^ (10 : ℝ) = phi N ^ (10 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (phi N) 10
    calc 64 * M ^ 2 * a ^ 4 * phi N ^ 9 ≤ phi N * phi N ^ 9 := by gcongr
      _ = phi N ^ (10 : ℝ) := by rw [h10]; ring
      _ ≤ _ := hφ10
  obtain ⟨hP0, hΓ, hY, hsq, hZN⟩ := expansion_poly (s := s) (ξ := ξ) hN1r hM1 ha1 hφ1 hφlog hφq
    hφq2 hqN hZa hT
  -- the coefficients `Ã_α`
  have hA := expansionInv_coeffs hmp γ hq0 hqsq hqN hφq hN1r hlog1 e s ξ hP0
  set n := (interp (lexPos N) γ Lv Lw).entryMoment e with hndef
  have hcb1 : ∀ K : ℕ, (N : ℝ) ^ (-(K : ℝ) * φq / 10) ≤ 1 := by
    intro K
    refine Real.rpow_le_one_of_one_le_of_nonpos hN1r ?_
    have : (0 : ℝ) ≤ K * φq := by positivity
    have h : -(K : ℝ) * φq / 10 = -(K * φq / 10) := by ring
    rw [h]
    have := div_nonneg this (by norm_num : (0 : ℝ) ≤ 10)
    linarith
  refine ⟨expA s ξ 0 n, fun α => (hA α).1, fun z hz w hw => ?_⟩
  -- the expansion at `z` and `w`
  have hzim : 0 < z.im :=
    lt_of_le_of_lt (div_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _)
      (Nat.cast_nonneg N)) hz.2.1
  have hB : 1 / z.im ≤ N := by
    have h1 : 1 ≤ phi N ^ C0 := Real.one_le_rpow hφ1 hC0.le
    have h2 : 1 / (N : ℝ) < z.im :=
      lt_of_le_of_lt (div_le_div_of_nonneg_right h1 hN0r.le) hz.2.1
    rw [div_le_iff₀ hzim]
    rw [div_lt_iff₀ hN0r] at h2
    linarith
  set X : (Fin s → ℕ) → ℂ := fun κ => ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn κ) w)
    ∂(interp (lexPos N) γ Lv Lw).law with hXdef
  set Y : (Fin s → ℕ) → ℂ := fun κ => ∫ ω, evalW (resR e z ω) (msc z) (wordP e (List.ofFn κ) w)
    ∂(interp (lexPos N) γ Lv Lw).law with hYdef
  have hX0 : ∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) γ Lv Lw).law = X 0 := by
    rw [hXdef]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact (expansion_evalW_wordP_zero _ _ e w hw).symm
  have hY0 : ∫ ω, evalWord (resR e z ω) (msc z) w ∂(interp (lexPos N) γ Lv Lw).law =
      ∑ k ∈ Finset.range (0 + 1), (n k : ℂ) * ∑ κ ∈ Finset.Nat.antidiagonalTuple s k, Y κ := by
    rw [zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_right,
      Finset.sum_singleton, hn0, Complex.ofReal_one, one_mul, hYdef]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact (expansion_evalW_wordP_zero _ _ e w hw).symm
  have hid := expansion_identity s ξ 0 n (Nat.zero_le _) hn0 X Y
  set P := ((interp (lexPos N) γ Lv Lw).law (goodEvent N C0)ᶜ).toReal with hPdef
  set Wc : ℝ := (1 + ((ξ : ℝ) + 1) * ((s : ℝ) * ξ + 1) ^ ξ) * 2 ^ ξ * ((N : ℝ) + 1) ^ (s + ξ)
    with hWcdef
  have herr : ∀ κ : Fin s → ℕ, ∑ t, κ t ≤ ξ → ‖(X - (Y + expU ℂ s ξ n Y)) κ‖ ≤
      2 ^ (∑ t, κ t) * 4 ^ (s + ∑ t, κ t + 2) *
        (4 * ((s + ∑ t, κ t : ℕ) : ℝ) / q) ^ (ξ - ∑ t, κ t + 1) + Wc * P :=
    fun κ hκ => expansion_err_le hLp hq0 hq1 hmpL.supp_v hz hB e w hw ξ hsq κ hκ
  have herr0 : ‖(X - (Y + expU ℂ s ξ n Y)) 0‖ ≤
      4 ^ (s + 2) * (4 * (s : ℝ) / q) ^ (ξ + 1) + Wc * P := by
    have := herr 0 (by simp)
    simpa using this
  have hP0' : 0 ≤ P := ENNReal.toReal_nonneg
  have hWc0 : 0 ≤ Wc := by positivity
  have hPbound : P ≤ (N : ℝ) ^ (C' : ℝ) * Real.exp (-c * phi N ^ 3) := by
    have h3 : phi N ^ (3 : ℝ) = phi N ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (phi N) 3
    rw [hPdef, Real.rpow_natCast, ← h3]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
  have hgood2 := expansion_good_le (s := s) (ξ := ξ) (ζ := ζ) hN1r hq0 hqN (by positivity) hΓ
    (by positivity) hY hφξ
  have hD : (6 * a + 4 + (C' : ℝ)) * Real.log N ≤ c * phi N := by
    have := mul_le_mul_of_nonneg_left hDlog hc.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at this
  have hbad2 := expansion_bad_le (s := s) (ξ := ξ) (a := a) hN16 hZN (by push_cast; exact hZa)
    hζ2 hφ1 hlog1 (Nat.cast_nonneg C') hD hPbound hP0'
  calc _ = ‖(X - (Y + expU ℂ s ξ n Y)) 0 - ∑ α ∈ highIdx s 0 ξ,
        (expA s ξ 0 n α : ℂ) * (X - (Y + expU ℂ s ξ n Y)) α‖ := by
        rw [hX0, hY0]; exact congrArg (fun x => ‖x‖) hid
    _ ≤ 4 ^ s * (N : ℝ) ^ (-ζ) :=
        expansion_final _ _ hq0 (by positivity) (by positivity) hWc0 hP0' herr0
          (fun α hα => herr α ((expansion_mem_highIdx α).1 hα).2) (fun α => (hA α).2)
          (fun α => (hA α).1.trans (hcb1 _)) hgood2 hbad2

/-! ### Compiled checks at a concrete nondegenerate point

The class `PairInterpClass 2 (2/5)` contains, for all large `N`, every interpolation `H_γ` of the
Rademacher laws against themselves (`q = N^{2/5}`); Lemma 6.5, (6.24)–(6.25) at these laws. -/

/-- The class `PairInterpClass 2 (2/5)` of Lemma 6.5 is nonempty for all large `N`. -/
example : ∀ᶠ N : ℕ in atTop, ∀ γ : ℕ,
    PairInterpClass 2 (2 / 5) N (interp (lexPos N) γ (radLaws N) (radLaws N)) := by
  filter_upwards [expansion_matchedPair_radLaws] with N h γ
  exact ⟨radLaws N, radLaws N, _, γ, h, le_rfl, rfl⟩

/-- `expectation_expansion_inv` for `C1 = 2`, `φq = 2/5`, `K_s = 1`, at every interpolation `H_γ`
of the Rademacher laws, every entry `e`, `ζ = 1` and words of length `s = 2`: all hypotheses hold
for all large `N`. -/
example : ∃ C0 > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ (γ : ℕ) (e : Fin N ⊕ OffDiag N),
    ∃ A : (Fin 2 → ℕ) → ℝ,
      (∀ α, |A α| ≤ (N : ℝ) ^ (-((∑ t, α t : ℕ) : ℝ) * (2 / 5) / 10)) ∧
      ∀ z ∈ specDomain N C0, ∀ w : Word N, w.length = 2 →
        ‖(∫ ω, evalWord (resS z ω) (msc z) w ∂(interp (lexPos N) γ (radLaws N) (radLaws N)).law)
          - (∫ ω, evalWord (resR e z ω) (msc z) w
              ∂(interp (lexPos N) γ (radLaws N) (radLaws N)).law)
          - ∑ α ∈ highIdx 2 0 (xiOf 1 (2 / 5)),
              (A α : ℂ) * ∫ ω, evalW (resS z ω) (msc z) (wordP e (List.ofFn α) w)
                ∂(interp (lexPos N) γ (radLaws N) (radLaws N)).law‖
          ≤ 4 ^ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨C0, hC0, N0, h⟩ := expectation_expansion_inv (C1 := 2) (φq := 2 / 5) (Ks := 1)
    (by norm_num) (by norm_num)
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [expansion_matchedPair_radLaws, eventually_ge_atTop N0,
    expansion_eventually_le_phi 2] with N hmp hN hφ γ e
  have hφ2 : (2 : ℝ) ≤ phi N ^ 2 := by nlinarith
  exact h N hN _ ⟨radLaws N, radLaws N, _, γ, hmp, le_rfl, rfl⟩ e 1 le_rfl (by linarith) 2
    (by push_cast; linarith)

#print axioms expectation_expansion_inv

end WEdgeNS
