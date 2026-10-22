import WEdgeNS.Model.Wigner

/-!
# Tail facts for the necessity part of Theorem 1.2

If (1.4) fails, `P(|x_12| ≥ s) ≥ c s^{-4}` along a sequence `s → ∞` (4.1), which yields
`P(|x_12| ≥ 4 √N) ≥ c N^{-2}` for infinitely many `N` and the bound in (4.6). Also a law that
satisfies Definition 1.1 but not (1.4).
-/

open MeasureTheory Filter Topology

namespace WEdgeNS

/-- (4.1): if (1.4) fails, then `s^4 P(|x| ≥ s) ≥ c` along a sequence `s → ∞`. -/
theorem frequently_tail_ge_of_not_tailCond {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ s in atTop, c ≤ s ^ 4 * (ν {x | s ≤ |x|}).toReal := by
  unfold TailCond at h
  rw [Metric.tendsto_nhds] at h
  push Not at h
  obtain ⟨ε, hε, hf⟩ := h
  refine ⟨ε, hε, hf.mono fun s hs => ?_⟩
  have h0 : 0 ≤ s ^ 4 * (ν {x | s ≤ |x|}).toReal :=
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg h0] at hs

/-- (4.6): the choice `N = ⌊(r/4)^2⌋`. -/
theorem floor_sq_div_four_bounds {r : ℝ} (hr : 4 ≤ r) :
    1 ≤ ⌊(r / 4) ^ 2⌋₊ ∧ 4 * Real.sqrt ⌊(r / 4) ^ 2⌋₊ ≤ r ∧
      r ^ 4 ≤ 1024 * (⌊(r / 4) ^ 2⌋₊ : ℝ) ^ 2 := by
  have hx : (1 : ℝ) ≤ (r / 4) ^ 2 := by
    have : (1 : ℝ) ≤ r / 4 := by linarith
    nlinarith
  have hN1 : 1 ≤ ⌊(r / 4) ^ 2⌋₊ := Nat.le_floor (by simpa using hx)
  have hNle : (⌊(r / 4) ^ 2⌋₊ : ℝ) ≤ (r / 4) ^ 2 := Nat.floor_le (by positivity)
  have hNlt : (r / 4) ^ 2 < ⌊(r / 4) ^ 2⌋₊ + 1 := Nat.lt_floor_add_one _
  have hN1' : (1 : ℝ) ≤ ⌊(r / 4) ^ 2⌋₊ := by exact_mod_cast hN1
  refine ⟨hN1, ?_, ?_⟩
  · have : Real.sqrt (⌊(r / 4) ^ 2⌋₊ : ℝ) ≤ r / 4 := by
      rw [Real.sqrt_le_left (by linarith)]
      exact hNle
    linarith
  · have h4 : r ^ 4 = 256 * ((r / 4) ^ 2) ^ 2 := by ring
    have hsq : ((r / 4) ^ 2) ^ 2 ≤ ((⌊(r / 4) ^ 2⌋₊ : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hNlt.le 2
    nlinarith

/-- (4.6), first step: if (1.4) fails, then `P(|x| ≥ 4 √N) ≥ c N^{-2}` for infinitely many `N`. -/
theorem frequently_tail_sqrt_ge {ν : Measure ℝ} [IsFiniteMeasure ν] (h : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ N : ℕ in atTop, c / (N : ℝ) ^ 2 ≤ (ν {x | 4 * Real.sqrt N ≤ |x|}).toReal := by
  obtain ⟨c₁, hc₁, hfreq⟩ := frequently_tail_ge_of_not_tailCond h
  refine ⟨c₁ / 1024, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨s, hsM, hs, hs4⟩ :=
    Filter.frequently_atTop.mp (hfreq.and_eventually (eventually_ge_atTop (4 : ℝ)))
      (4 * ((M : ℝ) + 1))
  obtain ⟨hN1, hsqrt, hpow⟩ := floor_sq_div_four_bounds hs4
  set N : ℕ := ⌊(s / 4) ^ 2⌋₊
  have hMN : M ≤ N := by
    refine le_trans (Nat.le_succ M) (Nat.le_floor ?_)
    have h1 : (M : ℝ) + 1 ≤ s / 4 := by linarith
    have h2 : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    push_cast
    nlinarith
  refine ⟨N, hMN, ?_⟩
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set P : ℝ := (ν {x | s ≤ |x|}).toReal
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  have hmono : P ≤ (ν {x | 4 * Real.sqrt N ≤ |x|}).toReal := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun x hx => ?_)
    exact le_trans hsqrt hx
  refine le_trans ?_ hmono
  rw [div_le_iff₀ (by positivity)]
  calc c₁ / 1024 ≤ (1024 * (N : ℝ) ^ 2 * P) / 1024 := by
        refine div_le_div_of_nonneg_right ?_ (by norm_num)
        calc c₁ ≤ s ^ 4 * P := hs
          _ ≤ 1024 * (N : ℝ) ^ 2 * P := mul_le_mul_of_nonneg_right hpow hP0
    _ = P * (N : ℝ) ^ 2 := by ring

/-- (4.6), second step: `(1 - p)^{N(N-1)/2} ≤ e^{-c/4}` when `c N^{-2} ≤ p ≤ 1`. -/
theorem one_sub_pow_choose_two_le {N : ℕ} (hN : 2 ≤ N) {c p : ℝ} (hc : 0 ≤ c)
    (hp : c / (N : ℝ) ^ 2 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ N.choose 2 ≤ Real.exp (-(c / 4)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hk : (N : ℝ) ^ 2 / 4 ≤ (N.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith
  have hp0 : 0 ≤ p := le_trans (by positivity) hp
  have h1 : (1 - p) ^ N.choose 2 ≤ (Real.exp (-p)) ^ N.choose 2 :=
    pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) _
  have h2 : (Real.exp (-p)) ^ N.choose 2 = Real.exp (-(p * N.choose 2)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  refine h1.trans (h2.le.trans (Real.exp_le_exp.mpr ?_))
  have : c / 4 ≤ p * N.choose 2 := by
    calc c / 4 = c / (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 / 4) := by field_simp
      _ ≤ p * (N.choose 2 : ℝ) := mul_le_mul hp hk (by positivity) hp0
  linarith

/-- The scale `2^{-1/2}` of the heavy-tailed example. -/
private noncomputable def tailC : ℝ := Real.sqrt (1 / 2)

private lemma tailC_sq : tailC ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)

private lemma tailC_pos : 0 < tailC := Real.sqrt_pos.mpr (by norm_num)

private lemma tailC_le_one : tailC ≤ 1 := by
  have := tailC_sq
  have := tailC_pos
  nlinarith

/-- The map `u ↦ 2^{-1/2} u^{-1/4}`. -/
private noncomputable def tailFun (u : ℝ) : ℝ := tailC * u ^ (-(1 / 4 : ℝ))

private lemma measurable_tailFun : Measurable tailFun :=
  (measurable_id.pow_const _).const_mul _

/-- The uniform law on `(0, 1)`. -/
private noncomputable def unifIoo : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

private instance : IsProbabilityMeasure unifIoo := ⟨by simp [unifIoo]⟩

/-- Law of `2^{-1/2} U^{-1/4}` with `U` uniform on `(0, 1)`: a one-sided law with
`P(X ≥ s) = 1 / (4 s^4)` for `s ≥ 2^{-1/2}`. -/
private noncomputable def tailHalf : Measure ℝ := unifIoo.map tailFun

private instance : IsProbabilityMeasure tailHalf := by
  unfold tailHalf
  infer_instance

/-- The symmetrisation of `tailHalf`. -/
private noncomputable def tailLaw : Measure ℝ := (2 : ENNReal)⁻¹ • (tailHalf + tailHalf.map Neg.neg)

private instance : IsProbabilityMeasure tailLaw := by
  refine ⟨?_⟩
  simp only [tailLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  rw [Measure.map_apply measurable_neg MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

private lemma tailLaw_map_neg : tailLaw.map Neg.neg = tailLaw := by
  unfold tailLaw
  rw [Measure.map_smul _ measurable_neg.aemeasurable, Measure.map_add _ _ measurable_neg,
    Measure.map_map measurable_neg measurable_neg]
  have : (Neg.neg ∘ Neg.neg : ℝ → ℝ) = id := funext fun x => neg_neg x
  rw [this, Measure.map_id, add_comm]

private lemma integral_id_tailLaw : ∫ x, x ∂tailLaw = 0 := by
  have h : ∫ x, (-x) ∂tailLaw = ∫ x, x ∂tailLaw := by
    have : tailLaw.IsNegInvariant := ⟨tailLaw_map_neg⟩
    exact integral_neg_eq_self (fun x : ℝ => x) tailLaw
  rw [integral_neg] at h
  linarith

private lemma tailFun_sq {u : ℝ} (hu : 0 < u) : tailFun u ^ 2 = 1 / 2 * u ^ (-(1 / 2 : ℝ)) := by
  unfold tailFun
  rw [mul_pow, tailC_sq, ← Real.rpow_two, ← Real.rpow_mul hu.le]
  norm_num

private lemma integrableOn_rpow_neg_half :
    IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))

private lemma integrable_sq_tailHalf : Integrable (fun x : ℝ => x ^ 2) tailHalf := by
  unfold tailHalf
  rw [integrable_map_measure (by fun_prop) measurable_tailFun.aemeasurable]
  have h : IntegrableOn (fun u : ℝ => 1 / 2 * u ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 1) :=
    integrableOn_rpow_neg_half.const_mul (1 / 2)
  exact IntegrableOn.congr_fun h (fun u hu => (tailFun_sq hu.1).symm) measurableSet_Ioo

private lemma integral_sq_tailHalf : ∫ x, x ^ 2 ∂tailHalf = 1 := by
  unfold tailHalf
  rw [integral_map measurable_tailFun.aemeasurable (by fun_prop)]
  change ∫ u in Set.Ioo (0 : ℝ) 1, tailFun u ^ 2 = 1
  rw [setIntegral_congr_fun measurableSet_Ioo (fun u hu => tailFun_sq hu.1), integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by norm_num))]
  norm_num

private lemma integrable_sq_map_neg : Integrable (fun x : ℝ => x ^ 2) (tailHalf.map Neg.neg) := by
  rw [integrable_map_measure (by fun_prop) measurable_neg.aemeasurable]
  simpa [Function.comp_def] using integrable_sq_tailHalf

private lemma integral_sq_map_neg : ∫ x, x ^ 2 ∂(tailHalf.map Neg.neg) = 1 := by
  rw [integral_map measurable_neg.aemeasurable (by fun_prop)]
  simpa using integral_sq_tailHalf

private lemma integrable_sq_tailLaw : Integrable (fun x : ℝ => x ^ 2) tailLaw := by
  unfold tailLaw
  exact (integrable_sq_tailHalf.add_measure integrable_sq_map_neg).smul_measure (by simp)

private lemma integral_sq_tailLaw : ∫ x, x ^ 2 ∂tailLaw = 1 := by
  unfold tailLaw
  rw [integral_smul_measure, integral_add_measure integrable_sq_tailHalf integrable_sq_map_neg,
    integral_sq_tailHalf, integral_sq_map_neg]
  simp [ENNReal.toReal_inv]
  norm_num

private lemma tailLaw_tail_ge {s : ℝ} (hs : 1 ≤ s) :
    1 / (4 * s ^ 4) ≤ (tailLaw {x | s ≤ |x|}).toReal := by
  have hs0 : 0 < s := by linarith
  have hA : MeasurableSet {x : ℝ | s ≤ |x|} := measurableSet_le measurable_const measurable_abs
  set t : ℝ := (tailC / s) ^ 4 with ht
  have ht1 : t ≤ 1 := by
    refine pow_le_one₀ (by have := tailC_pos; positivity) ?_
    rw [div_le_one hs0]
    exact tailC_le_one.trans hs
  have ht' : t = 1 / (4 * s ^ 4) := by
    have : tailC ^ 4 = 1 / 4 := by
      calc tailC ^ 4 = (tailC ^ 2) ^ 2 := by ring
        _ = 1 / 4 := by rw [tailC_sq]; norm_num
    rw [ht, div_pow, this]
    field_simp
  -- the set `(0, t)` is mapped into `{s ≤ |x|}`
  have hsub : Set.Ioo 0 t ⊆ tailFun ⁻¹' {x : ℝ | s ≤ |x|} := by
    intro u hu
    obtain ⟨hu0, hut⟩ := hu
    change s ≤ |tailFun u|
    set v : ℝ := u ^ (1 / 4 : ℝ) with hv
    have hv0 : 0 < v := Real.rpow_pos_of_pos hu0 _
    have hv4 : v ^ 4 = u := by
      rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
      norm_num
    have hvle : v ≤ tailC / s := by
      refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by have := tailC_pos; positivity) ?_
      rw [hv4]
      exact hut.le
    have hfun : tailFun u = tailC / v := by
      unfold tailFun
      rw [Real.rpow_neg hu0.le, ← hv, div_eq_mul_inv]
    rw [hfun, abs_of_pos (by have := tailC_pos; positivity), le_div_iff₀ hv0]
    rw [le_div_iff₀ hs0] at hvle
    linarith
  have hmu : ENNReal.ofReal t ≤ tailHalf {x : ℝ | s ≤ |x|} := by
    unfold tailHalf
    rw [Measure.map_apply measurable_tailFun hA]
    calc ENNReal.ofReal t = volume (Set.Ioo 0 t) := by simp
      _ = unifIoo (Set.Ioo 0 t) := by
        unfold unifIoo
        rw [Measure.restrict_apply measurableSet_Ioo,
          Set.inter_eq_left.mpr (Set.Ioo_subset_Ioo_right ht1)]
      _ ≤ unifIoo (tailFun ⁻¹' {x : ℝ | s ≤ |x|}) := measure_mono hsub
  have hneg : (tailHalf.map Neg.neg) {x : ℝ | s ≤ |x|} = tailHalf {x : ℝ | s ≤ |x|} := by
    rw [Measure.map_apply measurable_neg hA]
    congr 1
    ext x
    simp
  have hlaw : tailLaw {x : ℝ | s ≤ |x|} = tailHalf {x : ℝ | s ≤ |x|} := by
    unfold tailLaw
    rw [Measure.smul_apply, Measure.add_apply, hneg, smul_eq_mul, ← two_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  rw [← ht', ← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _), hlaw]
  exact hmu

private lemma not_tailCond_tailLaw : ¬ TailCond tailLaw := by
  intro hT
  have h1 := hT.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  obtain ⟨s, hs, hs1⟩ := (h1.and (eventually_ge_atTop (1 : ℝ))).exists
  have hs0 : 0 < s := by linarith
  have := mul_le_mul_of_nonneg_left (tailLaw_tail_ge hs1) (by positivity : 0 ≤ s ^ 4)
  have h2 : s ^ 4 * (1 / (4 * s ^ 4)) = 1 / 4 := by field_simp
  linarith

/-- There is a law satisfying Definition 1.1 (on and off the diagonal) for which (1.4) fails. -/
theorem exists_wignerLaws_not_tailCond : ∃ ν : Measure ℝ, WignerLaws ν ν ∧ ¬ TailCond ν := by
  exact ⟨tailLaw, ⟨inferInstance, inferInstance, integrable_sq_tailLaw, integrable_sq_tailLaw,
    integral_id_tailLaw, integral_sq_tailLaw, integral_id_tailLaw⟩, not_tailCond_tailLaw⟩

/-- The hypotheses of `one_sub_pow_choose_two_le` hold at `N = 3`, `c = 1`, `p = 1/9`. -/
example : (1 - (1 / 9 : ℝ)) ^ (3 : ℕ).choose 2 ≤ Real.exp (-((1 : ℝ) / 4)) :=
  one_sub_pow_choose_two_le (N := 3) (c := 1) (p := 1 / 9) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- A probability law with finite variance whose tail fails (1.4) and gives the bound of
`frequently_tail_sqrt_ge`. -/
example : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ¬ TailCond ν ∧
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ N : ℕ in atTop, c / (N : ℝ) ^ 2 ≤ (ν {x | 4 * Real.sqrt N ≤ |x|}).toReal := by
  obtain ⟨ν, hν, hT⟩ := exists_wignerLaws_not_tailCond
  have := hν.prob
  exact ⟨ν, hν.prob, hT, frequently_tail_sqrt_ge hT⟩

#print axioms frequently_tail_ge_of_not_tailCond
#print axioms floor_sq_div_four_bounds
#print axioms frequently_tail_sqrt_ge
#print axioms one_sub_pow_choose_two_le
#print axioms exists_wignerLaws_not_tailCond

end WEdgeNS
