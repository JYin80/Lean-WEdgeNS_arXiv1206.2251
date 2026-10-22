import WEdgeNS.EdgeUniv.EdgeProb
import WEdgeNS.EdgeUniv.Window

/-!
# Edge universality from the edge event and a Green function comparison
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- (5.15) (and [26] (6.25)) as a hypothesis on pairs of laws, with rate `N^{-κ+Cε}` and test
functions with four derivatives. -/
def GreenCompHyp (Pair : ∀ N : ℕ, EntryLaws N → EntryLaws N → Prop) (κ : ℝ) : Prop :=
  ∀ CF : ℝ, ∃ ε₀ > 0, ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ N0 : ℕ, ∀ N ≥ N0,
    ∀ Lv Lw : EntryLaws N, Pair N Lv Lw → ∀ F : ℝ → ℝ, ContDiff ℝ 4 F →
      (∀ n ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv n F x| ≤ CF * (1 + |x|) ^ CF) →
      ∀ E₁ E₂ : ℝ, |E₁ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        |E₂ - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        |∫ ω, F (N * ∫ y in E₁..E₂,
              (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩).im) ∂Lv.law -
          ∫ ω, F (N * ∫ y in E₁..E₂,
              (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩).im) ∂Lw.law| ≤
          (N : ℝ) ^ (-κ + C * ε)

/-- `N^C exp(-c φ) ≤ N^{-D} / 4` for all large `N` (Definition 2.3 with `ζ = 1`). -/
private lemma inputsComparison_rate {c : ℝ} (hc : 0 < c) (C : ℕ) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ C * Real.exp (-c * phi N ^ (1 : ℝ)) ≤ (N : ℝ) ^ (-D) / 4 := by
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3, (Real.tendsto_log_atTop.comp hl).eventually_ge_atTop 2,
    hl.eventually_ge_atTop (|C + D + 2| / c), hl.eventually_ge_atTop (Real.log 4 / 2)]
    with N hN hu hL hL4
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  simp only [Function.comp] at hu
  have hexp : Real.log N = Real.exp (Real.log (Real.log N)) := (Real.exp_log hLpos).symm
  have hbig : Real.log N ^ 2 ≤ phi N ^ (1 : ℝ) := by
    rw [Real.rpow_one, phi_eq_exp hN]
    conv_lhs => rw [hexp, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have hcL : C + D + 2 ≤ c * Real.log N := by
    have := (div_le_iff₀ hc).mp hL
    linarith [le_abs_self (C + D + 2)]
  have hkey : (C + D + 2) * Real.log N ≤ c * phi N ^ (1 : ℝ) := by nlinarith
  have h4 : (4 : ℝ) ≤ Real.exp (2 * Real.log N) := by
    rw [← Real.exp_log (show (0 : ℝ) < 4 by norm_num)]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos hNpos,
    ← Real.exp_add]
  calc Real.exp (Real.log N * C + -c * phi N ^ (1 : ℝ))
      ≤ Real.exp (Real.log N * -D - 2 * Real.log N) := Real.exp_le_exp.mpr (by nlinarith)
    _ = Real.exp (Real.log N * -D) / Real.exp (2 * Real.log N) := by rw [Real.exp_sub]
    _ ≤ Real.exp (Real.log N * -D) / 4 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h4

/-- One half of (5.27) inside the window: the sandwich of `P(λ_N < E)` for the law `A` at
`E = 2 + (t + N^{-ε}) N^{-2/3}`, the comparison of the smoothed traces of `A` and `B`, and the
sandwich for `B` at `E + N^{-2/3-ε}` give
`P_A(N^{2/3}(λ_N - 2) ≤ t) ≤ P_B(N^{2/3}(λ_N - 2) ≤ t + 2N^{-ε}) + r + p_A + p_B`. -/
private lemma inputsComparison_step {N : ℕ} {C ε r pA pB : ℝ} (hN : 3 ≤ N)
    {A B : EntryLaws N} (hA : A.IsProb) (hB : B.IsProb) {IA IB : ℝ → ℝ}
    (hSA : ∀ E, |E - 2| ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) →
      (A.law {ω | lambdaMax (symOfEntries ω) < E}).toReal ≤
        IA (E + (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) + pA)
    (hSB : ∀ E, |E - 2| ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) →
      IB (E - (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) / 2) - pB ≤
        (B.law {ω | lambdaMax (symOfEntries ω) < E}).toReal)
    (hAB : ∀ a, |a - 2| ≤ phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3) → IA a - IB a ≤ r)
    {t : ℝ} (ht : |t| + 2 * (N : ℝ) ^ (-ε) ≤ phi N ^ C) :
    edgeCdfL A t ≤ edgeCdfL B (t + 2 * (N : ℝ) ^ (-ε)) + r + pA + pB := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : (0 : ℝ) < N := by linarith
  have := isProbabilityMeasure_law hA
  have := isProbabilityMeasure_law hB
  set p0 := (N : ℝ) ^ (-(2 : ℝ) / 3) with hp0def
  set u := (N : ℝ) ^ (-ε) with hudef
  have hp0 : 0 < p0 := Real.rpow_pos_of_pos hX _
  have hu : 0 < u := Real.rpow_pos_of_pos hX _
  have hq : (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) = u * p0 := by
    rw [sub_eq_add_neg, Real.rpow_add hX, mul_comm]
  have hpp : (N : ℝ) ^ ((2 : ℝ) / 3) * p0 = 1 := by
    rw [hp0def, ← Real.rpow_add hX]; norm_num
  -- the two energies
  have hEa : |2 + t * p0 + u * p0 - 2| ≤ phi N ^ C * p0 := by
    rw [show 2 + t * p0 + u * p0 - 2 = (t + u) * p0 by ring, abs_mul, abs_of_pos hp0]
    refine mul_le_mul_of_nonneg_right ?_ hp0.le
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_pos hu]; linarith
  have hEb : |2 + t * p0 + u * p0 + u * p0 - 2| ≤ phi N ^ C * p0 := by
    rw [show 2 + t * p0 + u * p0 + u * p0 - 2 = (t + 2 * u) * p0 by ring, abs_mul,
      abs_of_pos hp0]
    refine mul_le_mul_of_nonneg_right ?_ hp0.le
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_pos (by linarith : 0 < 2 * u)]; linarith
  have hEm : |2 + t * p0 + u * p0 + u * p0 / 2 - 2| ≤ phi N ^ C * p0 := by
    rw [show 2 + t * p0 + u * p0 + u * p0 / 2 - 2 = (t + 3 / 2 * u) * p0 by ring, abs_mul,
      abs_of_pos hp0]
    refine mul_le_mul_of_nonneg_right ?_ hp0.le
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_pos (by linarith : 0 < 3 / 2 * u)]; linarith
  have h1 : edgeCdfL A t ≤
      (A.law {ω | lambdaMax (symOfEntries ω) < 2 + t * p0 + u * p0}).toReal := by
    unfold edgeCdfL
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
    have hω' : (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2) ≤ t := hω
    have hm := mul_le_mul_of_nonneg_left hω' hp0.le
    have e : p0 * ((N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)) =
        lambdaMax (symOfEntries ω) - 2 := by
      rw [← mul_assoc, mul_comm p0, hpp, one_mul]
    change lambdaMax (symOfEntries ω) < 2 + t * p0 + u * p0
    have : 0 < u * p0 := mul_pos hu hp0
    nlinarith
  have h2 := hSA _ hEa
  have h3 := hAB _ hEm
  have h4 := hSB _ hEb
  have h5 : (B.law {ω | lambdaMax (symOfEntries ω) < 2 + t * p0 + u * p0 + u * p0}).toReal ≤
      edgeCdfL B (t + 2 * u) := by
    unfold edgeCdfL
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
    have hω' : lambdaMax (symOfEntries ω) < 2 + t * p0 + u * p0 + u * p0 := hω
    change (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2) ≤ t + 2 * u
    have hNp : 0 < (N : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
    have hm := mul_le_mul_of_nonneg_left
      (show lambdaMax (symOfEntries ω) - 2 ≤ (t + 2 * u) * p0 by linarith) hNp.le
    calc (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)
        ≤ (N : ℝ) ^ ((2 : ℝ) / 3) * ((t + 2 * u) * p0) := hm
      _ = (t + 2 * u) * ((N : ℝ) ^ ((2 : ℝ) / 3) * p0) := by ring
      _ = t + 2 * u := by rw [hpp, mul_one]
  rw [hq] at h2 h4
  rw [show 2 + t * p0 + u * p0 + u * p0 - u * p0 / 2 = 2 + t * p0 + u * p0 + u * p0 / 2 by ring]
    at h4
  linarith

/-- Lemma 5.6 ([26], proof of Theorem 2.4): if both laws of every pair satisfy the
event `edgeInputEvent N C` with high probability for every `C ≥ C0`, and the pairs satisfy (5.15)
with rate `N^{-κ+Cε}`, then (5.27) holds for every `s ∈ ℝ`, with `δ` and `N0` independent of `s`
and of the pair. -/
theorem edge_universality_of_inputs {Pair : ∀ N : ℕ, EntryLaws N → EntryLaws N → Prop} {κ : ℝ}
    (hκ : 0 < κ) (hprob : ∀ N (Lv Lw : EntryLaws N), Pair N Lv Lw → Lv.IsProb ∧ Lw.IsProb)
    (hv : ∃ C0 > 0, ∀ C ≥ C0,
      HighProbOn 1 (fun N L => ∃ Lw, Pair N L Lw) (fun N _ => edgeInputEvent N C))
    (hw : ∃ C0 > 0, ∀ C ≥ C0,
      HighProbOn 1 (fun N L => ∃ Lv, Pair N Lv L) (fun N _ => edgeInputEvent N C))
    (hcomp : GreenCompHyp Pair κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ Lv Lw : EntryLaws N, Pair N Lv Lw → ∀ s : ℝ,
      edgeCdfL Lw (s - (N : ℝ) ^ (-δ)) - (N : ℝ) ^ (-δ) ≤ edgeCdfL Lv s ∧
      edgeCdfL Lv s ≤ edgeCdfL Lw (s + (N : ℝ) ^ (-δ)) + (N : ℝ) ^ (-δ) := by
  obtain ⟨C0v, hC0v, hv⟩ := hv
  obtain ⟨C0w, hC0w, hw⟩ := hw
  obtain ⟨CF, -, hFd⟩ := edgeCutoff_deriv_le
  obtain ⟨ε₀, hε₀, Cg, hCg, hcmp⟩ := hcomp CF
  have hF4 : ContDiff ℝ 4 (fun x : ℝ => edgeCutoff (x / Real.pi)) :=
    (edgeCutoff_props.1 4).comp (contDiff_id.div_const _)
  set C := max C0v C0w with hCdef
  have hC : 0 < C := lt_max_of_lt_left hC0v
  have hC1 : 0 < C + 1 := by linarith
  set ε := min (1 / 20) (min (ε₀ / 18) (min (κ / (36 * Cg)) (κ / 2))) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity)
    (by positivity)))
  have hε20 : ε ≤ 1 / 20 := min_le_left _ _
  have hε18 : ε ≤ ε₀ / 18 := (min_le_right _ _).trans (min_le_left _ _)
  have hε36 : ε ≤ κ / (36 * Cg) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε2 : ε ≤ κ / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCgε : 36 * Cg * ε ≤ κ := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 36 * Cg)).mp hε36
    linarith
  refine ⟨ε / 2, by positivity, ?_⟩
  obtain ⟨N1, hN1⟩ := prob_lambdaMax_lt_sandwich hC1 ε hε (by linarith)
  obtain ⟨N2, hN2⟩ := hcmp (9 * ε) (by positivity) (by linarith)
  obtain ⟨cv, hcv, Cv, -, Nv, hNv⟩ := hv C (le_max_left _ _)
  obtain ⟨cv', hcv', Cv', -, Nv', hNv'⟩ := hv (C + 1) (by linarith [le_max_left C0v C0w])
  obtain ⟨cw, hcw, Cw, -, Nw, hNw⟩ := hw C (le_max_right _ _)
  obtain ⟨cw', hcw', Cw', -, Nw', hNw'⟩ := hw (C + 1) (by linarith [le_max_right C0v C0w])
  have hrpow : ∀ x : ℝ, 0 < x → ∀ y : ℝ, ∀ᶠ N : ℕ in atTop, y ≤ (N : ℝ) ^ x := fun x hx y =>
    ((tendsto_rpow_atTop hx).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop y
  have hphi : ∀ᶠ N : ℕ in atTop, 2 * phi N ^ (C + 1) ≤ (N : ℝ) ^ (9 * ε) := by
    filter_upwards [phi_rpow_le_rpow (C + 1) (by positivity : (0 : ℝ) < 9 * ε / 2),
      hrpow (9 * ε / 2) (by positivity) 2, eventually_ge_atTop 1] with N h1 h2 h3
    have hX : (0 : ℝ) < N := by exact_mod_cast h3
    rw [show 9 * ε = 9 * ε / 2 + 9 * ε / 2 by ring, Real.rpow_add hX]
    have hφ0 : 0 ≤ phi N ^ (C + 1) :=
      Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _
    calc 2 * phi N ^ (C + 1) ≤ (N : ℝ) ^ (9 * ε / 2) * phi N ^ (C + 1) :=
          mul_le_mul_of_nonneg_right h2 hφ0
      _ ≤ (N : ℝ) ^ (9 * ε / 2) * (N : ℝ) ^ (9 * ε / 2) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hX _).le
  obtain ⟨N3, hN3⟩ := eventually_atTop.1 ((eventually_ge_atTop N1).and
    ((eventually_ge_atTop N2).and ((eventually_ge_atTop Nv).and ((eventually_ge_atTop Nv').and
    ((eventually_ge_atTop Nw).and ((eventually_ge_atTop Nw').and ((eventually_ge_atTop 21).and
    ((tendsto_natCast_atTop_atTop.eventually_ge_atTop ((4 : ℝ) ^ (1 / ε))).and (hphi.and
    ((hrpow (κ / 4) (by positivity) 2).and
    ((inputsComparison_rate hcv Cv (ε / 2)).and ((inputsComparison_rate hcv' Cv' (ε / 2)).and
    ((inputsComparison_rate hcw Cw (ε / 2)).and
    (inputsComparison_rate hcw' Cw' (ε / 2)))))))))))))))
  refine ⟨N3, fun N hN Lv Lw hP => ?_⟩
  obtain ⟨hNN1, hNN2, hNNv, hNNv', hNNw, hNNw', hN21, hN4, hNphi, hNκ, hrv, hrv', hrw, hrw'⟩ :=
    hN3 N hN
  obtain ⟨hLv, hLw⟩ := hprob N Lv Lw hP
  have hN21r : (21 : ℝ) ≤ N := by exact_mod_cast hN21
  have hX : (0 : ℝ) < N := by linarith
  have hN3' : 3 ≤ N := by omega
  -- the scales
  set d := (N : ℝ) ^ (-(ε / 2)) with hddef
  have hd : 0 < d := Real.rpow_pos_of_pos hX _
  have hu : 0 < (N : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hX _
  have hud : 2 * (N : ℝ) ^ (-ε) ≤ d := two_mul_rpow_neg_le hε hN4
  have hd1 : d ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hp0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hX _
  have hφ3 : 3 ≤ phi N :=
    (show (3 : ℝ) ≤ Real.log N by
      rw [Real.le_log_iff_exp_le hX]
      have he := Real.exp_one_lt_d9
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      have h0 := Real.exp_pos 1
      calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by gcongr
        _ ≤ 21 := by norm_num
        _ ≤ N := hN21r).trans (log_le_phi (by omega))
  have hφC1 : 0 < phi N ^ (C + 1) := Real.rpow_pos_of_pos (by linarith) _
  have hW : phi N ^ C + 2 ≤ phi N ^ (C + 1) := phi_rpow_add_two_le hN21 hC.le
  -- the comparison rate
  have hr : (N : ℝ) ^ (-κ + Cg * (9 * ε)) ≤ d / 2 := by
    have hκ4 : (N : ℝ) ^ (-(κ / 4)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hX.le, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hNκ
    calc (N : ℝ) ^ (-κ + Cg * (9 * ε)) ≤ (N : ℝ) ^ (-(ε / 2) + -(κ / 4)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith only [hCgε, hε2, hκ,
            (show Cg * (9 * ε) = 36 * Cg * ε / 4 by ring)])
      _ = d * (N : ℝ) ^ (-(κ / 4)) := Real.rpow_add hX _ _
      _ ≤ d * (1 / 2) := mul_le_mul_of_nonneg_left hκ4 hd.le
      _ = d / 2 := by ring
  -- the bad events
  have hbad : ∀ {c' D : ℝ} {C' : ℕ} {L : EntryLaws N},
      L.law (edgeInputEvent N D)ᶜ ≤
        ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c' * phi N ^ (1 : ℝ))) →
      (N : ℝ) ^ C' * Real.exp (-c' * phi N ^ (1 : ℝ)) ≤ (N : ℝ) ^ (-(ε / 2)) / 4 →
      (L.law (edgeInputEvent N D)ᶜ).toReal ≤ d / 4 := fun h1 h2 =>
    (ENNReal.toReal_le_of_le_ofReal (by positivity) h1).trans h2
  have bv := hbad (hNv N hNNv Lv ⟨Lw, hP⟩) hrv
  have bv' := hbad (hNv' N hNNv' Lv ⟨Lw, hP⟩) hrv'
  have bw := hbad (hNw N hNNw Lw ⟨Lv, hP⟩) hrw
  have bw' := hbad (hNw' N hNNw' Lw ⟨Lv, hP⟩) hrw'
  -- the smoothed traces as the functionals of (5.15)
  have hKF : ∀ (L : EntryLaws N) (a : ℝ),
      ∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
        ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) a (edgeEL N (C + 1))) ∂L.law =
      ∫ ω, (fun x : ℝ => edgeCutoff (x / Real.pi)) (N * ∫ y in a..edgeEL N (C + 1),
        (stieltjesM (symOfEntries ω) ⟨y, (N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)⟩).im) ∂L.law := by
    intro L a
    congr 1
    funext ω
    rw [smoothCount_eq _ (Real.rpow_pos_of_pos hX _)]
    congr 1
    ring
  have hwin9 : ∀ a : ℝ, |a - 2| ≤ phi N ^ (C + 1) * (N : ℝ) ^ (-(2 : ℝ) / 3) →
      |a - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 9 * ε) := by
    intro a ha
    rw [Real.rpow_add hX]
    calc |a - 2| ≤ phi N ^ (C + 1) * (N : ℝ) ^ (-(2 : ℝ) / 3) := ha
      _ ≤ (N : ℝ) ^ (9 * ε) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right (by linarith only [hNphi, hφC1]) hp0.le
      _ = (N : ℝ) ^ (-(2 : ℝ) / 3) * (N : ℝ) ^ (9 * ε) := mul_comm _ _
  have hE2 : |edgeEL N (C + 1) - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 9 * ε) := by
    rw [Real.rpow_add hX, edgeEL, show 2 + 2 * phi N ^ (C + 1) * (N : ℝ) ^ (-(2 : ℝ) / 3) - 2 =
      2 * phi N ^ (C + 1) * (N : ℝ) ^ (-(2 : ℝ) / 3) by ring, abs_of_pos (by positivity),
      mul_comm ((N : ℝ) ^ (-(2 : ℝ) / 3))]
    exact mul_le_mul_of_nonneg_right hNphi hp0.le
  have hcmpN := fun a (ha : |a - 2| ≤ phi N ^ (C + 1) * (N : ℝ) ^ (-(2 : ℝ) / 3)) =>
    hN2 N hNN2 Lv Lw hP _ hF4 hFd a (edgeEL N (C + 1)) (hwin9 a ha) hE2
  -- the window `|s| ≤ φ^C`
  have hwin : ∀ s : ℝ, -phi N ^ C ≤ s → s ≤ phi N ^ C →
      edgeCdfL Lw (s - 2 * (N : ℝ) ^ (-ε)) - d ≤ edgeCdfL Lv s ∧
      edgeCdfL Lv s ≤ edgeCdfL Lw (s + 2 * (N : ℝ) ^ (-ε)) + d := by
    intro s hs1 hs2
    have hsabs : |s| ≤ phi N ^ C := abs_le.2 ⟨hs1, hs2⟩
    constructor
    · have ht : |s - 2 * (N : ℝ) ^ (-ε)| + 2 * (N : ℝ) ^ (-ε) ≤ phi N ^ (C + 1) := by
        have h1 := abs_sub s (2 * (N : ℝ) ^ (-ε))
        rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * (N : ℝ) ^ (-ε))] at h1
        linarith only [h1, hsabs, hW, hud, hd1]
      have h := inputsComparison_step (C := C + 1) (ε := ε)
        (r := (N : ℝ) ^ (-κ + Cg * (9 * ε))) (pA := (Lw.law (edgeInputEvent N (C + 1))ᶜ).toReal)
        (pB := (Lv.law (edgeInputEvent N (C + 1))ᶜ).toReal) hN3' hLw hLv
        (IA := fun a => ∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) a (edgeEL N (C + 1))) ∂Lw.law)
        (IB := fun a => ∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) a (edgeEL N (C + 1))) ∂Lv.law)
        (fun E hE => (hN1 N hNN1 Lw hLw E hE).2) (fun E hE => (hN1 N hNN1 Lv hLv E hE).1)
        (fun a ha => by
          have := hcmpN a ha
          simp only [hKF]
          rw [abs_sub_comm] at this
          exact (le_abs_self _).trans this) ht
      rw [show s - 2 * (N : ℝ) ^ (-ε) + 2 * (N : ℝ) ^ (-ε) = s by ring] at h
      linarith only [h, hr, bv', bw']
    · have ht : |s| + 2 * (N : ℝ) ^ (-ε) ≤ phi N ^ (C + 1) := by
        linarith only [hsabs, hW, hud, hd1]
      have h := inputsComparison_step (C := C + 1) (ε := ε)
        (r := (N : ℝ) ^ (-κ + Cg * (9 * ε))) (pA := (Lv.law (edgeInputEvent N (C + 1))ᶜ).toReal)
        (pB := (Lw.law (edgeInputEvent N (C + 1))ᶜ).toReal) hN3' hLv hLw
        (IA := fun a => ∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) a (edgeEL N (C + 1))) ∂Lv.law)
        (IB := fun a => ∫ ω, edgeCutoff (smoothCount (symOfEntries_isHermitian ω)
          ((N : ℝ) ^ (-(2 : ℝ) / 3 - 9 * ε)) a (edgeEL N (C + 1))) ∂Lw.law)
        (fun E hE => (hN1 N hNN1 Lv hLv E hE).2) (fun E hE => (hN1 N hNN1 Lw hLw E hE).1)
        (fun a ha => by
          have := hcmpN a ha
          simp only [hKF]
          exact (le_abs_self _).trans this) ht
      linarith only [h, hr, bv', bw']
  -- the tails outside the window
  have hev : ∀ ω ∈ edgeInputEvent N C,
      |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C :=
    fun ω hω => hω.2.2.1
  refine sandwich_extend_range (fun s => (edgeCdfL_mem_Icc hLv s).1)
    (fun s => (edgeCdfL_mem_Icc hLv s).2) (fun s => (edgeCdfL_mem_Icc hLw s).1)
    (fun s => (edgeCdfL_mem_Icc hLw s).2) (monotone_edgeCdfL hLw) (W := phi N ^ C)
    (a := 2 * (N : ℝ) ^ (-ε)) (b := d) (p := d) (by positivity) hud le_rfl le_rfl
    (fun s hs => (edgeCdfL_le_of_lt_neg hLv hev hs).trans (by linarith only [bv, hd]))
    (fun s hs => (edgeCdfL_le_of_lt_neg hLw hev hs).trans (by linarith only [bw, hd]))
    (fun s hs => le_trans (by linarith only [bv, hd]) (one_sub_le_edgeCdfL_of_le hLv hev hs))
    (fun s hs => le_trans (by linarith only [bw, hd]) (one_sub_le_edgeCdfL_of_le hLw hev hs)) hwin

/-! ## Checks -/

/-- (5.15) for the pair predicate "both laws are the GOE entry laws": both expectations coincide,
so the hypothesis holds with every rate `κ`; both laws are probability laws. -/
example : (∀ κ : ℝ, GreenCompHyp (fun N Lv Lw => Lv = goeLaws N ∧ Lw = goeLaws N) κ) ∧
    ∀ N (Lv Lw : EntryLaws N), (Lv = goeLaws N ∧ Lw = goeLaws N) → Lv.IsProb ∧ Lw.IsProb := by
  refine ⟨fun κ CF => ⟨1, one_pos, 1, one_pos, fun ε _ _ =>
    ⟨1, fun N _ Lv Lw hP F _ _ E₁ E₂ _ _ => ?_⟩⟩, ?_⟩
  · obtain ⟨rfl, rfl⟩ := hP
    rw [sub_self, abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  · rintro N Lv Lw ⟨rfl, rfl⟩
    have h : (goeLaws N).IsProb :=
      ⟨fun _ => by unfold goeLaws ofIID; infer_instance,
        fun _ => by unfold goeLaws ofIID; infer_instance⟩
    exact ⟨h, h⟩

#print axioms edge_universality_of_inputs

end WEdgeNS
