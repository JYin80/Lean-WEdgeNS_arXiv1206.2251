import WEdgeNS.Reduction.TruncClass
import WEdgeNS.Reduction.ResolventShift
import WEdgeNS.Comparison.RigiditySmallQ
import WEdgeNS.LocalLaw.Deloc

/-!
# The good event of the small matrix
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- The good event of `H̃^S` used by (4.38)–(4.47): (4.38) at `z̃`, delocalization,
rigidity for every `j`, the edge inputs, and `|λ_α| ≤ 3`. -/
def smallGood (N : ℕ) (C ε : ℝ) : Set (Entries N) :=
  {ω | (∀ i, ‖resolventC (symOfEntries ω) (edgePt N) i i + 1‖ ≤ (N : ℝ) ^ (-ε / 2)) ∧
    ω ∈ delocEvent N C ∧
    (∀ j : Fin N, |eigAsc (symOfEntries_isHermitian ω) j - gammaLoc N ((j : ℕ) + 1)| ≤
      phi N ^ C * (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) *
        (N : ℝ) ^ (-(2 : ℝ) / 3)) ∧
    |(N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (symOfEntries ω) - 2)| ≤ phi N ^ C ∧
    ((Finset.univ.filter fun α => |(symOfEntries_isHermitian ω).eigenvalues α - 2| ≤
        2 * phi N ^ C * (N : ℝ) ^ (-(2 : ℝ) / 3)).card : ℝ) ≤ phi N ^ (2 * C) ∧
    ∀ α, |(symOfEntries_isHermitian ω).eigenvalues α| ≤ 3}

/-! ### Elementary facts -/

/-- `1 ≤ φ` for `N ≥ 3`. -/
private lemma sg_one_le_phi {N : ℕ} (hN : 3 ≤ N) : 1 ≤ phi N := by
  rw [phi_eq_exp hN]
  exact Real.one_le_exp (sq_nonneg _)

/-- A positive power of `N` is eventually at least any given constant. -/
private lemma sg_eventually_rpow_ge (X : ℝ) {y : ℝ} (hy : 0 < y) :
    ∀ᶠ N : ℕ in atTop, X ≤ (N : ℝ) ^ y :=
  ((tendsto_rpow_atTop hy).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop X

/-- The event (3.5) becomes weaker as its exponent grows. -/
private lemma sg_delocEvent_mono {N : ℕ} (hN : 3 ≤ N) {C C' : ℝ} (h : C ≤ C') :
    delocEvent N C ⊆ delocEvent N C' := by
  intro ω hω v μ hv hn i
  refine (hω v μ hv hn i).trans ?_
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (sg_one_le_phi hN) h) (Nat.cast_nonneg N)

/-! ### The semicircle law at `z̃` -/

/-- The self-consistent equation `m (z + m) = -1` in the upper half plane. -/
private lemma sg_msc_mul {z : ℂ} (hz : 0 < z.im) : msc z * (z + msc z) = -1 := by
  have h := msc_add_inv_eq_zero hz
  by_cases h0 : z + msc z = 0
  · rw [h0, _root_.inv_zero, add_zero] at h
    rw [h, add_zero] at h0
    rw [h0] at hz
    simp at hz
  · linear_combination (z + msc z) * h - mul_inv_cancel₀ h0

/-- At `z̃ = 2 + i N^{-2/3}`, `|m_sc(z̃) + 1| ≤ K N^{-1/3}` when `|m_sc(z̃)| ≤ K` and `K ≥ 1`. -/
private lemma sg_msc_edge {N : ℕ} (hN : 1 ≤ N) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ‖msc (edgePt N)‖ ≤ K) :
    ‖msc (edgePt N) + 1‖ ≤ K * (N : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3) with hη
  set u : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3) with hu
  have hη0 : 0 < η := Real.rpow_pos_of_pos hNpos _
  have hu0 : 0 < u := Real.rpow_pos_of_pos hNpos _
  have huu : u * u = η := by
    rw [hu, hη, ← Real.rpow_add hNpos]; norm_num
  have hzim : 0 < (edgePt N).im := hη0
  have hm := sg_msc_mul hzim
  set m : ℂ := msc (edgePt N) with hmdef
  have hz : edgePt N = 2 + (η : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [edgePt, hη]
  have hsq : (m + 1) ^ 2 = -((η : ℂ) * Complex.I) * m := by
    have : (m + 1) ^ 2 = (2 - edgePt N) * m := by
      linear_combination hm
    rw [this, hz]; ring
  have hnorm : ‖m + 1‖ ^ 2 ≤ η * K := by
    rw [← norm_pow, hsq, norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, abs_of_pos hη0]
    exact mul_le_mul_of_nonneg_left hK hη0.le
  have hKu : 0 ≤ K * u := by positivity
  have h2 : ‖m + 1‖ ^ 2 ≤ (K * u) ^ 2 := by
    refine hnorm.trans ?_
    have : (K * u) ^ 2 = K * K * η := by rw [← huu]; ring
    have h3 : 0 ≤ η * K * (K - 1) := mul_nonneg (by positivity) (by linarith)
    rw [this]
    nlinarith
  exact le_of_sq_le_sq h2 hKu

/-! ### The diagonal resolvent at `z̃` -/

/-- (4.38): on the local-law event (3.3) with `q = N^{φs}`, `|G_ii(z̃) + 1| ≤ N^{-ε/2}` for every
`i`, for all large `N`, when `ε < 1/2` and `ε/2 < φs`. -/
private lemma sg_resolvent_edge {CL φs ε K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ z : ℂ, |z.re| ≤ 5 → 0 < z.im → z.im ≤ 10 → ‖msc z‖ ≤ K)
    (hε : ε < 1 / 2) (hφs : ε / 2 < φs) :
    ∃ N1 : ℕ, ∀ N ≥ N1, ∀ ω : Entries N, ω ∈ localLawEvent N CL ((N : ℝ) ^ φs) →
      ∀ i, ‖resolventC (symOfEntries ω) (edgePt N) i i + 1‖ ≤ (N : ℝ) ^ (-ε / 2) := by
  set δ : ℝ := (φs - ε / 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((eventually_ge_atTop 3).and <| (phi_rpow_le_rpow CL (c := 1 / 24) (by norm_num)).and <|
      (phi_rpow_le_rpow CL hδ0).and <| (sg_eventually_rpow_ge 2 hδ0).and <|
      (sg_eventually_rpow_ge (2 * (2 * K + 1)) (y := 1 / 24) (by norm_num)))
  refine ⟨N1, fun N hN ω hω i => ?_⟩
  obtain ⟨h3, hφ24, hφδ, hNδ, hx⟩ := hN1 N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hφ1 : 1 ≤ phi N := sg_one_le_phi h3
  set η : ℝ := (N : ℝ) ^ (-(2 : ℝ) / 3) with hη
  set u : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 3) with hu
  set x : ℝ := (N : ℝ) ^ ((1 : ℝ) / 24) with hxdef
  set t : ℝ := (N : ℝ) ^ (-ε / 2) with htdef
  set P : ℝ := phi N ^ CL with hP
  set a : ℝ := (N : ℝ) ^ (-φs) with hadef
  have hη0 : 0 < η := Real.rpow_pos_of_pos hNpos _
  have hu0 : 0 < u := Real.rpow_pos_of_pos hNpos _
  have ha0 : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  have hNη : (N : ℝ) * η = (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [hη, show (N : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) + (-(2 : ℝ) / 3)) by
      rw [Real.rpow_add hNpos, Real.rpow_one]]
    norm_num
  have hNηu : (N : ℝ) * η * u = 1 := by
    rw [hNη, hu, ← Real.rpow_add hNpos]; norm_num
  have hinv : 1 / ((N : ℝ) * η) = u := by
    rw [one_div]; exact inv_eq_of_mul_eq_one_right hNηu
  -- the exponent identities
  have hxu : x * x * u = (N : ℝ) ^ (-(1 : ℝ) / 4) := by
    rw [hxdef, hu, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; norm_num
  have haδ : (N : ℝ) ^ δ * a * (N : ℝ) ^ δ = t := by
    rw [hadef, htdef, mul_comm ((N : ℝ) ^ δ), mul_assoc, ← Real.rpow_add hNpos,
      ← Real.rpow_add hNpos]
    congr 1
    rw [hδ]; ring
  have ht4 : (N : ℝ) ^ (-(1 : ℝ) / 4) ≤ t := by
    rw [htdef]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  -- the specialisation of (3.3) at `z̃`
  have hz : edgePt N ∈ specDomain N CL := by
    refine ⟨by norm_num [edgePt], ?_, ?_⟩
    · change phi N ^ CL / N < η
      rw [div_lt_iff₀ hNpos, mul_comm, hNη]
      exact lt_of_le_of_lt hφ24
        (Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num))
    · change η ≤ 10
      have : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1' (by norm_num)
      linarith
  have hzim : (edgePt N).im = η := rfl
  have hent := (hω _ hz).2 i i
  simp only [↓reduceIte] at hent
  unfold entryErr at hent
  rw [hzim, hinv, one_div, ← Real.rpow_neg hNpos.le] at hent
  have hzim0 : 0 < (edgePt N).im := hη0
  have hmK : ‖msc (edgePt N)‖ ≤ K := hK _ hz.1 hzim0 hz.2.2
  have hm : ‖msc (edgePt N) + 1‖ ≤ K * u := sg_msc_edge (by omega) hK1 hmK
  have him : (msc (edgePt N)).im ≤ K * u := by
    have h1 : (msc (edgePt N)).im = (msc (edgePt N) + 1).im := by simp
    rw [h1]
    exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm)
  have hdiv : (msc (edgePt N)).im / ((N : ℝ) * η) = (msc (edgePt N)).im * u := by
    rw [div_eq_mul_one_div, hinv]
  have hsqrt : √((msc (edgePt N)).im / ((N : ℝ) * η)) ≤ K * u := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [hdiv]
    have h1 : (msc (edgePt N)).im * u ≤ K * u * u := mul_le_mul_of_nonneg_right him hu0.le
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ K) (sq_nonneg u))
      (by linarith : (0 : ℝ) ≤ K - 1)]
  have hsplit : ‖resolventC (symOfEntries ω) (edgePt N) i i + 1‖ ≤
      ‖resolventC (symOfEntries ω) (edgePt N) i i - msc (edgePt N)‖ +
        ‖msc (edgePt N) + 1‖ := by
    calc ‖resolventC (symOfEntries ω) (edgePt N) i i + 1‖
        = ‖(resolventC (symOfEntries ω) (edgePt N) i i - msc (edgePt N)) +
            (msc (edgePt N) + 1)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  -- the first term of (3.3) against `N^{-ε/2}`
  have h1 : P * a ≤ t / 2 := by
    have hNδ0 : 0 ≤ (N : ℝ) ^ δ := by linarith
    have e1 : P * a * 2 ≤ P * a * (N : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_left hNδ (mul_nonneg hP0 ha0.le)
    have e2 : P * a * (N : ℝ) ^ δ ≤ (N : ℝ) ^ δ * a * (N : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hφδ ha0.le) hNδ0
    linarith
  -- the remaining terms against `N^{-ε/2}`
  have h2 : (P * (K + 1) + K) * u ≤ t / 2 := by
    have hx6 : 1 ≤ x := by linarith
    have hA : P * (K + 1) + K ≤ x * (2 * K + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hφ24) (by linarith : (0 : ℝ) ≤ K + 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ K) (by linarith : (0 : ℝ) ≤ x - 1)]
    have hxu0 : 0 ≤ x * u := by positivity
    have e1 : (P * (K + 1) + K) * u ≤ x * (2 * K + 1) * u :=
      mul_le_mul_of_nonneg_right hA hu0.le
    have e2 : 2 * (2 * K + 1) * (x * u) ≤ x * (x * u) :=
      mul_le_mul_of_nonneg_right hx hxu0
    have e3 : x * x * u ≤ t := by rw [hxu]; exact ht4
    linarith
  calc ‖resolventC (symOfEntries ω) (edgePt N) i i + 1‖
      ≤ P * ((N : ℝ) ^ (-φs) + √((msc (edgePt N)).im / ((N : ℝ) * η)) + u) + K * u :=
        hsplit.trans (add_le_add hent hm)
    _ ≤ P * (a + K * u + u) + K * u := by gcongr
    _ = P * a + (P * (K + 1) + K) * u := by ring
    _ ≤ t := by linarith

/-- The good event of `H̃^S` holds with high probability on the class of Theorem 3.6, for
`0 < ε < 1/2` and `ε/2 < φs`. -/
theorem highProb_smallGood {C1 φs ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) (hφs : ε / 2 < φs) :
    ∃ C > (0 : ℝ), HighProbOn 1 (SmallQClass C1 φs) (fun N _ => smallGood N C ε) := by
  have hφ0 : 0 < φs := by linarith
  obtain ⟨CL, hCL, hL⟩ := localLaw (ζ := 1) (C0 := max C1 1) (c := 1) one_pos
    (le_max_of_le_right zero_le_one) one_pos
  obtain ⟨Cd, hCd, hD⟩ := delocalization (ζ := 1) (C0 := max C1 1) (c := 1) one_pos
    (le_max_of_le_right zero_le_one) one_pos
  obtain ⟨Cr, hCr, hR⟩ := rigidity_smallQ (C1 := C1) hφ0
  obtain ⟨C0, hC0, hE⟩ := edge_inputs_smallQ (C1 := C1) hφ0
  obtain ⟨Ca, hCa, hA⟩ := abs_eigenvalues_le_smallQ (C1 := C1) hφ0
  obtain ⟨K, hK1, hK⟩ := msc_bounds
  obtain ⟨Nr, hNr⟩ := sg_resolvent_edge (CL := CL) hK1 (fun z h1 h2 h3 => (hK z h1 h2 h3).1.2) hε
    hφs
  have hL' : HighProbOn 1 (SmallQClass C1 φs)
      (fun N _ => localLawEvent N CL ((N : ℝ) ^ φs)) := by
    refine hL.mono_eventually (fun N L h => h.isGenWigner) ?_
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 (phi_rpow_le_rpow CL hφ0)
    exact ⟨N1, fun N hN L hcl ω hω => hω _ (hcl.supportParam (hN1 N hN) 1)⟩
  have hD' : HighProbOn 1 (SmallQClass C1 φs) (fun N _ => delocEvent N Cd) := by
    refine hD.mono_eventually (fun N L h => h.isGenWigner) ?_
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 (phi_rpow_le_rpow Cd hφ0)
    exact ⟨N1, fun N hN L hcl ω hω => hω ⟨_, hcl.supportParam (hN1 N hN) 1⟩⟩
  have hCd_le : Cd ≤ max (max Cd Cr) C0 := (le_max_left _ _).trans (le_max_left _ _)
  have hCr_le : Cr ≤ max (max Cd Cr) C0 := (le_max_right _ _).trans (le_max_left _ _)
  have hC0_le : C0 ≤ max (max Cd Cr) C0 := le_max_right _ _
  refine ⟨max (max Cd Cr) C0, lt_of_lt_of_le hCd hCd_le, ?_⟩
  obtain ⟨Na, hNa⟩ := eventually_atTop.1 (phi_rpow_le_rpow Ca (c := 2 / 3) (by norm_num))
  refine (hL'.inter (hD'.inter (hR.inter ((hE _ hC0_le).inter hA)))).mono_eventually
    (fun _ _ h => h) ⟨max (max Nr Na) 3, fun N hN L _ ω hω => ?_⟩
  obtain ⟨hω1, hω2, ⟨hω3, -⟩, hω4, hω5⟩ := hω
  have hNr' : Nr ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNa' : Na ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hφ1 : 1 ≤ phi N := sg_one_le_phi hN3
  simp only [smallGood, Set.mem_ofPred_eq]
  refine ⟨hNr N hNr' ω hω1, sg_delocEvent_mono hN3 hCd_le hω2, fun j => ?_, hω4.1, hω4.2,
    fun α => ?_⟩
  · refine (hω3 j).trans ?_
    have hmin : 0 ≤ (min (((j : ℕ) : ℝ) + 1) ((N : ℝ) - (j : ℕ))) ^ (-(1 : ℝ) / 3) := by
      apply Real.rpow_nonneg
      have : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
      exact le_min (by positivity) (by linarith)
    have hn : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hNpos.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hφ1 hCr_le) hmin) hn
  · have h1 : phi N ^ Ca * (N : ℝ) ^ (-(2 : ℝ) / 3) ≤ 1 := by
      calc phi N ^ Ca * (N : ℝ) ^ (-(2 : ℝ) / 3)
          ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right (hNa N hNa') (Real.rpow_nonneg hNpos.le _)
        _ = 1 := by rw [← Real.rpow_add hNpos]; norm_num
    linarith [hω5 α]

/-! ### Compiled checks

The hypotheses hold at `ε = 1/100` and `φs = 3ε/4 = 3/400` (so `ε/2 = 1/200 < 3/400`), for the
laws `truncLawsNorm ν ν' ε N` with `ν` Rademacher and `ν' = N(0, 2)`, which lie in the class of
Theorem 3.6 for all large `N`. -/

/-- The conclusion for these laws: the class membership holds from some `N0` on, and the
probability of the complement of `smallGood` is bounded by a sequence tending to `0`. -/
example : ∃ C > (0 : ℝ), ∃ C1 : ℝ, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∃ N0 : ℕ, ∀ N ≥ N0,
    SmallQClass C1 (3 * (1 / 100) / 4) N
      (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) N) ∧
    (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) N).law
      (smallGood N C (1 / 100))ᶜ ≤ ENNReal.ofReal (e N) := by
  obtain ⟨C1, N0, hcl⟩ := truncLawsNorm_smallQClass rademacher_wignerLaws rademacher_tailCond
    (ε := 1 / 100) (by norm_num) (by norm_num)
  obtain ⟨C, hC, h⟩ := highProb_smallGood (C1 := C1) (φs := 3 * (1 / 100) / 4) (ε := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨e, he, hev⟩ := h.tendstoOneOn one_pos
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  exact ⟨C, hC, C1, e, he, max N0 N1, fun N hN =>
    ⟨hcl N ((le_max_left _ _).trans hN), hN1 N ((le_max_right _ _).trans hN) _
      (hcl N ((le_max_left _ _).trans hN))⟩⟩

/-- The bound `N^{C'} exp(-c φ)` of `HighProbOn` at one point `N ≥ 1000`, for the same laws. -/
example : ∃ C > (0 : ℝ), ∃ C1 : ℝ, ∃ c > (0 : ℝ), ∃ C' : ℕ, ∃ N : ℕ, 1000 ≤ N ∧
    SmallQClass C1 (3 * (1 / 100) / 4) N
      (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) N) ∧
    (truncLawsNorm rademacher (gaussianReal 0 2) (1 / 100) N).law
      (smallGood N C (1 / 100))ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ C' * Real.exp (-c * phi N ^ (1 : ℝ))) := by
  obtain ⟨C1, N0, hcl⟩ := truncLawsNorm_smallQClass rademacher_wignerLaws rademacher_tailCond
    (ε := 1 / 100) (by norm_num) (by norm_num)
  obtain ⟨C, hC, c, hc, C', -, N1, h⟩ := highProb_smallGood (C1 := C1)
    (φs := 3 * (1 / 100) / 4) (ε := 1 / 100) (by norm_num) (by norm_num) (by norm_num)
  have hN0 : N0 ≤ max (max N0 N1) 1000 := (le_max_left _ _).trans (le_max_left _ _)
  have hN1 : N1 ≤ max (max N0 N1) 1000 := (le_max_right _ _).trans (le_max_left _ _)
  exact ⟨C, hC, C1, c, hc, C', max (max N0 N1) 1000, le_max_right _ _, hcl _ hN0,
    h _ hN1 _ (hcl _ hN0)⟩

#print axioms smallGood
#print axioms highProb_smallGood

end WEdgeNS
