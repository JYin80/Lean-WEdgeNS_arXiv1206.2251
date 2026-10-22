import WEdgeNS.Model.General

/-!
# φ and ζ-high probability uniformly over classes of entry laws (Definition 2.3)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- `φ = (log N)^{log log N}` of (2.2). -/
def phi (N : ℕ) : ℝ := Real.log N ^ Real.log (Real.log N)

private lemma log_nat_pos {N : ℕ} (hN : 3 ≤ N) : 0 < Real.log N := by
  apply Real.log_pos
  have : (3 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

theorem phi_eq_exp {N : ℕ} (hN : 3 ≤ N) : phi N = Real.exp (Real.log (Real.log N) ^ 2) := by
  unfold phi
  rw [Real.rpow_def_of_pos (log_nat_pos hN)]
  congr 1
  ring

private lemma one_le_phi {N : ℕ} (hN : 3 ≤ N) : 1 ≤ phi N := by
  rw [phi_eq_exp hN]
  exact Real.one_le_exp (sq_nonneg _)

theorem log_le_phi {N : ℕ} (hN : 16 ≤ N) : Real.log N ≤ phi N := by
  have hN3 : 3 ≤ N := by omega
  have hpos := log_nat_pos hN3
  have h16 : Real.log 16 ≤ Real.log N := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hN
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have he := Real.exp_one_lt_d9
  have hge : Real.exp 1 ≤ Real.log N := by linarith
  have hu : 1 ≤ Real.log (Real.log N) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hge
  rw [phi_eq_exp hN3]
  conv_lhs => rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  nlinarith

private lemma tendsto_loglog :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma tendsto_lognat : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem phi_rpow_le_rpow (C : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, phi N ^ C ≤ (N : ℝ) ^ c := by
  filter_upwards [eventually_ge_atTop 3, tendsto_loglog.eventually_ge_atTop (6 * |C| / c),
    tendsto_loglog.eventually_ge_atTop 0] with N hN hu hu0
  have hpos := log_nat_pos hN
  have hNpos : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set u := Real.log (Real.log N) with hu_def
  rw [phi_eq_exp hN, ← Real.exp_mul, Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.mpr
  have hexp : Real.log N = Real.exp u := (Real.exp_log hpos).symm
  have h3 : u ^ 3 / 6 ≤ Real.exp u := by
    have := Real.pow_div_factorial_le_exp u hu0 3
    simpa [Nat.factorial] using this
  have h6 : 6 * |C| ≤ c * u := by
    have := (div_le_iff₀ hc).mp hu
    linarith
  have hC : C ≤ |C| := le_abs_self C
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  calc u ^ 2 * C ≤ u ^ 2 * |C| := by gcongr
    _ ≤ u ^ 2 * (c * u / 6) := by gcongr; linarith
    _ = c * (u ^ 3 / 6) := by ring
    _ ≤ c * Real.exp u := by gcongr
    _ = Real.log N * c := by rw [← hexp]; ring

/-- Definition 2.3 uniformly over a class of entry laws: the events `Ω N L` hold with
`ζ`-high probability, with `c`, `C`, `N0` independent of `N` and of the laws in the class. -/
def HighProbOn (ζ : ℝ) (Cls : ∀ N : ℕ, EntryLaws N → Prop)
    (Ω : ∀ N : ℕ, EntryLaws N → Set (Entries N)) : Prop :=
  ∃ c > 0, ∃ C > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ L : EntryLaws N, Cls N L →
    L.law (Ω N L)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ C * Real.exp (-c * phi N ^ ζ))

private lemma natCast_ge_one {N : ℕ} (hN : 1 ≤ N) : (1 : ℝ) ≤ N := by exact_mod_cast hN

private lemma phi_rpow_nonneg (N : ℕ) (ζ : ℝ) : 0 ≤ phi N ^ ζ := by
  unfold phi
  exact Real.rpow_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _) _

theorem HighProbOn.inter {ζ : ℝ} {Cls : ∀ N : ℕ, EntryLaws N → Prop}
    {Ω₁ Ω₂ : ∀ N : ℕ, EntryLaws N → Set (Entries N)} (h₁ : HighProbOn ζ Cls Ω₁)
    (h₂ : HighProbOn ζ Cls Ω₂) : HighProbOn ζ Cls (fun N L => Ω₁ N L ∩ Ω₂ N L) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, N₁, h₁⟩ := h₁
  obtain ⟨c₂, hc₂, C₂, hC₂, N₂, h₂⟩ := h₂
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max C₁ C₂ + 1, by positivity,
    max N₁ (max N₂ 2), fun N hN L hL => ?_⟩
  have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂ : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : (1 : ℝ) ≤ N := natCast_ge_one (by omega)
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  rw [Set.compl_inter]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (h₁ N hN₁ L hL) (h₂ N hN₂ L hL)).trans ?_
  have hφ := phi_rpow_nonneg N ζ
  set E := Real.exp (-min c₁ c₂ * phi N ^ ζ) with hE
  have hEpos : 0 ≤ E := (Real.exp_pos _).le
  have hb₁ : (N : ℝ) ^ C₁ * Real.exp (-c₁ * phi N ^ ζ) ≤ (N : ℝ) ^ (max C₁ C₂) * E := by
    apply mul_le_mul (pow_le_pow_right₀ hN1 (le_max_left _ _))
      _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    have := min_le_left c₁ c₂
    nlinarith
  have hb₂ : (N : ℝ) ^ C₂ * Real.exp (-c₂ * phi N ^ ζ) ≤ (N : ℝ) ^ (max C₁ C₂) * E := by
    apply mul_le_mul (pow_le_pow_right₀ hN1 (le_max_right _ _))
      _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    have := min_le_right c₁ c₂
    nlinarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hpow : (N : ℝ) ^ (max C₁ C₂ + 1) = (N : ℝ) ^ (max C₁ C₂) * N := by
    rw [pow_succ]
  rw [hpow]
  have hm : 0 ≤ (N : ℝ) ^ (max C₁ C₂) * E := by positivity
  nlinarith

theorem HighProbOn.mono {ζ : ℝ} {Cls : ∀ N : ℕ, EntryLaws N → Prop}
    {Ω₁ Ω₂ : ∀ N : ℕ, EntryLaws N → Set (Entries N)} (h : HighProbOn ζ Cls Ω₁)
    (hsub : ∀ N L, Ω₁ N L ⊆ Ω₂ N L) : HighProbOn ζ Cls Ω₂ := by
  obtain ⟨c, hc, C, hC, N0, h⟩ := h
  exact ⟨c, hc, C, hC, N0, fun N hN L hL =>
    (measure_mono (Set.compl_subset_compl.mpr (hsub N L))).trans (h N hN L hL)⟩

theorem HighProbOn.of_le_zeta {ζ ζ' : ℝ} (h0 : 0 ≤ ζ') (hζ : ζ' ≤ ζ)
    {Cls : ∀ N : ℕ, EntryLaws N → Prop} {Ω : ∀ N : ℕ, EntryLaws N → Set (Entries N)}
    (h : HighProbOn ζ Cls Ω) : HighProbOn ζ' Cls Ω := by
  obtain ⟨c, hc, C, hC, N0, h⟩ := h
  refine ⟨c, hc, C, hC, max N0 3, fun N hN L hL => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  refine (h N hN0 L hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hNpos : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  have hφ : phi N ^ ζ' ≤ phi N ^ ζ := Real.rpow_le_rpow_of_exponent_le (one_le_phi hN3) hζ
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A union bound over at most `N^K` events indexed by `ι N`. -/
theorem HighProbOn.iInter {ζ K : ℝ} {Cls : ∀ N : ℕ, EntryLaws N → Prop} {ι : ℕ → Type}
    [∀ N, Fintype (ι N)] (hcard : ∀ N, (Fintype.card (ι N) : ℝ) ≤ (N : ℝ) ^ K)
    {Ω : ∀ N : ℕ, ι N → EntryLaws N → Set (Entries N)}
    (h : ∃ c > 0, ∃ C > 0, ∃ N0 : ℕ, ∀ N ≥ N0, ∀ k : ι N, ∀ L : EntryLaws N, Cls N L →
      L.law (Ω N k L)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ C * Real.exp (-c * phi N ^ ζ))) :
    HighProbOn ζ Cls (fun N L => ⋂ k, Ω N k L) := by
  obtain ⟨c, hc, C, hC, N0, h⟩ := h
  refine ⟨c, hc, ⌈K⌉₊ + C, by omega, max N0 1, fun N hN L hL => ?_⟩
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN1' : (1 : ℝ) ≤ N := natCast_ge_one hN1
  have hNpos : (0 : ℝ) < N := by linarith
  rw [Set.compl_iInter]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  set x : ℝ := (N : ℝ) ^ C * Real.exp (-c * phi N ^ ζ) with hx
  have hx0 : 0 ≤ x := by positivity
  calc ∑ k, L.law (Ω N k L)ᶜ ≤ ∑ _k : ι N, ENNReal.ofReal x :=
        Finset.sum_le_sum fun k _ => h N hN0 k L hL
    _ = ENNReal.ofReal ((Fintype.card (ι N) : ℝ) * x) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card (ι N))), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hK : (N : ℝ) ^ K ≤ (N : ℝ) ^ ⌈K⌉₊ := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hN1' (Nat.le_ceil K)
        have hpow : (N : ℝ) ^ (⌈K⌉₊ + C) = (N : ℝ) ^ ⌈K⌉₊ * (N : ℝ) ^ C := pow_add _ _ _
        have hE : 0 ≤ Real.exp (-c * phi N ^ ζ) := (Real.exp_pos _).le
        have hNC : 0 ≤ (N : ℝ) ^ C := by positivity
        calc (Fintype.card (ι N) : ℝ) * x ≤ (N : ℝ) ^ ⌈K⌉₊ * x :=
              mul_le_mul_of_nonneg_right ((hcard N).trans hK) hx0
          _ = (N : ℝ) ^ (⌈K⌉₊ + C) * Real.exp (-c * phi N ^ ζ) := by
              rw [hpow, hx]; ring

/-- "With probability `1 - o(1)`" uniformly over a class: one `ε_N → 0` for all laws. -/
def TendstoOneOn (Cls : ∀ N : ℕ, EntryLaws N → Prop)
    (Ω : ∀ N : ℕ, EntryLaws N → Set (Entries N)) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ N in atTop, ∀ L : EntryLaws N, Cls N L → L.law (Ω N L)ᶜ ≤ ENNReal.ofReal (ε N)

theorem HighProbOn.tendstoOneOn {ζ : ℝ} (hζ : 0 < ζ) {Cls : ∀ N : ℕ, EntryLaws N → Prop}
    {Ω : ∀ N : ℕ, EntryLaws N → Set (Entries N)} (h : HighProbOn ζ Cls Ω) :
    TendstoOneOn Cls Ω := by
  obtain ⟨c, hc, C, hC, N0, h⟩ := h
  refine ⟨fun N => (N : ℝ) ^ C * Real.exp (-c * phi N ^ ζ), ?_,
    (eventually_ge_atTop N0).mono fun N hN L hL => h N hN L hL⟩
  have hev : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ C * Real.exp (-c * phi N ^ ζ) ≤ Real.exp (-((C : ℝ) * Real.log N)) := by
    filter_upwards [eventually_ge_atTop 3, tendsto_loglog.eventually_ge_atTop (2 / ζ),
      tendsto_lognat.eventually_ge_atTop (2 * (C : ℝ) / c)] with N hN hu hl
    have hpos := log_nat_pos hN
    have hNpos : (0 : ℝ) < N := by
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    set u := Real.log (Real.log N) with hu_def
    have hexp : Real.log N = Real.exp u := (Real.exp_log hpos).symm
    have hu2 : 2 ≤ ζ * u := by
      have := (div_le_iff₀ hζ).mp hu
      linarith
    have hu0 : 0 ≤ u := by
      by_contra hneg
      rw [not_le] at hneg
      nlinarith
    have hφ : phi N ^ ζ = Real.exp (ζ * u ^ 2) := by
      rw [phi_eq_exp hN, ← Real.exp_mul]; congr 1; ring
    have h2u : 2 * u ≤ ζ * u ^ 2 := by nlinarith
    have hbig : Real.log N ^ 2 ≤ phi N ^ ζ := by
      rw [hφ, hexp, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    have hc2 : 2 * C ≤ c * Real.log N := (div_le_iff₀ hc).mp hl |> fun h => by linarith
    have hC2 : 2 * C * Real.log N ≤ c * phi N ^ ζ := by
      nlinarith
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hNpos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlim : Tendsto (fun N : ℕ => Real.exp (-((C : ℝ) * Real.log N))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_lognat.const_mul_atTop (by exact_mod_cast hC))
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) hev hlim

/-! ### Compiled witnesses

Entry laws for which every entry is `δ₀`; the class contains exactly this family. -/

/-- Every diagonal and upper entry law is the point mass at `0`. -/
def diracLaws (N : ℕ) : EntryLaws N :=
  ⟨fun _ => Measure.dirac 0, fun _ => Measure.dirac 0⟩

/-- The class consisting of the single entry-law family `diracLaws`. -/
def diracCls (N : ℕ) (L : EntryLaws N) : Prop := L = diracLaws N

/-- The point-mass entry laws are probability measures. -/
lemma diracLaws_isProb (N : ℕ) : (diracLaws N).IsProb :=
  ⟨fun _ => Measure.dirac.isProbabilityMeasure, fun _ => Measure.dirac.isProbabilityMeasure⟩

/-- Each diagonal entry law of `diracLaws N` is a probability measure. -/
instance diracLaws_diag_prob (N : ℕ) (i : Fin N) :
    IsProbabilityMeasure ((diracLaws N).diag i) :=
  (diracLaws_isProb N).diag i

/-- Each upper entry law of `diracLaws N` is a probability measure. -/
instance diracLaws_off_prob (N : ℕ) (p : OffDiag N) :
    IsProbabilityMeasure ((diracLaws N).off p) :=
  (diracLaws_isProb N).off p

/-- Under the point-mass laws, the event that the diagonal entry `k` is nonzero is null. -/
lemma law_diag_ne (N : ℕ) (k : Fin N) :
    (diracLaws N).law {ω | ω.1 k ≠ 0} = 0 := by
  have hset : {ω : Entries N | ω.1 k ≠ 0} =
      (Set.pi Set.univ (fun j : Fin N => if j = k then ({0}ᶜ : Set ℝ) else Set.univ)) ×ˢ
        (Set.univ : Set (OffDiag N → ℝ)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies,
      and_true]
    constructor
    · intro h j
      by_cases hj : j = k
      · subst hj; simpa using h
      · simp [hj]
    · intro h
      simpa using h k
  unfold EntryLaws.law
  rw [hset, Measure.prod_prod, Measure.pi_pi]
  apply mul_eq_zero_of_left
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [diracLaws])

/-- Under the point-mass laws, the event that the upper entry `p` is nonzero is null. -/
lemma law_off_ne (N : ℕ) (p : OffDiag N) :
    (diracLaws N).law {ω | ω.2 p ≠ 0} = 0 := by
  have hset : {ω : Entries N | ω.2 p ≠ 0} =
      (Set.univ : Set (Fin N → ℝ)) ×ˢ
        (Set.pi Set.univ (fun j : OffDiag N => if j = p then ({0}ᶜ : Set ℝ) else Set.univ)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies,
      true_and]
    constructor
    · intro h j
      by_cases hj : j = p
      · subst hj; simpa using h
      · simp [hj]
    · intro h
      simpa using h p
  unfold EntryLaws.law
  rw [hset, Measure.prod_prod, Measure.pi_pi]
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [diracLaws])

/-- Under the point-mass family, all diagonal entries vanish with ζ-high probability, for every
`ζ`. -/
lemma diag_highProb (ζ : ℝ) :
    HighProbOn ζ diracCls (fun N _ => ⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}) := by
  refine HighProbOn.iInter (K := 1) (ι := fun N => Fin N) (Ω := fun N k _ => {ω | ω.1 k = 0})
    (fun N => by simp) ⟨1, one_pos, 1, one_pos, 0, fun N _ k L hL => ?_⟩
  subst hL
  have := law_diag_ne N k
  rw [Set.compl_ofPred]
  simp only [diracLaws] at this ⊢
  rw [show {a : Entries N | ¬a.1 k = 0} = {ω | ω.1 k ≠ 0} from rfl, this]
  exact zero_le

/-- Under the point-mass family, all upper entries vanish with ζ-high probability, for every
`ζ`. -/
lemma off_highProb (ζ : ℝ) :
    HighProbOn ζ diracCls (fun N _ => ⋂ p : OffDiag N, {ω : Entries N | ω.2 p = 0}) := by
  refine HighProbOn.iInter (K := 2) (ι := fun N => OffDiag N)
    (Ω := fun N p _ => {ω | ω.2 p = 0}) (fun N => ?_)
    ⟨1, one_pos, 1, one_pos, 0, fun N _ p L hL => ?_⟩
  · have h1 : Fintype.card (OffDiag N) ≤ N * N := by
      calc Fintype.card (OffDiag N) ≤ Fintype.card (Fin N × Fin N) :=
            Fintype.card_subtype_le _
        _ = N * N := by simp
    calc (Fintype.card (OffDiag N) : ℝ) ≤ (N : ℝ) * N := by exact_mod_cast h1
      _ = (N : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
  · subst hL
    have := law_off_ne N p
    rw [Set.compl_ofPred]
    simp only [diracLaws] at this ⊢
    rw [show {a : Entries N | ¬a.2 p = 0} = {ω | ω.2 p ≠ 0} from rfl, this]
    exact zero_le

/-- For `N = 3` the event that all diagonal entries vanish is not the whole space. -/
lemma diag_zero_ne_univ :
    (⋂ k : Fin 3, {ω : Entries 3 | ω.1 k = 0}) ≠ Set.univ := by
  intro h
  have : ((fun _ => 1 : Fin 3 → ℝ), (fun _ => 0 : OffDiag 3 → ℝ)) ∈
      (⋂ k : Fin 3, {ω : Entries 3 | ω.1 k = 0}) := by rw [h]; trivial
  simp at this

/-- For `N = 3` the event that all upper entries vanish is not the whole space. -/
lemma off_zero_ne_univ :
    (⋂ p : OffDiag 3, {ω : Entries 3 | ω.2 p = 0}) ≠ Set.univ := by
  intro h
  have : ((fun _ => 0 : Fin 3 → ℝ), (fun _ => 1 : OffDiag 3 → ℝ)) ∈
      (⋂ p : OffDiag 3, {ω : Entries 3 | ω.2 p = 0}) := by rw [h]; trivial
  exact one_ne_zero (Set.mem_iInter.1 this ⟨(0, 1), by decide⟩)

/-- Witness for `HighProbOn.iInter`: `ι N = Fin N` (so `N = 3` has three events) and `K = 1`;
the class is the point-mass family, a probability law, and the event is not trivial. -/
example :
    (diracLaws 3).IsProb ∧ (⋂ k : Fin 3, {ω : Entries 3 | ω.1 k = 0}) ≠ Set.univ ∧
      HighProbOn 1 diracCls (fun N _ => ⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}) :=
  ⟨diracLaws_isProb 3, diag_zero_ne_univ, diag_highProb 1⟩

/-- Witness for `HighProbOn.iInter` over the upper entries, with `K = 2`. -/
example :
    (diracLaws 3).IsProb ∧ (⋂ p : OffDiag 3, {ω : Entries 3 | ω.2 p = 0}) ≠ Set.univ ∧
      HighProbOn 1 diracCls (fun N _ => ⋂ p : OffDiag N, {ω : Entries N | ω.2 p = 0}) :=
  ⟨diracLaws_isProb 3, off_zero_ne_univ, off_highProb 1⟩

/-- Witness for `HighProbOn.inter`: two nontrivial events, each of high probability. -/
example :
    (diracLaws 3).IsProb ∧
      (⋂ k : Fin 3, {ω : Entries 3 | ω.1 k = 0}) ≠ Set.univ ∧
      (⋂ p : OffDiag 3, {ω : Entries 3 | ω.2 p = 0}) ≠ Set.univ ∧
      HighProbOn 1 diracCls (fun N _ => (⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}) ∩
        (⋂ p : OffDiag N, {ω : Entries N | ω.2 p = 0})) :=
  ⟨diracLaws_isProb 3, diag_zero_ne_univ, off_zero_ne_univ,
    HighProbOn.inter (diag_highProb 1) (off_highProb 1)⟩

/-- Witness for `HighProbOn.mono`: the intersection is contained in the diagonal event. -/
example :
    HighProbOn 1 diracCls (fun N _ => ⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}) :=
  HighProbOn.mono (HighProbOn.inter (diag_highProb 1) (off_highProb 1))
    (fun _ _ _ hω => hω.1)

/-- Witness for `HighProbOn.of_le_zeta`: `ζ' = 1/2 ≤ ζ = 1`. -/
example :
    HighProbOn (1 / 2) diracCls (fun N _ => ⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}) :=
  HighProbOn.of_le_zeta (by norm_num) (by norm_num) (diag_highProb 1)

/-- Witness for `HighProbOn.tendstoOneOn` with `ζ = 1`. -/
example :
    TendstoOneOn diracCls (fun N _ => ⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}) :=
  HighProbOn.tendstoOneOn one_pos (diag_highProb 1)

/-- Witness for `phi_rpow_le_rpow`: a concrete real value at `C = 1`, `c = 1`. -/
example : ∀ᶠ N : ℕ in atTop, phi N ^ (1 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
  phi_rpow_le_rpow 1 one_pos

#print axioms phi_eq_exp
#print axioms log_le_phi
#print axioms phi_rpow_le_rpow
#print axioms HighProbOn.inter
#print axioms HighProbOn.mono
#print axioms HighProbOn.of_le_zeta
#print axioms HighProbOn.iInter
#print axioms HighProbOn.tendstoOneOn

end WEdgeNS
