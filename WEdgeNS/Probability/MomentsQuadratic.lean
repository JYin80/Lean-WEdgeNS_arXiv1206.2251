import WEdgeNS.Probability.MomentsLinear

/-!
# High moments of off-diagonal quadratic forms in independent bounded variables
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- `f` is a.e. bounded in absolute value by some constant. -/
private def MQBdd {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∃ c, ∀ᵐ ω ∂μ, |f ω| ≤ c

section Bdd
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Constants are a.e. bounded. -/
private lemma MQBdd.const (c : ℝ) : MQBdd μ (fun _ => c) :=
  ⟨|c|, Eventually.of_forall fun _ => le_rfl⟩

/-- Sums of a.e. bounded functions are a.e. bounded. -/
private lemma MQBdd.add {f g : Ω → ℝ} (hf : MQBdd μ f) (hg : MQBdd μ g) :
    MQBdd μ (fun ω => f ω + g ω) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  exact ⟨c + d, by
    filter_upwards [hc, hd] with ω h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)⟩

/-- Products of a.e. bounded functions are a.e. bounded. -/
private lemma MQBdd.mul {f g : Ω → ℝ} (hf : MQBdd μ f) (hg : MQBdd μ g) :
    MQBdd μ (fun ω => f ω * g ω) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c * d, ?_⟩
  filter_upwards [hc, hd] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- Powers of a.e. bounded functions are a.e. bounded. -/
private lemma MQBdd.pow {f : Ω → ℝ} (hf : MQBdd μ f) (m : ℕ) : MQBdd μ (fun ω => f ω ^ m) := by
  induction m with
  | zero => simpa using MQBdd.const (μ := μ) 1
  | succ m ih => simpa [pow_succ] using ih.mul hf

/-- Finite sums of a.e. bounded functions are a.e. bounded. -/
private lemma MQBdd.sum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, MQBdd μ (f i)) : MQBdd μ (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MQBdd.const (μ := μ) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A measurable a.e. bounded function is integrable for a finite measure. -/
private lemma MQBdd.integrable [IsFiniteMeasure μ] {f : Ω → ℝ} (hm : Measurable f)
    (hf : MQBdd μ f) : Integrable f μ := by
  obtain ⟨c, hc⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable c
    (by filter_upwards [hc] with ω h; simpa [Real.norm_eq_abs] using h)

end Bdd

/-- `u ^ (n - m) * v ^ m ≤ u ^ n + v ^ n` for `u, v ≥ 0` and `m ≤ n`. -/
private lemma momentsQuadratic_pow_mul_pow_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {m n : ℕ}
    (hmn : m ≤ n) : u ^ (n - m) * v ^ m ≤ u ^ n + v ^ n := by
  have h1 : u ^ (n - m) * v ^ m ≤ max u v ^ (n - m) * max u v ^ m := by
    gcongr
    · exact le_max_left _ _
    · exact le_max_right _ _
  rw [← pow_add, Nat.sub_add_cancel hmn] at h1
  rcases max_choice u v with h | h <;> rw [h] at h1 <;>
    linarith [pow_nonneg hu n, pow_nonneg hv n]

/-- An off-diagonal double sum over `Fin n` as a sum over the pairs `j < i`. -/
private lemma momentsQuadratic_sum_offDiag {n : ℕ} (f : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, (if i = j then 0 else f i j) =
      ∑ i, ∑ j, (if j < i then f i j + f j i else 0) := by
  have h1 : ∀ i j : Fin n, (if i = j then 0 else f i j) =
      (if j < i then f i j else 0) + (if i < j then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, (if i < j then f i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, (if j < i then f j i else 0) := Finset.sum_comm
  calc ∑ i, ∑ j, (if i = j then 0 else f i j)
      = ∑ i, ∑ j, ((if j < i then f i j else 0) + (if i < j then f i j else 0)) := by
        simp_rw [h1]
    _ = ∑ i, ∑ j, (if j < i then f i j else 0) + ∑ i, ∑ j, (if i < j then f i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, (if j < i then f i j else 0) + ∑ i, ∑ j, (if j < i then f j i else 0) := by
        rw [h2]
    _ = ∑ i, ∑ j, (if j < i then f i j + f j i else 0) := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp


/-- One step of the moment recursion: for `X` independent of `(Y, Z)`, centred, bounded by `L`,
with second moment at most `s`, and `E Z ^ (2p) ≤ T ^ (2p)`, `E Y ^ (2p) ≤ y ^ (2p)`, the binomial
expansion of `E (Z + X Y) ^ (2p)` is bounded term by term. -/
private lemma momentsQuadratic_step {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y Z : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hXb : MQBdd μ X) (hYb : MQBdd μ Y) (hZb : MQBdd μ Z)
    (hind : IndepFun X (fun ω => (Y ω, Z ω)) μ) (h0 : ∫ ω, X ω ∂μ = 0)
    {L s : ℝ} (hL : 0 ≤ L) (hXbd : ∀ᵐ ω ∂μ, |X ω| ≤ L) (hXvar : ∫ ω, X ω ^ 2 ∂μ ≤ s)
    (p : ℕ) {T y : ℝ} (hT : 0 < T) (hy : 0 < y)
    (hZm : ∫ ω, Z ω ^ (2 * p) ∂μ ≤ T ^ (2 * p)) (hYm : ∫ ω, Y ω ^ (2 * p) ∂μ ≤ y ^ (2 * p)) :
    ∫ ω, (Z ω + X ω * Y ω) ^ (2 * p) ∂μ ≤ ∫ ω, Z ω ^ (2 * p) ∂μ +
      ∑ m ∈ Finset.range (2 * p + 1), (if 2 ≤ m then ((2 * p).choose m : ℝ) *
        (s * L ^ (m - 2)) * (2 * (T ^ (2 * p - m) * y ^ m)) else 0) := by
  set n := 2 * p with hn
  have hint : ∀ m, Integrable (fun ω => (X ω * Y ω) ^ m * Z ω ^ (n - m) * (n.choose m : ℝ)) μ :=
    fun m => MQBdd.integrable (by fun_prop)
      ((((hXb.mul hYb).pow m).mul (hZb.pow _)).mul (MQBdd.const _))
  have hexp : (fun ω => (Z ω + X ω * Y ω) ^ n) = fun ω => ∑ m ∈ Finset.range (n + 1),
      (X ω * Y ω) ^ m * Z ω ^ (n - m) * (n.choose m : ℝ) := by
    funext ω; rw [add_comm, add_pow]
  -- moments of `X`
  have hXmom : ∀ m, 2 ≤ m → |∫ ω, X ω ^ m ∂μ| ≤ s * L ^ (m - 2) := by
    intro m hm
    have hi2 : Integrable (fun ω => L ^ (m - 2) * X ω ^ 2) μ :=
      MQBdd.integrable (by fun_prop) ((MQBdd.const _).mul (hXb.pow 2))
    calc |∫ ω, X ω ^ m ∂μ| ≤ ∫ ω, |X ω ^ m| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, L ^ (m - 2) * X ω ^ 2 ∂μ := by
          refine integral_mono_ae (MQBdd.integrable (by fun_prop) (hXb.pow m)).abs hi2 ?_
          filter_upwards [hXbd] with ω hω
          have : |X ω ^ m| = |X ω| ^ (m - 2) * X ω ^ 2 := by
            rw [abs_pow, ← sq_abs (X ω), ← pow_add, Nat.sub_add_cancel hm]
          rw [this]
          gcongr
      _ = L ^ (m - 2) * ∫ ω, X ω ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ L ^ (m - 2) * s := by gcongr
      _ = s * L ^ (m - 2) := mul_comm _ _
  -- mixed moments of `Y` and `Z`
  have hYZ : ∀ m, m ≤ n → |∫ ω, Y ω ^ m * Z ω ^ (n - m) ∂μ| ≤ 2 * (T ^ (n - m) * y ^ m) := by
    intro m hm
    have hn2 : Even n := even_two_mul p
    have hig : Integrable (fun ω => T ^ (n - m) * y ^ m *
        ((Z ω / T) ^ n + (Y ω / y) ^ n)) μ :=
      MQBdd.integrable (by fun_prop)
        ((MQBdd.const _).mul (((hZb.mul (MQBdd.const _)).pow n).add
          ((hYb.mul (MQBdd.const _)).pow n)))
    calc |∫ ω, Y ω ^ m * Z ω ^ (n - m) ∂μ| ≤ ∫ ω, |Y ω ^ m * Z ω ^ (n - m)| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, T ^ (n - m) * y ^ m * ((Z ω / T) ^ n + (Y ω / y) ^ n) ∂μ := by
          refine integral_mono (MQBdd.integrable (by fun_prop)
            ((hYb.pow m).mul (hZb.pow _))).abs hig fun ω => ?_
          have hu : 0 ≤ |Z ω| / T := div_nonneg (abs_nonneg _) hT.le
          have hv : 0 ≤ |Y ω| / y := div_nonneg (abs_nonneg _) hy.le
          have key := momentsQuadratic_pow_mul_pow_le hu hv hm
          have e1 : |Y ω ^ m * Z ω ^ (n - m)| =
              T ^ (n - m) * y ^ m * ((|Z ω| / T) ^ (n - m) * (|Y ω| / y) ^ m) := by
            rw [abs_mul, abs_pow, abs_pow, div_pow, div_pow]
            field_simp
          have e2 : (Z ω / T) ^ n + (Y ω / y) ^ n = (|Z ω| / T) ^ n + (|Y ω| / y) ^ n := by
            rw [div_pow, div_pow, div_pow, div_pow, hn2.pow_abs, hn2.pow_abs]
          rw [e1, e2]
          gcongr
      _ = T ^ (n - m) * y ^ m * ((∫ ω, Z ω ^ n ∂μ) / T ^ n + (∫ ω, Y ω ^ n ∂μ) / y ^ n) := by
          rw [integral_const_mul, integral_add]
          · simp_rw [div_pow]
            rw [integral_div, integral_div]
          · exact MQBdd.integrable (by fun_prop) ((hZb.mul (MQBdd.const _)).pow n)
          · exact MQBdd.integrable (by fun_prop) ((hYb.mul (MQBdd.const _)).pow n)
      _ ≤ T ^ (n - m) * y ^ m * (1 + 1) := by
          have hTn : 0 < T ^ n := pow_pos hT n
          have hyn : 0 < y ^ n := pow_pos hy n
          gcongr
          · exact (div_le_one hTn).2 hZm
          · exact (div_le_one hyn).2 hYm
      _ = 2 * (T ^ (n - m) * y ^ m) := by ring
  have hterm : ∀ m ∈ Finset.range (n + 1),
      ∫ ω, (X ω * Y ω) ^ m * Z ω ^ (n - m) * (n.choose m : ℝ) ∂μ ≤
        (if m = 0 then ∫ ω, Z ω ^ n ∂μ else 0) + (if 2 ≤ m then (n.choose m : ℝ) *
          (s * L ^ (m - 2)) * (2 * (T ^ (n - m) * y ^ m)) else 0) := by
    intro m hm
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · simp
    have hsplit : (fun ω => (X ω * Y ω) ^ m * Z ω ^ (n - m) * (n.choose m : ℝ)) =
        fun ω => (n.choose m : ℝ) * (X ω ^ m * (Y ω ^ m * Z ω ^ (n - m))) := by
      funext ω; ring
    have hI : IndepFun (fun ω => X ω ^ m) (fun ω => Y ω ^ m * Z ω ^ (n - m)) μ :=
      hind.comp (φ := fun x : ℝ => x ^ m) (ψ := fun yz : ℝ × ℝ => yz.1 ^ m * yz.2 ^ (n - m))
        (by fun_prop) (by fun_prop)
    have hprod : ∫ ω, X ω ^ m * (Y ω ^ m * Z ω ^ (n - m)) ∂μ =
        (∫ ω, X ω ^ m ∂μ) * ∫ ω, Y ω ^ m * Z ω ^ (n - m) ∂μ :=
      hI.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)
    rw [hsplit, integral_const_mul, hprod, ite_eq_right hm1.ne', zero_add]
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have : m = 1 := by omega
      subst this
      simp [h0]
    rw [ite_eq_left hm2, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc (∫ ω, X ω ^ m ∂μ) * ∫ ω, Y ω ^ m * Z ω ^ (n - m) ∂μ
        ≤ |(∫ ω, X ω ^ m ∂μ) * ∫ ω, Y ω ^ m * Z ω ^ (n - m) ∂μ| := le_abs_self _
      _ = |∫ ω, X ω ^ m ∂μ| * |∫ ω, Y ω ^ m * Z ω ^ (n - m) ∂μ| := abs_mul _ _
      _ ≤ (s * L ^ (m - 2)) * (2 * (T ^ (n - m) * y ^ m)) :=
          mul_le_mul (hXmom m hm2) (hYZ m hmn) (abs_nonneg _)
            ((abs_nonneg _).trans (hXmom m hm2))
  rw [hexp, integral_finsetSum _ (fun m _ => hint m)]
  calc ∑ m ∈ Finset.range (n + 1), ∫ ω, (X ω * Y ω) ^ m * Z ω ^ (n - m) * (n.choose m : ℝ) ∂μ
      ≤ ∑ m ∈ Finset.range (n + 1), ((if m = 0 then ∫ ω, Z ω ^ n ∂μ else 0) +
          (if 2 ≤ m then (n.choose m : ℝ) * (s * L ^ (m - 2)) *
            (2 * (T ^ (n - m) * y ^ m)) else 0)) := Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (n + 1)) 0]
        simp


/-- Even moments of an off-diagonal quadratic form with real coefficients bounded by `β`,
under `q ≥ 1` and `n ≤ N`: the form is the sum of the increments `a k * Y k`, where `Y k` is a
linear form in the earlier variables, and the moment recursion is closed with the linear-form
bound `hlin` (Lemma A.1 (i) of [15]). -/
private lemma momentsQuadratic_real {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℝ} (hK : 0 < K) {n N : ℕ} {a : Fin n → Ω → ℝ}
    (hind : iIndepFun a μ) (hmeas : ∀ i, Measurable (a i)) (h0 : ∀ i, ∫ ω, a i ω ∂μ = 0)
    {q : ℝ} (hq : 0 < q) (hq1 : 1 ≤ q) (hnN : n ≤ N)
    (hbd : ∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ q⁻¹) (hvar : ∀ i, ∫ ω, a i ω ^ 2 ∂μ ≤ K / N)
    {p : ℕ} (hp : 1 ≤ p) {C1 : ℝ} (hC1 : 0 < C1)
    (hlin : ∀ A : Fin n → ℂ, ∫ ω, ‖∑ i, A i * a i ω‖ ^ (2 * p) ∂μ ≤
        (C1 * p) ^ (2 * p) * ((⨆ i, ‖A i‖) / q + Real.sqrt (K / N * ∑ i, ‖A i‖ ^ 2)) ^ (2 * p))
    (b : Fin n → Fin n → ℝ) {β σ : ℝ} (hβ : 0 < β) (hb : ∀ i j, i ≠ j → |b i j| ≤ β)
    (hσ : 0 ≤ σ) (hbσ : ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, (if i = j then 0 else b i j ^ 2) ≤ σ ^ 2) :
    ∫ ω, (∑ i, ∑ j, (if i = j then 0 else b i j * a i ω * a j ω)) ^ (2 * p) ∂μ ≤
      (64 * C1 * (K + 1) * p ^ 2 * (β / q + σ)) ^ (2 * p) := by
  classical
  set L : ℝ := q⁻¹ with hLdef
  set s : ℝ := K / N with hsdef
  set κ : ℝ := K + 1 with hκdef
  set D : ℝ := β / q + σ with hDdef
  set A : ℝ := 8 * C1 * κ * p * D with hAdef
  set T : ℝ := 64 * C1 * κ * p ^ 2 * D with hTdef
  have hL0 : 0 < L := inv_pos.mpr hq
  have hL1 : L ≤ 1 := inv_le_one_of_one_le₀ hq1
  have hs0 : 0 ≤ s := div_nonneg hK.le (Nat.cast_nonneg _)
  have hns : (n : ℝ) * s ≤ K := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · simp [hsdef, hN, hK.le]
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      rw [hsdef, ← mul_div_assoc, div_le_iff₀ hN', mul_comm K]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) hK.le
  have hκ1 : 1 ≤ κ := by linarith
  have hKκ : K ≤ κ := by linarith
  have hβL : β / q = β * L := div_eq_mul_inv _ _
  have hβq : 0 < β / q := div_pos hβ hq
  have hD : 0 < D := by linarith
  have hσD : σ ≤ D := by linarith
  have hβD : β * L ≤ D := by rw [← hβL]; linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hA0 : 0 < A := by positivity
  have hT0 : 0 < T := by positivity
  have hTA : T = 8 * p * A := by rw [hTdef, hAdef]; ring
  -- coefficients of the decomposition into increments
  set c : Fin n → Fin n → ℝ := fun l j => if j < l then b l j + b j l else 0 with hcdef
  set Y : Fin n → Ω → ℝ := fun l ω => ∑ j, c l j * a j ω with hYdef
  set Z : ℕ → Ω → ℝ := fun k ω => ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < k),
    a l ω * Y l ω with hZdef
  set r : Fin n → ℝ := fun l => Real.sqrt (s * ∑ j, ‖(c l j : ℂ)‖ ^ 2) with hrdef
  set y : Fin n → ℝ := fun l => C1 * p * (2 * (β / q) + r l) with hydef
  have hc : ∀ l j, |c l j| ≤ 2 * β := by
    intro l j
    simp only [hcdef]
    split_ifs with h
    · calc |b l j + b j l| ≤ |b l j| + |b j l| := abs_add_le _ _
        _ ≤ β + β := add_le_add (hb l j h.ne') (hb j l h.ne)
        _ = 2 * β := by ring
    · simp; linarith
  have hcn : ∀ l j, ‖(c l j : ℂ)‖ ^ 2 = c l j ^ 2 := by
    intro l j; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hr0 : ∀ l, 0 ≤ r l := fun l => Real.sqrt_nonneg _
  have hrsq : ∀ l, r l ^ 2 = s * ∑ j, c l j ^ 2 := by
    intro l
    simp only [hrdef, hcn]
    exact Real.sq_sqrt (mul_nonneg hs0 (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hrsq_le : ∀ l, s * ∑ j, c l j ^ 2 ≤ (2 * κ * β) ^ 2 := by
    intro l
    calc s * ∑ j, c l j ^ 2 ≤ s * ∑ _j : Fin n, (2 * β) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hc l j) 2) hs0
      _ = (n * s) * (2 * β) ^ 2 := by simp; ring
      _ ≤ K * (2 * β) ^ 2 := by gcongr
      _ ≤ κ ^ 2 * (2 * β) ^ 2 := by gcongr; nlinarith
      _ = (2 * κ * β) ^ 2 := by ring
  have hr_le : ∀ l, r l ≤ 2 * κ * β := by
    intro l
    have h2 : r l ^ 2 ≤ (2 * κ * β) ^ 2 := (hrsq l).trans_le (hrsq_le l)
    have : 0 ≤ 2 * κ * β := by positivity
    exact (pow_le_pow_iff_left₀ (hr0 l) this (by norm_num)).1 h2
  have hcsq : ∑ l, ∑ j, c l j ^ 2 ≤ 2 * ∑ i, ∑ j, (if i = j then 0 else b i j ^ 2) := by
    rw [momentsQuadratic_sum_offDiag (fun i j => b i j ^ 2), Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [hcdef]
    split_ifs
    · nlinarith [sq_nonneg (b l j - b j l)]
    · simp
  have hy0 : ∀ l, 0 < y l := by
    intro l
    have := hr0 l
    simp only [hydef]
    positivity
  -- moments of the linear forms `Y l`
  have hYm : ∀ l, ∫ ω, Y l ω ^ (2 * p) ∂μ ≤ y l ^ (2 * p) := by
    intro l
    have h := hlin (fun j => (c l j : ℂ))
    have hlhs : ∀ ω, ‖∑ j, (c l j : ℂ) * (a j ω : ℂ)‖ ^ (2 * p) = Y l ω ^ (2 * p) := by
      intro ω
      have : ∑ j, (c l j : ℂ) * (a j ω : ℂ) = ((Y l ω : ℝ) : ℂ) := by
        simp only [hYdef]; push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_eq_abs, (even_two_mul p).pow_abs]
    simp_rw [hlhs] at h
    refine h.trans ?_
    have hsup : (⨆ j, ‖(c l j : ℂ)‖) / q ≤ 2 * (β / q) := by
      have : Nonempty (Fin n) := ⟨l⟩
      rw [mul_div_assoc']
      gcongr
      refine ciSup_le fun j => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hc l j
    have hsup0 : 0 ≤ (⨆ j, ‖(c l j : ℂ)‖) / q :=
      div_nonneg (Real.iSup_nonneg fun j => norm_nonneg _) hq.le
    have e : y l ^ (2 * p) = (C1 * p) ^ (2 * p) * (2 * (β / q) + r l) ^ (2 * p) := mul_pow _ _ _
    rw [e]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg hsup0 (Real.sqrt_nonneg _))
      (add_le_add hsup le_rfl) _) (by positivity)
  -- the sums of the step increments
  have hYsum : ∀ m, 2 ≤ m → ∑ l, s * L ^ (m - 2) * y l ^ m ≤ A ^ m := by
    intro m hm
    have hLm : L ^ (m - 2) ≤ 1 := pow_le_one₀ hL0.le hL1
    have hyl : ∀ l, y l ^ m ≤ (C1 * p) ^ m * 2 ^ m * ((2 * (β * L)) ^ m + r l ^ m) := by
      intro l
      have hu : 0 ≤ 2 * (β * L) := by positivity
      have h2 : (2 * (β * L) + r l) ^ m ≤ 2 ^ m * ((2 * (β * L)) ^ m + r l ^ m) := by
        calc (2 * (β * L) + r l) ^ m ≤ (2 * max (2 * (β * L)) (r l)) ^ m :=
              pow_le_pow_left₀ (add_nonneg hu (hr0 l))
                (by linarith [le_max_left (2 * (β * L)) (r l), le_max_right (2 * (β * L)) (r l)]) m
          _ = 2 ^ m * max (2 * (β * L)) (r l) ^ m := mul_pow _ _ _
          _ ≤ 2 ^ m * ((2 * (β * L)) ^ m + r l ^ m) := by
              gcongr
              rcases max_choice (2 * (β * L)) (r l) with h | h <;> rw [h]
              · linarith [pow_nonneg (hr0 l) m]
              · linarith [pow_nonneg hu m]
      rw [show y l = (C1 * p) * (2 * (β * L) + r l) by simp only [hydef, hβL], mul_pow,
        mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    -- the `β L` terms
    have hfirst : ∑ _l : Fin n, s * L ^ (m - 2) * (2 * (β * L)) ^ m ≤ (2 * κ * D) ^ m := by
      calc ∑ _l : Fin n, s * L ^ (m - 2) * (2 * (β * L)) ^ m
          = (n * s) * L ^ (m - 2) * (2 * (β * L)) ^ m := by simp; ring
        _ ≤ K * 1 * (2 * D) ^ m := by gcongr
        _ ≤ κ ^ m * (2 * D) ^ m := by
            rw [mul_one]
            gcongr
            exact hKκ.trans (le_self_pow₀ hκ1 (by omega))
        _ = (2 * κ * D) ^ m := by rw [← mul_pow]; ring
    -- the `r l` terms
    have hsecond : ∑ l, s * L ^ (m - 2) * r l ^ m ≤ (2 * κ * D) ^ m := by
      have hpt : ∀ l, s * L ^ (m - 2) * r l ^ m ≤ s * r l ^ 2 * (2 * κ * D) ^ (m - 2) := by
        intro l
        have e : r l ^ m = r l ^ 2 * r l ^ (m - 2) := by
          rw [← pow_add]; congr 1; omega
        have hrl : L * r l ≤ 2 * κ * D := by
          calc L * r l ≤ L * (2 * κ * β) := mul_le_mul_of_nonneg_left (hr_le l) hL0.le
            _ = 2 * κ * (β * L) := by ring
            _ ≤ 2 * κ * D := mul_le_mul_of_nonneg_left hβD (by positivity)
        calc s * L ^ (m - 2) * r l ^ m = s * r l ^ 2 * (L * r l) ^ (m - 2) := by
              rw [e, mul_pow]; ring
          _ ≤ s * r l ^ 2 * (2 * κ * D) ^ (m - 2) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hL0.le (hr0 l)) hrl _)
                (mul_nonneg hs0 (sq_nonneg _))
      have hsr : ∑ l, s * r l ^ 2 = s ^ 2 * ∑ l, ∑ j, c l j ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hrsq]; ring
      have hs2 : s ^ 2 * ∑ l, ∑ j, c l j ^ 2 ≤ 2 * κ ^ 2 * D ^ 2 := by
        have hs2' : s ^ 2 = K ^ 2 * ((N : ℝ) ^ 2)⁻¹ := by rw [hsdef, div_pow, div_eq_mul_inv]
        have hb0 : 0 ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, (if i = j then 0 else b i j ^ 2) := by
          refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
            Finset.sum_nonneg fun j _ => ?_)
          split_ifs <;> positivity
        calc s ^ 2 * ∑ l, ∑ j, c l j ^ 2
            ≤ s ^ 2 * (2 * ∑ i, ∑ j, (if i = j then 0 else b i j ^ 2)) :=
              mul_le_mul_of_nonneg_left hcsq (sq_nonneg _)
          _ = 2 * K ^ 2 * (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, (if i = j then 0 else b i j ^ 2)) := by
              rw [hs2']; ring
          _ ≤ 2 * κ ^ 2 * D ^ 2 := by
              have hσ2 : σ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hσ hσD 2
              have hK2 : K ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hK.le hKκ 2
              calc 2 * K ^ 2 * (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, (if i = j then 0 else b i j ^ 2))
                  ≤ 2 * κ ^ 2 * σ ^ 2 := by gcongr
                _ ≤ 2 * κ ^ 2 * D ^ 2 := by gcongr
      calc ∑ l, s * L ^ (m - 2) * r l ^ m ≤ ∑ l, s * r l ^ 2 * (2 * κ * D) ^ (m - 2) :=
            Finset.sum_le_sum fun l _ => hpt l
        _ = (∑ l, s * r l ^ 2) * (2 * κ * D) ^ (m - 2) := by rw [Finset.sum_mul]
        _ ≤ (2 * κ ^ 2 * D ^ 2) * (2 * κ * D) ^ (m - 2) := by
            rw [hsr]; gcongr
        _ ≤ (2 * κ * D) ^ 2 * (2 * κ * D) ^ (m - 2) := by
            gcongr
            nlinarith [sq_nonneg (κ * D)]
        _ = (2 * κ * D) ^ m := by rw [← pow_add]; congr 1; omega
    calc ∑ l, s * L ^ (m - 2) * y l ^ m
        ≤ ∑ l, (C1 * p) ^ m * 2 ^ m * (s * L ^ (m - 2) * (2 * (β * L)) ^ m +
            s * L ^ (m - 2) * r l ^ m) := by
          refine Finset.sum_le_sum fun l _ => ?_
          calc s * L ^ (m - 2) * y l ^ m
              ≤ s * L ^ (m - 2) * ((C1 * p) ^ m * 2 ^ m * ((2 * (β * L)) ^ m + r l ^ m)) :=
                mul_le_mul_of_nonneg_left (hyl l) (by positivity)
            _ = _ := by ring
      _ = (C1 * p) ^ m * 2 ^ m * (∑ _l : Fin n, s * L ^ (m - 2) * (2 * (β * L)) ^ m +
            ∑ l, s * L ^ (m - 2) * r l ^ m) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (C1 * p) ^ m * 2 ^ m * ((2 * κ * D) ^ m + (2 * κ * D) ^ m) := by
          gcongr
      _ = (C1 * p) ^ m * 2 ^ m * 2 * (2 * κ * D) ^ m := by ring
      _ ≤ (C1 * p) ^ m * 2 ^ m * 2 ^ m * (2 * κ * D) ^ m := by
          gcongr
          exact le_self_pow₀ (by norm_num) (by omega)
      _ = A ^ m := by
          rw [hAdef, ← mul_pow, ← mul_pow, ← mul_pow]
          congr 1
          ring
  -- the total of the step increments
  set g : Fin n → ℕ → ℝ := fun l m => if 2 ≤ m then ((2 * p).choose m : ℝ) *
    (s * L ^ (m - 2)) * (2 * (T ^ (2 * p - m) * y l ^ m)) else 0 with hgdef
  set inc : Fin n → ℝ := fun l => ∑ m ∈ Finset.range (2 * p + 1), g l m with hincdef
  have hg0 : ∀ l m, 0 ≤ g l m := by
    intro l m
    simp only [hgdef]
    split_ifs
    · have := hy0 l
      positivity
    · exact le_rfl
  have hinc0 : ∀ l, 0 ≤ inc l := fun l => Finset.sum_nonneg fun m _ => hg0 l m
  have htot : ∑ l, inc l ≤ T ^ (2 * p) := by
    have hm_le : ∀ m ∈ Finset.range (2 * p + 1),
        ∑ l, g l m ≤ T ^ (2 * p) / 2 * (1 / 2) ^ m := by
      intro m hm
      have hmn : m ≤ 2 * p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      by_cases h2 : 2 ≤ m
      · have e : ∑ l, g l m = ((2 * p).choose m : ℝ) * 2 * T ^ (2 * p - m) *
            ∑ l, s * L ^ (m - 2) * y l ^ m := by
          simp only [hgdef, ite_eq_left h2, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [e]
        have hch : ((2 * p).choose m : ℝ) * 2 ≤ (2 * p : ℝ) ^ m := by
          have h1 := Nat.choose_le_pow_div (α := ℝ) m (2 * p)
          have hf : (2 : ℝ) ≤ m.factorial := by
            exact_mod_cast (Nat.factorial_le h2 : (2 : ℕ).factorial ≤ m.factorial)
          have hf0 : (0 : ℝ) < m.factorial := by positivity
          push_cast at h1
          rw [le_div_iff₀ hf0] at h1
          exact (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _)).trans h1
        have hTm : T ^ (2 * p) / 2 * (1 / 2) ^ m = T ^ (2 * p - m) * A ^ m * ((4 * p) ^ m / 2) := by
          rw [← pow_sub_mul_pow T hmn]
          have hT2 : T * (1 / 2) = 4 * p * A := by rw [hTA]; ring
          have : T ^ m * (1 / 2) ^ m = (4 * p) ^ m * A ^ m := by
            rw [← mul_pow T, hT2, mul_pow]
          calc T ^ (2 * p - m) * T ^ m / 2 * (1 / 2) ^ m
              = T ^ (2 * p - m) * (T ^ m * (1 / 2) ^ m) / 2 := by ring
            _ = _ := by rw [this]; ring
        rw [hTm]
        have h4 : (2 * p : ℝ) ^ m ≤ (4 * p) ^ m / 2 := by
          have : (4 * p : ℝ) ^ m = 2 ^ m * (2 * p) ^ m := by
            rw [← mul_pow]; congr 1; ring
          rw [this]
          have h22 : (2 : ℝ) ≤ 2 ^ m := le_self_pow₀ (by norm_num) (by omega)
          have : (0 : ℝ) ≤ (2 * p) ^ m := by positivity
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
          calc (2 * p : ℝ) ^ m * 2 ≤ (2 * p) ^ m * 2 ^ m := mul_le_mul_of_nonneg_left h22 this
            _ = 2 ^ m * (2 * p) ^ m := mul_comm _ _
        calc ((2 * p).choose m : ℝ) * 2 * T ^ (2 * p - m) * ∑ l, s * L ^ (m - 2) * y l ^ m
            ≤ (2 * p : ℝ) ^ m * T ^ (2 * p - m) * A ^ m := by
              rw [mul_assoc _ (T ^ (2 * p - m)), mul_assoc _ (T ^ (2 * p - m))]
              gcongr
              exact hYsum m h2
          _ ≤ (4 * p) ^ m / 2 * T ^ (2 * p - m) * A ^ m := by gcongr
          _ = _ := by ring
      · have : ∀ l, g l m = 0 := fun l => by simp only [hgdef, ite_eq_right h2]
        simp only [this, Finset.sum_const_zero]
        positivity
    calc ∑ l, inc l = ∑ m ∈ Finset.range (2 * p + 1), ∑ l, g l m := by
          simp only [hincdef]; exact Finset.sum_comm
      _ ≤ ∑ m ∈ Finset.range (2 * p + 1), T ^ (2 * p) / 2 * (1 / 2) ^ m :=
          Finset.sum_le_sum hm_le
      _ = T ^ (2 * p) / 2 * ∑ m ∈ Finset.range (2 * p + 1), (1 / 2 : ℝ) ^ m := by
          rw [Finset.mul_sum]
      _ ≤ T ^ (2 * p) / 2 * 2 := by
          gcongr
          exact sum_geometric_two_le _
      _ = T ^ (2 * p) := by ring
  -- measurability and boundedness
  have hab : ∀ i, MQBdd μ (a i) := fun i => ⟨L, hbd i⟩
  have hYb : ∀ l, MQBdd μ (Y l) := fun l =>
    MQBdd.sum (f := fun j ω => c l j * a j ω) Finset.univ fun j _ =>
      (MQBdd.const (c l j)).mul (hab j)
  have hYmeas : ∀ l, Measurable (Y l) := fun l =>
    Finset.measurable_sum (f := fun j ω => c l j * a j ω) _ fun j _ => (hmeas j).const_mul _
  have hZb : ∀ k, MQBdd μ (Z k) := fun k =>
    MQBdd.sum (f := fun l ω => a l ω * Y l ω) _ fun l _ => (hab l).mul (hYb l)
  have hZmeas : ∀ k, Measurable (Z k) := fun k =>
    Finset.measurable_sum (f := fun l ω => a l ω * Y l ω) _ fun l _ => (hmeas l).mul (hYmeas l)
  -- independence of the new variable from the past
  have hindep : ∀ k (hk : k < n), IndepFun (a ⟨k, hk⟩) (fun ω => (Y ⟨k, hk⟩ ω, Z k ω)) μ := by
    intro k hk
    have hdisj : Disjoint ({⟨k, hk⟩} : Set (Fin n)) {i : Fin n | i.val < k} := by
      rw [Set.disjoint_singleton_left]; simp
    have hI := indep_iSup_of_disjoint (fun i => (hmeas i).comap_le) hind.iIndep hdisj
    have haT : Measurable[⨆ i ∈ ({⟨k, hk⟩} : Set (Fin n)),
        MeasurableSpace.comap (a i) inferInstance] (a ⟨k, hk⟩) :=
      measurable_iff_comap_le.2 (le_iSup₂ (f := fun i (_ : i ∈ ({⟨k, hk⟩} : Set (Fin n))) =>
        MeasurableSpace.comap (a i) inferInstance) ⟨k, hk⟩ rfl)
    set mS : MeasurableSpace Ω := ⨆ i ∈ {i : Fin n | i.val < k},
      MeasurableSpace.comap (a i) inferInstance with hmS
    have haS : ∀ i : Fin n, i.val < k → Measurable[mS] (a i) := fun i hi =>
      measurable_iff_comap_le.2 (le_iSup₂ (f := fun i (_ : i ∈ {i : Fin n | i.val < k}) =>
        MeasurableSpace.comap (a i) inferInstance) i hi)
    have hYS : ∀ l : Fin n, l.val ≤ k → Measurable[mS] (Y l) := by
      intro l hl
      refine Finset.measurable_sum (f := fun j ω => c l j * a j ω) _ fun j _ => ?_
      by_cases hj : j < l
      · exact (haS j (lt_of_lt_of_le (Fin.lt_def.mp hj) hl)).const_mul _
      · have : c l j = 0 := by simp [hcdef, hj]
        simp only [this, zero_mul]
        exact measurable_const
    have hZS : Measurable[mS] (Z k) := by
      refine Finset.measurable_sum (f := fun l ω => a l ω * Y l ω) _ fun l hl => ?_
      have hl' : l.val < k := by simpa using hl
      exact (haS l hl').mul (hYS l hl'.le)
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le hI (measurable_iff_comap_le.1 haT)
      (measurable_iff_comap_le.1 ((hYS _ le_rfl).prodMk hZS))
  -- the recursion
  have hfil : ∀ k (hk : k < n), Finset.univ.filter (fun l : Fin n => l.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun l : Fin n => l.val < k)) := by
    intro k hk
    ext l
    simp [Fin.ext_iff]
    omega
  have hnotmem : ∀ k (hk : k < n), (⟨k, hk⟩ : Fin n) ∉
      Finset.univ.filter (fun l : Fin n => l.val < k) := by
    intro k hk; simp
  have hstepZ : ∀ k (hk : k < n), Z (k + 1) = fun ω => Z k ω + a ⟨k, hk⟩ ω * Y ⟨k, hk⟩ ω := by
    intro k hk
    funext ω
    simp only [hZdef]
    rw [hfil k hk, Finset.sum_insert (hnotmem k hk), add_comm]
  have hmain : ∀ k, k ≤ n → ∫ ω, Z k ω ^ (2 * p) ∂μ ≤
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < k), inc l := by
    intro k
    induction k with
    | zero =>
      intro _
      have hp2 : 2 * p ≠ 0 := by omega
      simp [hZdef, zero_pow hp2]
    | succ k ih =>
      intro hk1
      have hk : k < n := hk1
      have ih' := ih hk.le
      have hZT : ∫ ω, Z k ω ^ (2 * p) ∂μ ≤ T ^ (2 * p) :=
        ih'.trans ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun l _ _ => hinc0 l).trans htot)
      have hst := momentsQuadratic_step (hmeas ⟨k, hk⟩) (hYmeas _) (hZmeas k) (hab _) (hYb _)
        (hZb k) (hindep k hk) (h0 _) hL0.le (hbd _) (hvar _) p hT0 (hy0 _) hZT (hYm _)
      rw [hstepZ k hk, hfil k hk, Finset.sum_insert (hnotmem k hk)]
      calc ∫ ω, (Z k ω + a ⟨k, hk⟩ ω * Y ⟨k, hk⟩ ω) ^ (2 * p) ∂μ
          ≤ ∫ ω, Z k ω ^ (2 * p) ∂μ + inc ⟨k, hk⟩ := hst
        _ ≤ _ := by linarith
  have hQ : ∀ ω, (∑ i, ∑ j, (if i = j then 0 else b i j * a i ω * a j ω)) = Z n ω := by
    intro ω
    rw [momentsQuadratic_sum_offDiag (fun i j => b i j * a i ω * a j ω)]
    simp only [hZdef, hYdef, hcdef]
    rw [Finset.filter_true_of_mem (fun l _ => l.isLt)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  simp_rw [hQ]
  calc ∫ ω, Z n ω ^ (2 * p) ∂μ
      ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < n), inc l := hmain n le_rfl
    _ = ∑ l, inc l := by rw [Finset.filter_true_of_mem (fun l _ => l.isLt)]
    _ ≤ T ^ (2 * p) := htot

/-- High moments of off-diagonal quadratic forms (Lemma A.1 (ii), (A.4) of [15]),
bounded entries with variance at most `K/N`. -/
theorem moment_quadratic_le (K : ℝ) (hK : 0 < K) : ∃ C > 0, ∀ {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n N : ℕ) (a : Fin n → Ω → ℝ), iIndepFun a μ →
    (∀ i, Measurable (a i)) → (∀ i, ∫ ω, a i ω ∂μ = 0) → ∀ q : ℝ, 0 < q → 1 ≤ q → n ≤ N →
    (∀ i, ∀ᵐ ω ∂μ, |a i ω| ≤ q⁻¹) → (∀ i, ∫ ω, a i ω ^ 2 ∂μ ≤ K / N) →
    ∀ (B : Fin n → Fin n → ℂ) (p : ℕ), 1 ≤ p →
      ∫ ω, ‖∑ i, ∑ j, (if i = j then 0 else B i j * a i ω * a j ω)‖ ^ (2 * p) ∂μ ≤
        (C * p) ^ (4 * p) * ((⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖) / q +
          Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖B i j‖ ^ 2)) ^ (2 * p) := by
  obtain ⟨C1, hC1, hlin⟩ := moment_linear_le
  refine ⟨128 * C1 * (K + 1) + 1, by positivity, ?_⟩
  intro Ω _ μ _ n N a hind hmeas h0 q hq hq1 hnN hbd hvar B p hp
  set β : ℝ := ⨆ i, ⨆ j, if i = j then 0 else ‖B i j‖ with hβdef
  set σ : ℝ := Real.sqrt (((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖B i j‖ ^ 2)
    with hσdef
  set C : ℝ := 128 * C1 * (K + 1) + 1 with hCdef
  have hβ0 : 0 ≤ β := Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => by
    split_ifs <;> simp
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hBle : ∀ i j, i ≠ j → ‖B i j‖ ≤ β := by
    intro i j hij
    have h1 : (if i = j then 0 else ‖B i j‖) ≤ ⨆ j, if i = j then 0 else ‖B i j‖ :=
      le_ciSup (Finite.bddAbove_range (fun j => if i = j then 0 else ‖B i j‖)) j
    have h2 : (⨆ j, if i = j then (0 : ℝ) else ‖B i j‖) ≤ β :=
      le_ciSup (f := fun i => ⨆ j, if i = j then (0 : ℝ) else ‖B i j‖)
        (Finite.bddAbove_range _) i
    rw [ite_eq_right hij] at h1
    exact h1.trans h2
  have hD0 : 0 ≤ β / q + σ := add_nonneg (div_nonneg hβ0 hq.le) hσ0
  have hRHS0 : 0 ≤ (C * p) ^ (4 * p) * (β / q + σ) ^ (2 * p) := by
    have : 0 ≤ C := by positivity
    exact mul_nonneg (by positivity) (pow_nonneg hD0 _)
  have hp2 : 2 * p ≠ 0 := by omega
  rcases hβ0.eq_or_lt with hβz | hβ
  · -- all off-diagonal coefficients vanish
    have hz : ∀ ω, (∑ i, ∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))) = 0 := by
      intro ω
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rfl
      · have h := hBle i j hij
        rw [← hβz] at h
        have : B i j = 0 := norm_le_zero_iff.mp h
        simp [this]
    simp only [hz, norm_zero, zero_pow hp2, integral_zero]
    exact hRHS0
  -- real and imaginary parts
  have hab : ∀ i, MQBdd μ (a i) := fun i => ⟨q⁻¹, hbd i⟩
  have hintR : ∀ b : Fin n → Fin n → ℝ, Integrable (fun ω =>
      (∑ i, ∑ j, (if i = j then 0 else b i j * a i ω * a j ω)) ^ (2 * p)) μ := by
    intro b
    refine MQBdd.integrable ?_ ((MQBdd.sum _ fun i _ => MQBdd.sum _ fun j _ => ?_).pow _)
    · refine (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_).pow_const _
      by_cases h : i = j
      · simp [h]
      · simp only [h, ite_false]
        fun_prop
    · rcases eq_or_ne i j with h | h
      · simpa [h] using MQBdd.const (μ := μ) 0
      · simpa [h] using ((MQBdd.const (b i j)).mul (hab i)).mul (hab j)
  have hlin' : ∀ A : Fin n → ℂ, ∫ ω, ‖∑ i, A i * a i ω‖ ^ (2 * p) ∂μ ≤
      (C1 * p) ^ (2 * p) * ((⨆ i, ‖A i‖) / q + Real.sqrt (K / N * ∑ i, ‖A i‖ ^ 2)) ^ (2 * p) :=
    fun A => hlin μ n a hind hmeas h0 q (K / N) hq hbd hvar A p hp
  have hσsq : σ ^ 2 = ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, if i = j then 0 else ‖B i j‖ ^ 2 := by
    refine Real.sq_sqrt (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => ?_))
    split_ifs <;> positivity
  have hpart : ∀ f : ℂ → ℝ, (∀ z, |f z| ≤ ‖z‖) →
      ∫ ω, (∑ i, ∑ j, (if i = j then 0 else f (B i j) * a i ω * a j ω)) ^ (2 * p) ∂μ ≤
        (64 * C1 * (K + 1) * p ^ 2 * (β / q + σ)) ^ (2 * p) := by
    intro f hf
    refine momentsQuadratic_real hK hind hmeas h0 hq hq1 hnN hbd hvar hp hC1 hlin'
      (fun i j => f (B i j)) hβ (fun i j hij => (hf _).trans (hBle i j hij)) hσ0 ?_
    rw [hσsq]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => ?_) (by positivity)
    split_ifs
    · exact le_rfl
    · rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf _) 2
  have hre := hpart Complex.re Complex.abs_re_le_norm
  have him := hpart Complex.im Complex.abs_im_le_norm
  have hpt : ∀ ω, ‖∑ i, ∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))‖ ^ (2 * p)
      ≤ 2 ^ p * ((∑ i, ∑ j, (if i = j then 0 else (B i j).re * a i ω * a j ω)) ^ (2 * p) +
        (∑ i, ∑ j, (if i = j then 0 else (B i j).im * a i ω * a j ω)) ^ (2 * p)) := by
    intro ω
    set Q := ∑ i, ∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ)) with hQ
    have hQre : Q.re = ∑ i, ∑ j, (if i = j then 0 else (B i j).re * a i ω * a j ω) := by
      simp only [hQ, Complex.re_sum, apply_ite Complex.re, Complex.zero_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
      simp
    have hQim : Q.im = ∑ i, ∑ j, (if i = j then 0 else (B i j).im * a i ω * a j ω) := by
      simp only [hQ, Complex.im_sum, apply_ite Complex.im, Complex.zero_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      simp
    have hn : ‖Q‖ ^ 2 = Q.re ^ 2 + Q.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [pow_mul, hn, ← hQre, ← hQim]
    exact sq_add_sq_pow_le _ _ p
  have hgi : Integrable (fun ω => 2 ^ p *
      ((∑ i, ∑ j, (if i = j then 0 else (B i j).re * a i ω * a j ω)) ^ (2 * p) +
        (∑ i, ∑ j, (if i = j then 0 else (B i j).im * a i ω * a j ω)) ^ (2 * p))) μ :=
    ((hintR _).add (hintR _)).const_mul _
  set T : ℝ := 64 * C1 * (K + 1) * p ^ 2 * (β / q + σ) with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hC1le : 1 ≤ C := by
    have : 0 ≤ 128 * C1 * (K + 1) := by positivity
    linarith
  have hfin : 2 ^ p * (T ^ (2 * p) + T ^ (2 * p)) ≤ (C * p) ^ (4 * p) * (β / q + σ) ^ (2 * p) := by
    have h1 : 2 ^ p * (T ^ (2 * p) + T ^ (2 * p)) ≤ (2 * T) ^ (2 * p) := by
      have h2p : (2 : ℝ) ≤ 2 ^ p := le_self_pow₀ (by norm_num) (by omega)
      have e : (2 * T) ^ (2 * p) = 2 ^ p * 2 ^ p * T ^ (2 * p) := by
        rw [mul_pow, pow_mul, ← mul_pow]; norm_num
      rw [e]
      have : 0 ≤ T ^ (2 * p) := pow_nonneg hT0 _
      calc 2 ^ p * (T ^ (2 * p) + T ^ (2 * p)) = 2 ^ p * 2 * T ^ (2 * p) := by ring
        _ ≤ 2 ^ p * 2 ^ p * T ^ (2 * p) := by gcongr
    have h2 : 2 * T ≤ (C * p) ^ 2 * (β / q + σ) := by
      have hc : 128 * C1 * (K + 1) ≤ C ^ 2 := by
        have : C ≤ C ^ 2 := by nlinarith
        linarith
      calc 2 * T = (128 * C1 * (K + 1)) * (p ^ 2 * (β / q + σ)) := by rw [hTdef]; ring
        _ ≤ C ^ 2 * (p ^ 2 * (β / q + σ)) := by gcongr
        _ = (C * p) ^ 2 * (β / q + σ) := by ring
    calc 2 ^ p * (T ^ (2 * p) + T ^ (2 * p)) ≤ (2 * T) ^ (2 * p) := h1
      _ ≤ ((C * p) ^ 2 * (β / q + σ)) ^ (2 * p) := pow_le_pow_left₀ (by positivity) h2 _
      _ = (C * p) ^ (4 * p) * (β / q + σ) ^ (2 * p) := by
          rw [mul_pow, ← pow_mul]; ring_nf
  calc ∫ ω, ‖∑ i, ∑ j, (if i = j then 0 else B i j * (a i ω : ℂ) * (a j ω : ℂ))‖ ^ (2 * p) ∂μ
      ≤ ∫ ω, 2 ^ p * ((∑ i, ∑ j, (if i = j then 0 else (B i j).re * a i ω * a j ω)) ^ (2 * p) +
        (∑ i, ∑ j, (if i = j then 0 else (B i j).im * a i ω * a j ω)) ^ (2 * p)) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) hgi
          (Eventually.of_forall hpt)
    _ = 2 ^ p * (∫ ω, (∑ i, ∑ j, (if i = j then 0 else (B i j).re * a i ω * a j ω)) ^ (2 * p) ∂μ
        + ∫ ω, (∑ i, ∑ j, (if i = j then 0 else (B i j).im * a i ω * a j ω)) ^ (2 * p) ∂μ) := by
        rw [integral_const_mul, integral_add (hintR _) (hintR _)]
    _ ≤ 2 ^ p * (T ^ (2 * p) + T ^ (2 * p)) := by gcongr
    _ ≤ (C * p) ^ (4 * p) * (β / q + σ) ^ (2 * p) := hfin


/-! ### Checks -/

/-- The fair coin law on `Bool`. -/
private def momentsQuadraticCoin : Measure Bool := (2 : ENNReal)⁻¹ • Measure.count

private instance : IsProbabilityMeasure momentsQuadraticCoin := by
  constructor
  simp only [momentsQuadraticCoin, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The Rademacher sign attached to a coin. -/
private def momentsQuadraticSign (b : Bool) : ℝ := if b then 1 else -1

/-- Two independent Rademacher variables on `Fin 2 → Bool` with the product law. -/
private def momentsQuadraticRad : Fin 2 → (Fin 2 → Bool) → ℝ :=
  fun i ω => momentsQuadraticSign (ω i)

private lemma momentsQuadratic_integral_coin (f : Bool → ℝ) :
    ∫ b, f b ∂momentsQuadraticCoin = (f true + f false) / 2 := by
  rw [momentsQuadraticCoin, integral_smul_measure, integral_count]
  simp
  ring

private lemma momentsQuadratic_integral_rad (i : Fin 2) (f : ℝ → ℝ) :
    ∫ ω, f (momentsQuadraticRad i ω) ∂(Measure.pi fun _ => momentsQuadraticCoin) =
      (f 1 + f (-1)) / 2 := by
  have := integral_comp_eval (μ := fun _ : Fin 2 => momentsQuadraticCoin) (i := i)
    (f := fun b => f (momentsQuadraticSign b)) (Measurable.of_discrete).aestronglyMeasurable
  simp only [momentsQuadraticRad]
  rw [this, momentsQuadratic_integral_coin]
  simp [momentsQuadraticSign]

/-- Nondegenerate instance: two independent Rademacher signs (`n = N = 2`), `K = 2`, `q = 1`
(the bounds `|a i| ≤ q⁻¹` and `E a i ^ 2 ≤ K / N` are both attained), the off-diagonal matrix
`![![0, 1], ![1, 0]]`, moment order `2 * 2`. -/
example : ∃ C > 0,
    ∫ ω, ‖∑ i, ∑ j, (if i = j then 0 else ![![(0 : ℂ), 1], ![1, 0]] i j *
        momentsQuadraticRad i ω * momentsQuadraticRad j ω)‖ ^ (2 * 2)
        ∂(Measure.pi fun _ => momentsQuadraticCoin) ≤
      (C * (2 : ℕ)) ^ (4 * 2) * ((⨆ i, ⨆ j, if i = j then 0 else
        ‖![![(0 : ℂ), 1], ![1, 0]] i j‖) / 1 + Real.sqrt ((((2 : ℕ) : ℝ) ^ 2)⁻¹ *
          ∑ i, ∑ j, if i = j then 0 else ‖![![(0 : ℂ), 1], ![1, 0]] i j‖ ^ 2)) ^ (2 * 2) := by
  obtain ⟨C, hC, h⟩ := moment_quadratic_le 2 two_pos
  refine ⟨C, hC, h (Measure.pi fun _ => momentsQuadraticCoin) 2 2 momentsQuadraticRad ?_ ?_ ?_
    1 one_pos le_rfl le_rfl ?_ ?_ _ 2 (by norm_num)⟩
  · exact iIndepFun_pi (X := fun _ => momentsQuadraticSign)
      (fun _ => (Measurable.of_discrete).aemeasurable)
  · intro i; exact (Measurable.of_discrete).comp (measurable_pi_apply i)
  · intro i
    have := momentsQuadratic_integral_rad i id
    simpa using this
  · intro i
    refine Eventually.of_forall fun ω => ?_
    simp only [momentsQuadraticRad, momentsQuadraticSign, inv_one]
    split_ifs <;> norm_num
  · intro i
    have := momentsQuadratic_integral_rad i (fun x => x ^ 2)
    rw [this]; norm_num

#print axioms moment_quadratic_le

end WEdgeNS
