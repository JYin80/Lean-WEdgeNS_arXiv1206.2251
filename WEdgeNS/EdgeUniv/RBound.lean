import WEdgeNS.EdgeUniv.Apriori
import WEdgeNS.Comparison.Telescope
import WEdgeNS.Resolvent.Expansion
import WEdgeNS.Model.HighProbCalc

/-!
# The resolvent with one entry removed
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-! ### The size of the entries of `H_γ` -/

/-- The index type `Fin N ⊕ OffDiag N` of the entries has at most `N * N` elements. -/
private lemma rbound_card_le (N : ℕ) : Fintype.card (Fin N ⊕ OffDiag N) ≤ N * N := by
  have hinj : Function.Injective
      (Sum.elim (fun i : Fin N => (i, i)) (fun p : OffDiag N => p.1)) := by
    rintro (i | p) (j | q) h
    · simp only [Sum.elim_inl, Prod.mk.injEq] at h
      rw [h.1]
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      have := q.2
      simp only at h1 h2
      omega
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      have := p.2
      simp only at h1 h2
      omega
    · simp only [Sum.elim_inr] at h
      rw [Subtype.ext h]
  simpa using Fintype.card_le_of_injective _ hinj

/-- The marginal of `L.law` at the entry `e` is the law of that entry. -/
private lemma rbound_law_entryVal {N : ℕ} {L : EntryLaws N} (hL : L.IsProb)
    (e : Fin N ⊕ OffDiag N) {A : Set ℝ} (hA : MeasurableSet A) :
    L.law {ω | entryVal e ω ∈ A} = Sum.elim L.diag L.off e A := by
  have h1 := hL.diag
  have h2 := hL.off
  rcases e with i | p
  · have hset : {ω : Entries N | entryVal (Sum.inl i) ω ∈ A} =
        (Function.eval i ⁻¹' A) ×ˢ (Set.univ : Set (OffDiag N → ℝ)) := by
      ext ω
      simp [entryVal]
    rw [hset]
    change ((Measure.pi L.diag).prod (Measure.pi L.off)) _ = _
    rw [Measure.prod_prod, measure_univ, mul_one,
      (measurePreserving_eval L.diag i).measure_preimage hA.nullMeasurableSet]
    rfl
  · have hset : {ω : Entries N | entryVal (Sum.inr p) ω ∈ A} =
        (Set.univ : Set (Fin N → ℝ)) ×ˢ (Function.eval p ⁻¹' A) := by
      ext ω
      simp [entryVal]
    rw [hset]
    change ((Measure.pi L.diag).prod (Measure.pi L.off)) _ = _
    rw [Measure.prod_prod, measure_univ, one_mul,
      (measurePreserving_eval L.off p).measure_preimage hA.nullMeasurableSet]
    rfl

/-- Definition 2.4 bounds every coordinate: `P(q⁻¹ < |h_e|) ≤ exp(-N^c)`. -/
private lemma rbound_tail_le {N : ℕ} {L : EntryLaws N} (hL : L.IsProb) {q c : ℝ}
    (h : L.BoundedSupport q c) (e : Fin N ⊕ OffDiag N) :
    L.law {ω | q⁻¹ < |entryVal e ω|} ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) ^ c)) := by
  have hA : MeasurableSet {x : ℝ | q⁻¹ < |x|} :=
    measurableSet_lt measurable_const measurable_id.abs
  have := rbound_law_entryVal hL e hA
  simp only [Set.mem_ofPred_eq] at this
  rw [this]
  rcases e with i | p
  · exact h.1 i
  · exact h.2 p

/-- A smaller threshold `q⁻¹ ≤ q'⁻¹` keeps Definition 2.4. -/
private lemma rbound_boundedSupport_mono {N : ℕ} {L : EntryLaws N} {q q' c : ℝ}
    (hqq : q⁻¹ ≤ q'⁻¹) (h : L.BoundedSupport q c) : L.BoundedSupport q' c :=
  have hsub : {x : ℝ | q'⁻¹ < |x|} ⊆ {x : ℝ | q⁻¹ < |x|} := fun _ hx => lt_of_le_of_lt hqq hx
  ⟨fun i => (measure_mono hsub).trans (h.1 i), fun p => (measure_mono hsub).trans (h.2 p)⟩

/-- The entries of every `H_γ` are bounded by `N^ε q⁻¹`, `q = N^{φs}`, with high probability
((3.27), [16] (6.41)): almost surely for a law of Lemma 3.5, from the Gaussian tail for the GOE. -/
theorem entryVal_le_largeQInterp {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → HighProbOn 1
      (fun N L => ∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N))
      (fun N _ => {ω | ∀ e : Fin N ⊕ OffDiag N, |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs)}) := by
  intro ε hε hε'
  have _ := hC0
  have _ := hφs
  have h0 : 0 < 1 / 2 - ε / 2 := by linarith
  have h1 : 1 / 2 - ε / 2 < 1 / 2 := by linarith
  obtain ⟨c, hc, Ng, hg⟩ := goeLaws_boundedSupport h0 h1
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (phi_rpow_le_rpow 1 hc)
  refine HighProbOn.mono (HighProbOn.iInter (K := 2) (ι := fun N => Fin N ⊕ OffDiag N)
    (Ω := fun N e _ => {ω : Entries N | |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs)})
    (fun N => ?_) ⟨1, one_pos, 1, one_pos, max (max Ng N1) 1, fun N hN e L hL => ?_⟩)
    (fun N L ω hω => Set.mem_iInter.1 hω)
  · calc (Fintype.card (Fin N ⊕ OffDiag N) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by
          exact_mod_cast rbound_card_le N
      _ = (N : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; push_cast; ring
  · obtain ⟨Lv, γ, hv, rfl⟩ := hL
    have hNg : Ng ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    have hN1' : N1 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    have hNpos : 1 ≤ N := (le_max_right _ _).trans hN
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have hN0 : (0 : ℝ) < N := by linarith
    set q : ℝ := ((N : ℝ) ^ (ε - φs))⁻¹ with hq
    have hqinv : q⁻¹ = (N : ℝ) ^ (ε - φs) := inv_inv _
    have hLv : Lv.BoundedSupport q c := by
      have hle : ((N : ℝ) ^ φs)⁻¹ ≤ q⁻¹ := by
        rw [hqinv, ← Real.rpow_neg hN0.le]
        exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
      have hbs : Lv.BoundedSupportAS q :=
        ⟨fun i => measure_mono_null (fun x hx => lt_of_le_of_lt hle hx) (hv.2.1 i),
          fun p => measure_mono_null (fun x hx => lt_of_le_of_lt hle hx) (hv.2.2 p)⟩
      exact hbs.boundedSupport c
    have hGoe : (goeLaws N).BoundedSupport q c := by
      refine rbound_boundedSupport_mono ?_ (hg N hNg)
      rw [hqinv, ← Real.rpow_neg hN0.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
    have hint := interp_boundedSupport (Φ := lexPos N) (γ := γ) hLv hGoe
    have hprob : (interp (lexPos N) γ Lv (goeLaws N)).IsProb :=
      (interp_isGenWigner hv.1 (goeLaws_isGenWigner N)).isProb
    have hset : ({ω : Entries N | |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs)})ᶜ =
        {ω | q⁻¹ < |entryVal e ω|} := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, hqinv]
    rw [hset]
    refine (rbound_tail_le hprob hint e).trans (ENNReal.ofReal_le_ofReal ?_)
    have hφ : phi N ^ (1 : ℝ) ≤ (N : ℝ) ^ c := hN1 N hN1'
    have hex : Real.exp (-(N : ℝ) ^ c) ≤ Real.exp (-1 * phi N ^ (1 : ℝ)) :=
      Real.exp_le_exp.2 (by linarith)
    refine hex.trans (le_mul_of_one_le_left (Real.exp_pos _).le ?_)
    rw [pow_one]
    exact hN1r

/-! ### The expansion (3.28) with one entry removed -/

/-- The absolute row sums of the complex matrix `M` are at most `a`. -/
private def RowBd {N : ℕ} (a : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ k, ∑ j, ‖M k j‖ ≤ a

private lemma rowBd_one {N : ℕ} : RowBd (N := N) 1 1 := by
  intro k
  have h : ∀ j, ‖(1 : Matrix (Fin N) (Fin N) ℂ) k j‖ = if k = j then 1 else 0 := by
    intro j
    by_cases hj : k = j <;> simp [Matrix.one_apply, hj]
  simp_rw [h]
  simp

private lemma rowBd_mul {N : ℕ} {a b : ℝ} {A B : Matrix (Fin N) (Fin N) ℂ} (hb : 0 ≤ b)
    (hA : RowBd a A) (hB : RowBd b B) : RowBd (a * b) (A * B) := by
  intro k
  calc ∑ j, ‖(A * B) k j‖ ≤ ∑ j, ∑ i, ‖A k i‖ * ‖B i j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_mul _ _).le)
    _ = ∑ i, ‖A k i‖ * ∑ j, ‖B i j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ‖A k i‖ * b := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hB i) (norm_nonneg _)
    _ = (∑ i, ‖A k i‖) * b := (Finset.sum_mul _ _ _).symm
    _ ≤ a * b := mul_le_mul_of_nonneg_right (hA k) hb

private lemma rowBd_pow {N : ℕ} {a : ℝ} {A : Matrix (Fin N) (Fin N) ℂ} (ha : 0 ≤ a)
    (hA : RowBd a A) (n : ℕ) : RowBd (a ^ n) (A ^ n) := by
  induction n with
  | zero => simpa using rowBd_one
  | succ n ih => rw [pow_succ, pow_succ]; exact rowBd_mul ha ih hA

/-- A row-sum bound times an entrywise bound bounds the entries of the product. -/
private lemma norm_mul_apply_le {N : ℕ} {a c : ℝ} {A M : Matrix (Fin N) (Fin N) ℂ} (hc : 0 ≤ c)
    (hA : RowBd a A) (hM : ∀ i j, ‖M i j‖ ≤ c) (k l : Fin N) : ‖(A * M) k l‖ ≤ a * c := by
  rw [Matrix.mul_apply]
  calc ‖∑ j, A k j * M j l‖ ≤ ∑ j, ‖A k j‖ * ‖M j l‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)
    _ ≤ ∑ j, ‖A k j‖ * c := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hM j l) (norm_nonneg _)
    _ = (∑ j, ‖A k j‖) * c := (Finset.sum_mul _ _ _).symm
    _ ≤ a * c := mul_le_mul_of_nonneg_right (hA k) hc

private lemma entryPairs_length_le {N : ℕ} (e : Fin N ⊕ OffDiag N) :
    (entryPairs e).length ≤ 2 := by
  rcases e with a | p <;> simp [entryPairs]

/-- `V = v I_e` has at most two nonzero entries, each of modulus `|v|`. -/
private lemma sum_norm_entryMat {N : ℕ} (e : Fin N ⊕ OffDiag N) (v : ℝ) :
    ∑ i, ∑ j, ‖((v • entryMat e).map (fun x : ℝ => (x : ℂ))) i j‖ ≤ 2 * |v| := by
  have hterm : ∀ i j : Fin N, ‖((v • entryMat e).map (fun x : ℝ => (x : ℂ))) i j‖ =
      |v| * (if (i, j) ∈ entryPairs e then 1 else 0) := by
    intro i j
    by_cases h : (i, j) ∈ entryPairs e <;> simp [entryMat, h]
  simp_rw [hterm, ← Finset.mul_sum]
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg v)
  rw [← Fintype.sum_prod_type' (fun i j => if (i, j) ∈ entryPairs e then (1 : ℝ) else 0),
    Finset.sum_boole]
  have hsub : Finset.univ.filter (fun x : Fin N × Fin N => x ∈ entryPairs e) ⊆
      (entryPairs e).toFinset := fun x hx => List.mem_toFinset.2 (Finset.mem_filter.1 hx).2
  have h1 := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  have h2 := h1.trans (entryPairs_length_le e)
  exact_mod_cast h2

/-- If all entries of `S` have modulus at most `2`, the absolute row sums of `S V` are at most
`4 |v|`. -/
private lemma rowBd_mul_entryMat {N : ℕ} (e : Fin N ⊕ OffDiag N) (v : ℝ)
    {S : Matrix (Fin N) (Fin N) ℂ} (hS : ∀ i j, ‖S i j‖ ≤ 2) :
    RowBd (4 * |v|) (S * (v • entryMat e).map (fun x : ℝ => (x : ℂ))) := by
  intro k
  set V := (v • entryMat e).map (fun x : ℝ => (x : ℂ)) with hV
  calc ∑ j, ‖(S * V) k j‖ ≤ ∑ j, ∑ i, 2 * ‖V i j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hS k i) (norm_nonneg _)))
    _ = 2 * ∑ i, ∑ j, ‖V i j‖ := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
    _ ≤ 2 * (2 * |v|) := mul_le_mul_of_nonneg_left (sum_norm_entryMat e v) (by norm_num)
    _ = 4 * |v| := by ring

/-- (3.28) with `n = 4` for `R = G(Q)`, `S = G(Q + V)`, `V = v I_e`: if `|v| ≤ B` and all entries of
`S` have modulus at most `2`, then `|R_kl - S_kl| ≤ 2 Σ_{m=1}^4 (4B)^m + (4B)^5 / η`. -/
private lemma norm_resolventC_zeroEntry_sub_le_aux {N : ℕ} (e : Fin N ⊕ OffDiag N)
    (ω : Entries N) {z : ℂ} (hz : 0 < z.im) {B : ℝ} (hv : |entryVal e ω| ≤ B)
    (hS : ∀ i j, ‖resolventC (symOfEntries ω) z i j‖ ≤ 2) (k l : Fin N) :
    ‖resolventC (symOfEntries (zeroEntry e ω)) z k l - resolventC (symOfEntries ω) z k l‖ ≤
      2 * (4 * B + (4 * B) ^ 2 + (4 * B) ^ 3 + (4 * B) ^ 4) + (4 * B) ^ 5 * (1 / z.im) := by
  have hH := symOfEntries_isHermitian ω
  have hQ := symOfEntries_isHermitian (zeroEntry e ω)
  have hdec := symOfEntries_eq_zeroEntry_add e ω
  set Vr : Matrix (Fin N) (Fin N) ℝ := entryVal e ω • entryMat e with hVr
  have hVrH : (-Vr).IsHermitian := by
    have : -Vr = symOfEntries (zeroEntry e ω) - symOfEntries ω := by
      rw [hdec]; abel
    rw [this]
    exact hQ.sub hH
  have hHQ : symOfEntries ω + -Vr = symOfEntries (zeroEntry e ω) := by
    rw [hdec]; abel
  have hexp := resolventC_expansion_right hH hVrH hz 4
  rw [hHQ] at hexp
  set S := resolventC (symOfEntries ω) z with hSdef
  set R := resolventC (symOfEntries (zeroEntry e ω)) z with hRdef
  set M : Matrix (Fin N) (Fin N) ℂ := S * Vr.map (fun x : ℝ => (x : ℂ)) with hM
  have hneg : -(S * (-Vr).map (fun x : ℝ => (x : ℂ))) = M := by
    have : (-Vr).map (fun x : ℝ => (x : ℂ)) = -(Vr.map (fun x : ℝ => (x : ℂ))) := by
      ext i j; simp
    rw [this, Matrix.mul_neg, neg_neg]
  rw [hneg] at hexp
  have hRS : R - S = ∑ i ∈ Finset.range 4, M ^ (i + 1) * S + M ^ 5 * R := by
    have h := hexp
    rw [Finset.sum_range_succ'] at h
    simp only [pow_zero, Matrix.one_mul, Nat.reduceAdd] at h
    refine sub_eq_of_eq_add ?_
    calc R = _ := h
      _ = _ := by abel
  have hMb : RowBd (4 * |entryVal e ω|) M := rowBd_mul_entryMat e (entryVal e ω) hS
  have hB0 : 0 ≤ 4 * |entryVal e ω| := by positivity
  have hx : 4 * |entryVal e ω| ≤ 4 * B := by linarith
  have hx0 : 0 ≤ 4 * B := hB0.trans hx
  have hpow : ∀ n : ℕ, RowBd ((4 * B) ^ n) (M ^ n) := fun n =>
    fun k => (rowBd_pow hB0 hMb n k).trans (pow_le_pow_left₀ hB0 hx n)
  have hRb : ∀ i j, ‖R i j‖ ≤ 1 / z.im := fun i j => norm_resolventC_apply_le hQ hz i j
  have hz1 : 0 ≤ 1 / z.im := by positivity
  have hterm : ∀ i : ℕ, ‖(M ^ (i + 1) * S) k l‖ ≤ (4 * B) ^ (i + 1) * 2 := fun i =>
    norm_mul_apply_le (by norm_num) (hpow (i + 1)) hS k l
  have hrem : ‖(M ^ 5 * R) k l‖ ≤ (4 * B) ^ 5 * (1 / z.im) :=
    norm_mul_apply_le hz1 (hpow 5) hRb k l
  have hentry : R k l - S k l = ∑ i ∈ Finset.range 4, (M ^ (i + 1) * S) k l + (M ^ 5 * R) k l := by
    have := congrFun (congrFun hRS k) l
    simpa [Matrix.sum_apply] using this
  rw [hentry]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) hrem)
  calc ∑ i ∈ Finset.range 4, ‖(M ^ (i + 1) * S) k l‖ ≤
        ∑ i ∈ Finset.range 4, (4 * B) ^ (i + 1) * 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * (4 * B + (4 * B) ^ 2 + (4 * B) ^ 3 + (4 * B) ^ 4) := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero]
        ring

/-- The exponent bookkeeping of (3.27): for `N^ε ≥ 3`, `N^{2ε+φs-1/3} ≥ 96`, `N^{11/30} ≥ 3072`,
the terms `N^{-1/3+2ε}`, `2 Σ_{m=1}^4 (4B)^m` and `(4B)^5 η⁻¹` with `B = N^{ε-φs}` and
`η = N^{-2/3-ε}` add up to at most `N^{-1/3+3ε}`. -/
private lemma rbound_arith {N : ℕ} {ε φs : ℝ} (hN : 2 ≤ N) (hε' : ε < 1 / 10)
    (hφs : 1 / 3 < φs) (h1 : 3 ≤ (N : ℝ) ^ ε)
    (h2 : 96 ≤ (N : ℝ) ^ (2 * ε + (φs - 1 / 3))) (h3 : 3072 ≤ (N : ℝ) ^ ((11 : ℝ) / 30)) :
    (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) +
      (2 * (4 * (N : ℝ) ^ (ε - φs) + (4 * (N : ℝ) ^ (ε - φs)) ^ 2 +
          (4 * (N : ℝ) ^ (ε - φs)) ^ 3 + (4 * (N : ℝ) ^ (ε - φs)) ^ 4) +
        (4 * (N : ℝ) ^ (ε - φs)) ^ 5 * (1 / (N : ℝ) ^ (-(2 : ℝ) / 3 - ε))) ≤
      (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := by
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hn0 : (0 : ℝ) < N := by linarith
  set n : ℝ := (N : ℝ) with hn
  set B : ℝ := n ^ (ε - φs) with hB
  set P₀ : ℝ := n ^ (-(1 : ℝ) / 3 + 2 * ε) with hP₀
  set P : ℝ := n ^ (-(1 : ℝ) / 3 + 3 * ε) with hP
  have hB0 : 0 ≤ B := (Real.rpow_pos_of_pos hn0 _).le
  have hP₀0 : 0 < P₀ := Real.rpow_pos_of_pos hn0 _
  have hP1 : P ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1.le (by linarith)
  have hPP₀ : P = P₀ * n ^ ε := by
    rw [hP, hP₀, ← Real.rpow_add hn0]
    congr 1
    ring
  have hP₀P : 3 * P₀ ≤ P := by
    rw [hPP₀]
    nlinarith
  have hBP : 96 * B ≤ P := by
    have e : B * n ^ (2 * ε + (φs - 1 / 3)) = P := by
      rw [hB, hP, ← Real.rpow_add hn0]
      congr 1
      ring
    nlinarith
  have hx1 : 4 * B ≤ 1 := by linarith
  have hx0 : 0 ≤ 4 * B := by positivity
  have hsum : 4 * B + (4 * B) ^ 2 + (4 * B) ^ 3 + (4 * B) ^ 4 ≤ 4 * (4 * B) := by
    have a2 := pow_le_of_le_one hx0 hx1 (by norm_num : (2 : ℕ) ≠ 0)
    have a3 := pow_le_of_le_one hx0 hx1 (by norm_num : (3 : ℕ) ≠ 0)
    have a4 := pow_le_of_le_one hx0 hx1 (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  have hη : 1 / n ^ (-(2 : ℝ) / 3 - ε) = n ^ ((2 : ℝ) / 3 + ε) := by
    rw [one_div, ← Real.rpow_neg hn0.le]
    congr 1
    ring
  have hB5 : B ^ 5 = n ^ (5 * (ε - φs)) := by
    rw [hB, ← Real.rpow_mul_natCast hn0.le]
    congr 1
    push_cast
    ring
  set T : ℝ := n ^ (5 * (ε - φs) + ((2 : ℝ) / 3 + ε)) with hT
  have hT0 : 0 ≤ T := (Real.rpow_pos_of_pos hn0 _).le
  have hrem : (4 * B) ^ 5 * (1 / n ^ (-(2 : ℝ) / 3 - ε)) = 1024 * T := by
    rw [hη, mul_pow, hB5, hT, Real.rpow_add hn0 (5 * (ε - φs)) ((2 : ℝ) / 3 + ε)]
    ring
  have hPT : P = T * n ^ (5 * φs - 1 - 3 * ε) := by
    rw [hP, hT, ← Real.rpow_add hn0]
    congr 1
    ring
  have hexp : n ^ ((11 : ℝ) / 30) ≤ n ^ (5 * φs - 1 - 3 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
  have hTP : 3072 * T ≤ P := by
    rw [hPT]
    exact mul_le_mul_of_nonneg_left (h3.trans hexp) hT0 |>.trans_eq' (by ring)
  rw [hrem]
  linarith

/-- (3.27) from the expansion (3.28) (`resolventC_expansion_right` with `n = 4`): on
`aprioriEvent N ε`, if `|v_e| ≤ N^ε q⁻¹`, the resolvent `R` of `Q` (the entry `e` set to zero)
satisfies `|R_kl - δ_kl m_sc| ≤ N^{-1/3+3ε}` for all `E ∈ I_ε` and all `k, l`. -/
theorem norm_resolventC_zeroEntry_sub_le {φs : ℝ} (hφs : 1 / 3 < φs) (hφs' : φs ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ ω : Entries N,
      ∀ e : Fin N ⊕ OffDiag N, ω ∈ aprioriEvent N ε → |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs) →
      ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) → ∀ k l,
        ‖resolventC (symOfEntries (zeroEntry e ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
            (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
          (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε) := by
  intro ε hε hε'
  have _ := hφs'
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 <|
    (eventually_ge_atTop 2).and <|
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3).and <|
    (((tendsto_rpow_atTop (by linarith : 0 < 2 * ε + (φs - 1 / 3))).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 96).and <|
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 11 / 30)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 3072
  refine ⟨N0, fun N hN ω e hω hv E hE k l => ?_⟩
  obtain ⟨hN2, h1, h2, h3⟩ := hN0 N hN
  replace h1 : 3 ≤ (N : ℝ) ^ ε := h1
  replace h2 : 96 ≤ (N : ℝ) ^ (2 * ε + (φs - 1 / 3)) := h2
  replace h3 : 3072 ≤ (N : ℝ) ^ ((11 : ℝ) / 30) := h3
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hn0 : (0 : ℝ) < N := by linarith
  have hη0 : 0 < (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := Real.rpow_pos_of_pos hn0 _
  have hP1 : (N : ℝ) ^ (-(1 : ℝ) / 3 + 2 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1.le (by linarith)
  have hS : ∀ i j, ‖resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ i j‖ ≤ 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact (aprioriEvent_bounds (by omega) hε hε' hω).1 E hE i
    · have h := hω E hE i j
      simp only [hij, ↓reduceIte, sub_zero] at h
      linarith
  have haux := norm_resolventC_zeroEntry_sub_le_aux e ω
    (z := ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩) hη0 hv hS k l
  have hz : (⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ : ℂ).im = (N : ℝ) ^ (-(2 : ℝ) / 3 - ε) := rfl
  rw [hz] at haux
  have hev := hω E hE k l
  have harith := rbound_arith hN2 hε' hφs h1 h2 h3
  calc _ = ‖(resolventC (symOfEntries (zeroEntry e ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l) +
        (resolventC (symOfEntries ω) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
          (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add haux hev)
    _ ≤ _ := by linarith

/-- (3.27) with high probability for every `H_γ`, simultaneously for all entries `e`. -/
theorem apriori_zeroEntry_largeQInterp {C0 φs : ℝ} (hC0 : 0 ≤ C0) (hφs : 1 / 3 < φs)
    (hφs' : φs ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 10 → HighProbOn 1
      (fun N L => ∃ Lv γ, LargeQClass C0 φs N Lv ∧ L = interp (lexPos N) γ Lv (goeLaws N))
      (fun N _ => {ω | ∀ e : Fin N ⊕ OffDiag N, ∀ E : ℝ, |E - 2| ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + ε) →
        ∀ k l, ‖resolventC (symOfEntries (zeroEntry e ω)) ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ k l -
            (if k = l then msc ⟨E, (N : ℝ) ^ (-(2 : ℝ) / 3 - ε)⟩ else 0)‖ ≤
          (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * ε)}) := by
  intro ε hε hε'
  obtain ⟨N0, hN0⟩ := norm_resolventC_zeroEntry_sub_le hφs hφs' ε hε hε'
  refine HighProbOn.mono_eventually ((apriori_largeQInterp_event hC0 hφs hφs' ε hε hε').inter
    (entryVal_le_largeQInterp hC0 hφs hφs' ε hε hε')) (fun _ _ h => h) ⟨N0, ?_⟩
  intro N hN L _ ω hω e E hE k l
  exact hN0 N hN ω e hω.1 (hω.2 e) E hE k l

/-- The event `Ω` of [16] (6.55) for the replacement of the entry `e`: (3.26) and
`|v_e| ≤ N^ε q⁻¹` ((3.27) then holds on it, `norm_resolventC_zeroEntry_sub_le`). -/
def swapEvent (N : ℕ) (ε φs : ℝ) (e : Fin N ⊕ OffDiag N) : Set (Entries N) :=
  aprioriEvent N ε ∩ {ω | |entryVal e ω| ≤ (N : ℝ) ^ (ε - φs)}

/-! ### Checks -/

/-- For the GOE (`γ = 0`, Rademacher laws as `Lv`) at `(C0, φs) = (1, 2/5)`: for all large `N`
there is one `ω` with `ω ∈ swapEvent N ε (2/5) e` for every entry `e`; the complement of the
intersection of the two high-probability events has probability at most `ε_N → 0`, while the whole
space has probability `1`. -/
private lemma swapEvent_nonempty {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) :
    ∀ᶠ N : ℕ in atTop, ∃ ω : Entries N, ∀ e : Fin N ⊕ OffDiag N, ω ∈ swapEvent N ε (2 / 5) e := by
  obtain ⟨e, he, hev⟩ := ((apriori_largeQInterp_event (C0 := 1) (φs := 2 / 5) zero_le_one
    (by norm_num) (by norm_num) ε hε hε').inter
    (entryVal_le_largeQInterp (C0 := 1) (φs := 2 / 5) zero_le_one (by norm_num) (by norm_num) ε hε
      hε')).tendstoOneOn one_pos
  filter_upwards [hev, he.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 32] with
    N hN heN h32
  by_contra hne
  push Not at hne
  have hemp : aprioriEvent N ε ∩ {ω | ∀ e : Fin N ⊕ OffDiag N,
      |entryVal e ω| ≤ (N : ℝ) ^ (ε - 2 / 5)} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    obtain ⟨e, he⟩ := hne ω
    exact he ⟨hω.1, hω.2 e⟩
  have := EntryLaws.isProbabilityMeasure_law (goeLaws_isGenWigner N).isProb
  have h1 := hN (goeLaws N) ⟨radLaws N, 0, ⟨radLaws_isGenWigner (by omega),
    radLaws_boundedSupportAS h32⟩, (interp_lexPos_zero _ _).symm⟩
  rw [hemp, Set.compl_empty, measure_univ] at h1
  exact absurd (h1.trans_lt (ENNReal.ofReal_lt_one.mpr heN)) (lt_irrefl _)

/-- The class of `entryVal_le_largeQInterp` at `(C0, φs) = (1, 2/5)` is inhabited by the GOE
(`γ = 0`, Rademacher laws as `Lv`) for all large `N`. -/
example : ∀ᶠ N : ℕ in atTop, ∃ Lv γ, LargeQClass 1 (2 / 5) N Lv ∧
    goeLaws N = interp (lexPos N) γ Lv (goeLaws N) := by
  filter_upwards [eventually_ge_atTop 32] with N h32
  exact ⟨radLaws N, 0, ⟨radLaws_isGenWigner (by omega), radLaws_boundedSupportAS h32⟩,
    (interp_lexPos_zero _ _).symm⟩

/-- The hypotheses of `norm_resolventC_zeroEntry_sub_le` hold together at `ε = 1/20`,
`φs = 2/5`: for all large `N ≥ 2` there is an `ω` lying in `swapEvent N (1/20) (2/5) e` for every
entry `e` (a nonempty index set), and the conclusion holds for it at the centre `E = 2` of `I_ε`
and all `k, l`. -/
example : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ ∃ ω : Entries N, ∀ e : Fin N ⊕ OffDiag N,
    ω ∈ swapEvent N (1 / 20) (2 / 5) e ∧ ∀ k l,
      ‖resolventC (symOfEntries (zeroEntry e ω)) ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ k l -
          (if k = l then msc ⟨2, (N : ℝ) ^ (-(2 : ℝ) / 3 - 1 / 20)⟩ else 0)‖ ≤
        (N : ℝ) ^ (-(1 : ℝ) / 3 + 3 * (1 / 20)) := by
  obtain ⟨N0, hN0⟩ := norm_resolventC_zeroEntry_sub_le (φs := 2 / 5) (by norm_num) (by norm_num)
    (1 / 20) (by norm_num) (by norm_num)
  filter_upwards [swapEvent_nonempty (ε := 1 / 20) (by norm_num) (by norm_num),
    eventually_ge_atTop (max N0 2)] with N ⟨ω, hω⟩ hN
  refine ⟨le_trans (le_max_right _ _) hN, ω, fun e => ⟨hω e, fun k l => ?_⟩⟩
  have hr : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / 3 + 1 / 20) := by positivity
  exact hN0 N (le_trans (le_max_left _ _) hN) ω e (hω e).1 (hω e).2 2
    (by rw [sub_self, abs_zero]; exact hr) k l

#print axioms entryVal_le_largeQInterp
#print axioms norm_resolventC_zeroEntry_sub_le
#print axioms apriori_zeroEntry_largeQInterp
#print axioms swapEvent

end WEdgeNS
