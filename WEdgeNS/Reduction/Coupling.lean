import WEdgeNS.Reduction.Tail
import WEdgeNS.Model.Ensembles
import WEdgeNS.Probability.ProductSpace

/-!
# The coupling of the entries on an auxiliary product space
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

open EntryLaws

/-- Law of `x - m` for `x ∼ ν` conditioned on `|x| > T` ((4.14), centred by `m`); `δ₀` when
`ν{|x| > T} = 0`, where the conditional law is undefined. -/
def truncLargeCentered (ν : Measure ℝ) (T : ℝ) : Measure ℝ :=
  if ν {x | T < |x|} = 0 then Measure.dirac 0
  else (cond ν {x | T < |x|}).map (fun x => x - cutoffMean ν T)

/-- The selector `1(|x| > T)`; its law under `ν` is `ν_c` of (4.15)ff. -/
def largeInd (T x : ℝ) : ℝ := if T < |x| then 1 else 0

/-- The auxiliary space of (4.16): small, large and selector entries. -/
abbrev CoupleSpace (N : ℕ) := Entries N × Entries N × Entries N

/-- The law on the auxiliary space: three independent blocks, each with independent entries;
diagonal laws from `ν'`, upper laws from `ν`. -/
def coupleLaw (ν ν' : Measure ℝ) (ε : ℝ) (N : ℕ) : Measure (CoupleSpace N) :=
  (entryLaw (truncCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
      (truncCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N).prod
    ((entryLaw (truncLargeCentered ν ((N : ℝ) ^ (1 / 2 - ε)))
        (truncLargeCentered ν' ((N : ℝ) ^ (1 / 2 - ε))) N).prod
      (entryLaw (ν.map (largeInd ((N : ℝ) ^ (1 / 2 - ε))))
        (ν'.map (largeInd ((N : ℝ) ^ (1 / 2 - ε)))) N))

/-- The coupled entries `(1 - c) x^S + c x^L + m` of (4.16) (unscaled). -/
def coupleMap (m m' : ℝ) {N : ℕ} (u : CoupleSpace N) : Entries N :=
  (fun i => (1 - u.2.2.1 i) * u.1.1 i + u.2.2.1 i * u.2.1.1 i + m',
   fun p => (1 - u.2.2.2 p) * u.1.2 p + u.2.2.2 p * u.2.1.2 p + m)

theorem measurable_coupleMap (m m' : ℝ) (N : ℕ) :
    Measurable (coupleMap m m' (N := N)) := by
  unfold coupleMap
  fun_prop

/-! ### One coordinate: the laws of the small, large and selector entries -/

private lemma coupling_measurableSet_small (T : ℝ) : MeasurableSet {x : ℝ | |x| ≤ T} :=
  measurableSet_le continuous_abs.measurable measurable_const

private lemma coupling_measurableSet_large (T : ℝ) : MeasurableSet {x : ℝ | T < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

private lemma coupling_compl_small (T : ℝ) : {x : ℝ | |x| ≤ T}ᶜ = {x : ℝ | T < |x|} := by
  ext x
  simp [not_le]

/-- The selector function is measurable. -/
lemma measurable_largeInd (T : ℝ) : Measurable (largeInd T) := by
  unfold largeInd
  exact Measurable.ite (coupling_measurableSet_large T) measurable_const measurable_const

/-- The centred small-part law is a probability measure when `ν` charges `{|x| ≤ T}`. -/
lemma isProbabilityMeasure_truncCentered (ν : Measure ℝ) [IsProbabilityMeasure ν] {T : ℝ}
    (h : ν {x | |x| ≤ T} ≠ 0) : IsProbabilityMeasure (truncCentered ν T) := by
  have := cond_isProbabilityMeasure (μ := ν) h
  unfold truncCentered
  infer_instance

/-- The centred large-part law is a probability measure. -/
lemma isProbabilityMeasure_truncLargeCentered (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T : ℝ) : IsProbabilityMeasure (truncLargeCentered ν T) := by
  unfold truncLargeCentered
  split_ifs with h
  · infer_instance
  · have := cond_isProbabilityMeasure (μ := ν) h
    infer_instance

/-- A conditional law pushed forward by a measurable map has total mass at most `1`. -/
lemma map_cond_univ_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : Set ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) : ((cond ν s).map f) Set.univ ≤ 1 := by
  rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
  by_cases h : ν s = 0
  · rw [cond_eq_zero.mpr (Or.inr h)]
    simp
  · have := cond_isProbabilityMeasure (μ := ν) h
    rw [measure_univ]

/-- The centred small-part law has total mass at most `1`. -/
lemma truncCentered_univ_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ) :
    truncCentered ν T Set.univ ≤ 1 := by
  unfold truncCentered
  exact map_cond_univ_le_one ν _ _ (by fun_prop)

/-- The centred large-part law has total mass at most `1`. -/
lemma truncLargeCentered_univ_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T : ℝ) : truncLargeCentered ν T Set.univ ≤ 1 := by
  unfold truncLargeCentered
  split_ifs with h
  · simp
  · exact map_cond_univ_le_one ν _ _ (by fun_prop)

/-- The joint law of independent entries has total mass at most `1` when each entry law does. -/
lemma entryLaw_univ_le_one {L L' : Measure ℝ} (N : ℕ) (h : L Set.univ ≤ 1)
    (h' : L' Set.univ ≤ 1) : entryLaw L L' N Set.univ ≤ 1 := by
  have : IsFiniteMeasure L := ⟨lt_of_le_of_lt h ENNReal.one_lt_top⟩
  have : IsFiniteMeasure L' := ⟨lt_of_le_of_lt h' ENNReal.one_lt_top⟩
  unfold entryLaw
  have h1 : ((Measure.pi fun _ : Fin N => L') Set.univ) ≤ 1 := by
    rw [Measure.pi_univ]
    exact Finset.prod_le_one (fun i _ => h')
  have h2 : ((Measure.pi fun _ : OffDiag N => L) Set.univ) ≤ 1 := by
    rw [Measure.pi_univ]
    exact Finset.prod_le_one (fun i _ => h)
  have := Measure.prod_prod (μ := Measure.pi fun _ : Fin N => L')
    (ν := Measure.pi fun _ : OffDiag N => L) Set.univ Set.univ
  rw [Set.univ_prod_univ] at this
  rw [this]
  calc _ ≤ 1 * 1 := mul_le_mul' h1 h2
    _ = 1 := one_mul 1

private lemma coupling_isProb_selector (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ) :
    IsProbabilityMeasure (ν.map (largeInd T)) :=
  inferInstance

/-- The selector law is `ν{|x| ≤ T} δ₀ + ν{|x| > T} δ₁`. -/
private lemma coupling_map_largeInd (ν : Measure ℝ) (T : ℝ) :
    ν.map (largeInd T) =
      ν {x | |x| ≤ T} • Measure.dirac 0 + ν {x | T < |x|} • Measure.dirac 1 := by
  have hA := coupling_measurableSet_small T
  have hB := coupling_measurableSet_large T
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := ν) hA]
  rw [Measure.map_add _ _ (measurable_largeInd T), coupling_compl_small]
  congr 1
  · rw [Measure.map_congr (g := fun _ => (0 : ℝ)) ?_, Measure.map_const,
      Measure.restrict_apply_univ]
    filter_upwards [ae_restrict_mem hA] with x hx
    simp [largeInd, not_lt.mpr (show |x| ≤ T from hx)]
  · rw [Measure.map_congr (g := fun _ => (1 : ℝ)) ?_, Measure.map_const,
      Measure.restrict_apply_univ]
    filter_upwards [ae_restrict_mem hB] with x hx
    simp [largeInd, show T < |x| from hx]

/-- The mixture `(1 - c) s + c l + m` for `c ∼ a δ₀ + b δ₁` independent of `s` and `l`. -/
private lemma coupling_map_mix (μS μL : Measure ℝ) [IsProbabilityMeasure μS]
    [IsProbabilityMeasure μL] (a b : ENNReal) (m : ℝ) :
    (μS.prod (μL.prod (a • Measure.dirac 0 + b • Measure.dirac 1))).map
      (fun q : ℝ × ℝ × ℝ => (1 - q.2.2) * q.1 + q.2.2 * q.2.1 + m) =
      a • μS.map (fun x => x + m) + b • μL.map (fun x => x + m) := by
  have hf : Measurable (fun q : ℝ × ℝ × ℝ => (1 - q.2.2) * q.1 + q.2.2 * q.2.1 + m) := by
    fun_prop
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_add,
    Measure.prod_smul_right, Measure.prod_smul_right, Measure.map_add _ _ hf,
    Measure.map_smul _ hf.aemeasurable, Measure.map_smul _ hf.aemeasurable,
    Measure.prod_dirac, Measure.prod_dirac]
  congr 2
  · rw [show μS.prod (Measure.map (fun x => (x, (0 : ℝ))) μL) =
        (μS.prod μL).map (Prod.map id (fun x => (x, (0 : ℝ)))) by
          rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id],
      Measure.map_map hf (by fun_prop)]
    rw [show ((fun q : ℝ × ℝ × ℝ => (1 - q.2.2) * q.1 + q.2.2 * q.2.1 + m) ∘
        Prod.map id (fun x => (x, (0 : ℝ)))) = (fun x => x + m) ∘ Prod.fst by
          funext q; simp,
      ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul]
  · rw [show μS.prod (Measure.map (fun x => (x, (1 : ℝ))) μL) =
        (μS.prod μL).map (Prod.map id (fun x => (x, (1 : ℝ)))) by
          rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id],
      Measure.map_map hf (by fun_prop)]
    rw [show ((fun q : ℝ × ℝ × ℝ => (1 - q.2.2) * q.1 + q.2.2 * q.2.1 + m) ∘
        Prod.map id (fun x => (x, (1 : ℝ)))) = (fun x => x + m) ∘ Prod.snd by
          funext q; simp,
      ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod, measure_univ,
      one_smul]

private lemma coupling_map_shift (μ : Measure ℝ) (c : ℝ) :
    (μ.map (fun x => x - c)).map (fun x => x + c) = μ := by
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    show ((fun x : ℝ => x + c) ∘ fun x => x - c) = id from funext fun x => by simp,
    Measure.map_id]

private lemma coupling_smul_cond (ν : Measure ℝ) [IsFiniteMeasure ν] {s : Set ℝ}
    (h : ν s ≠ 0) : ν s • cond ν s = ν.restrict s := by
  rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

/-- (4.16) for one entry: `(1 - c) x^S + c x^L + m` has law `ν`. -/
private lemma coupling_map_coord (ν : Measure ℝ) [IsProbabilityMeasure ν] {T : ℝ}
    (hS : ν {x | |x| ≤ T} ≠ 0) :
    ((truncCentered ν T).prod ((truncLargeCentered ν T).prod (ν.map (largeInd T)))).map
      (fun q : ℝ × ℝ × ℝ => (1 - q.2.2) * q.1 + q.2.2 * q.2.1 + cutoffMean ν T) = ν := by
  have := isProbabilityMeasure_truncCentered ν hS
  have := isProbabilityMeasure_truncLargeCentered ν T
  have hA := coupling_measurableSet_small T
  have hSm : truncCentered ν T = (cond ν {x | |x| ≤ T}).map (fun x => x - cutoffMean ν T) :=
    rfl
  rw [coupling_map_largeInd, coupling_map_mix, hSm, coupling_map_shift,
    coupling_smul_cond ν hS]
  have hL : ν {x | T < |x|} • (truncLargeCentered ν T).map (fun x => x + cutoffMean ν T) =
      ν.restrict {x | |x| ≤ T}ᶜ := by
    rw [coupling_compl_small]
    by_cases hB : ν {x | T < |x|} = 0
    · rw [hB, zero_smul, Measure.restrict_eq_zero.mpr hB]
    · simp only [truncLargeCentered, hB, ↓reduceIte]
      rw [coupling_map_shift, coupling_smul_cond ν hB]
  rw [hL, Measure.restrict_add_restrict_compl hA]

/-! ### All coordinates -/

/-- Exchange of the middle factors of a product of four measures. -/
private lemma coupling_measurePreserving_swap4 {α β γ δ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] (a : Measure α) (b : Measure β)
    (c : Measure γ) (d : Measure δ) [SigmaFinite a] [SigmaFinite b] [SigmaFinite c]
    [SigmaFinite d] :
    MeasurePreserving (fun q : (α × β) × (γ × δ) => ((q.1.1, q.2.1), (q.1.2, q.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have h1 := measurePreserving_prodAssoc a b (c.prod d)
  have h2 := (MeasurePreserving.id a).prod
    (MeasurePreserving.symm _ (measurePreserving_prodAssoc b c d))
  have h3 := (MeasurePreserving.id a).prod
    ((Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d))
  have h4 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have h5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc a c (b.prod d))
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- Three independent product blocks, read coordinatewise through `g`. -/
private lemma coupling_pi_triple {ι : Type*} [Fintype ι] (μ1 μ2 μ3 : Measure ℝ)
    [IsProbabilityMeasure μ1] [IsProbabilityMeasure μ2] [IsProbabilityMeasure μ3]
    (g : ℝ × ℝ × ℝ → ℝ) (hg : Measurable g) :
    ((Measure.pi fun _ : ι => μ1).prod
        ((Measure.pi fun _ : ι => μ2).prod (Measure.pi fun _ : ι => μ3))).map
      (fun q i => g (q.1 i, q.2.1 i, q.2.2 i)) =
      Measure.pi fun _ : ι => (μ1.prod (μ2.prod μ3)).map g := by
  have h1 := measurePreserving_arrowProdEquivProdArrow ℝ (ℝ × ℝ) ι (fun _ => μ1)
    (fun _ => μ2.prod μ3)
  have h2 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun _ => μ2) (fun _ => μ3)
  have h := ((MeasurePreserving.id (Measure.pi fun _ : ι => μ1)).prod h2).comp h1
  rw [← h.map_eq, Measure.map_map (by fun_prop) h.measurable]
  exact Measure.pi_map_pi (fun _ => hg.aemeasurable)

theorem isProbabilityMeasure_coupleLaw {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} {N : ℕ}
    (hS : ν {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0)
    (hS' : ν' {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0) :
    IsProbabilityMeasure (coupleLaw ν ν' ε N) := by
  have := isProbabilityMeasure_truncCentered ν hS
  have := isProbabilityMeasure_truncCentered ν' hS'
  have := isProbabilityMeasure_truncLargeCentered ν ((N : ℝ) ^ (1 / 2 - ε))
  have := isProbabilityMeasure_truncLargeCentered ν' ((N : ℝ) ^ (1 / 2 - ε))
  have := coupling_isProb_selector ν ((N : ℝ) ^ (1 / 2 - ε))
  have := coupling_isProb_selector ν' ((N : ℝ) ^ (1 / 2 - ε))
  unfold coupleLaw
  infer_instance

/-- (4.16) at a general cut-off `T`. -/
private lemma coupling_map_aux (ν ν' : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (T : ℝ) (N : ℕ) (hS : ν {x | |x| ≤ T} ≠ 0)
    (hS' : ν' {x | |x| ≤ T} ≠ 0) :
    ((entryLaw (truncCentered ν T) (truncCentered ν' T) N).prod
        ((entryLaw (truncLargeCentered ν T) (truncLargeCentered ν' T) N).prod
          (entryLaw (ν.map (largeInd T)) (ν'.map (largeInd T)) N))).map
      (coupleMap (cutoffMean ν T) (cutoffMean ν' T)) = entryLaw ν ν' N := by
  have := isProbabilityMeasure_truncCentered ν hS
  have := isProbabilityMeasure_truncCentered ν' hS'
  have := isProbabilityMeasure_truncLargeCentered ν T
  have := isProbabilityMeasure_truncLargeCentered ν' T
  have := coupling_isProb_selector ν T
  have := coupling_isProb_selector ν' T
  have hgm : Measurable (fun q : ℝ × ℝ × ℝ => (1 - q.2.2) * q.1 + q.2.2 * q.2.1 +
      cutoffMean ν T) := by fun_prop
  have hgm' : Measurable (fun q : ℝ × ℝ × ℝ => (1 - q.2.2) * q.1 + q.2.2 * q.2.1 +
      cutoffMean ν' T) := by fun_prop
  have hFd : Measurable (fun (q : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) (i : Fin N) =>
      (1 - q.2.2 i) * q.1 i + q.2.2 i * q.2.1 i + cutoffMean ν' T) := by fun_prop
  have hFo : Measurable (fun (q : (OffDiag N → ℝ) × (OffDiag N → ℝ) × (OffDiag N → ℝ))
      (p : OffDiag N) => (1 - q.2.2 p) * q.1 p + q.2.2 p * q.2.1 p + cutoffMean ν T) := by
    fun_prop
  have hsw := (MeasurePreserving.id (entryLaw (truncCentered ν T) (truncCentered ν' T) N)).prod
    (coupling_measurePreserving_swap4
      (Measure.pi fun _ : Fin N => truncLargeCentered ν' T)
      (Measure.pi fun _ : OffDiag N => truncLargeCentered ν T)
      (Measure.pi fun _ : Fin N => ν'.map (largeInd T))
      (Measure.pi fun _ : OffDiag N => ν.map (largeInd T)))
  have hsw2 := coupling_measurePreserving_swap4
    (Measure.pi fun _ : Fin N => truncCentered ν' T)
    (Measure.pi fun _ : OffDiag N => truncCentered ν T)
    ((Measure.pi fun _ : Fin N => truncLargeCentered ν' T).prod
      (Measure.pi fun _ : Fin N => ν'.map (largeInd T)))
    ((Measure.pi fun _ : OffDiag N => truncLargeCentered ν T).prod
      (Measure.pi fun _ : OffDiag N => ν.map (largeInd T)))
  have hsh : MeasurePreserving
      (fun u : CoupleSpace N => ((u.1.1, u.2.1.1, u.2.2.1), (u.1.2, u.2.1.2, u.2.2.2)))
      ((entryLaw (truncCentered ν T) (truncCentered ν' T) N).prod
        ((entryLaw (truncLargeCentered ν T) (truncLargeCentered ν' T) N).prod
          (entryLaw (ν.map (largeInd T)) (ν'.map (largeInd T)) N)))
      (((Measure.pi fun _ : Fin N => truncCentered ν' T).prod
          ((Measure.pi fun _ : Fin N => truncLargeCentered ν' T).prod
            (Measure.pi fun _ : Fin N => ν'.map (largeInd T)))).prod
        ((Measure.pi fun _ : OffDiag N => truncCentered ν T).prod
          ((Measure.pi fun _ : OffDiag N => truncLargeCentered ν T).prod
            (Measure.pi fun _ : OffDiag N => ν.map (largeInd T))))) :=
    hsw2.comp hsw
  have hcm : (coupleMap (cutoffMean ν T) (cutoffMean ν' T) : CoupleSpace N → Entries N) =
      Prod.map (fun (q : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) (i : Fin N) =>
          (1 - q.2.2 i) * q.1 i + q.2.2 i * q.2.1 i + cutoffMean ν' T)
        (fun (q : (OffDiag N → ℝ) × (OffDiag N → ℝ) × (OffDiag N → ℝ)) (p : OffDiag N) =>
          (1 - q.2.2 p) * q.1 p + q.2.2 p * q.2.1 p + cutoffMean ν T) ∘
      (fun u : CoupleSpace N => ((u.1.1, u.2.1.1, u.2.2.1), (u.1.2, u.2.1.2, u.2.2.2))) :=
    rfl
  rw [hcm, ← Measure.map_map (hFd.prodMap hFo) hsh.measurable, hsh.map_eq,
    ← Measure.map_prod_map _ _ hFd hFo,
    coupling_pi_triple _ _ _ _ hgm', coupling_pi_triple _ _ _ _ hgm,
    coupling_map_coord ν hS, coupling_map_coord ν' hS']
  rfl

/-- (4.16): the coupled entries have the law of Definition 1.1, including the degenerate
cases `α = 0` or `α̃ = 0`. -/
theorem map_coupleMap_coupleLaw {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} {N : ℕ}
    (hS : ν {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0)
    (hS' : ν' {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0) :
    (coupleLaw ν ν' ε N).map (coupleMap (cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε)))
      (cutoffMean ν' ((N : ℝ) ^ (1 / 2 - ε)))) = entryLaw ν ν' N := by
  exact coupling_map_aux ν ν' _ N hS hS'

/-- `P_H(N^{2/3}(λ_N - 2) ≤ s)` computed on the auxiliary space. -/
theorem edgeCdf_eq_coupleLaw {ν ν' : Measure ℝ} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {ε : ℝ} {N : ℕ}
    (hS : ν {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0)
    (hS' : ν' {x | |x| ≤ (N : ℝ) ^ (1 / 2 - ε)} ≠ 0) (s : ℝ) :
    edgeCdf ν ν' N s = (coupleLaw ν ν' ε N {u | edgeScaled N (coupleMap
      (cutoffMean ν ((N : ℝ) ^ (1 / 2 - ε)))
      (cutoffMean ν' ((N : ℝ) ^ (1 / 2 - ε))) u) ≤ s}).toReal := by
  rw [edgeCdf, ← map_coupleMap_coupleLaw hS hS' (ε := ε),
    Measure.map_apply (measurable_coupleMap _ _ N)
      (measurableSet_le (measurable_edgeScaled N) measurable_const)]
  rfl

/-! ### Non-vacuity at Rademacher off-diagonal entries and `N(0, 2)` diagonal entries,
`ε = 1/100`, `N = 1000`: the off-diagonal tail is empty (`α = 0`), the diagonal tail is not -/

private lemma coupling_one_le_T : (1 : ℝ) ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) :=
  Real.one_le_rpow (by norm_num) (by norm_num)

/-- The small-mass condition for Rademacher entries. -/
private lemma coupling_hS :
    rademacher {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  have h1 : Measure.dirac (1 : ℝ) {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} = 1 :=
    Measure.dirac_apply_of_mem (by simpa using coupling_one_le_T)
  simp only [rademacher, Measure.smul_apply, Measure.add_apply, h1, smul_eq_mul]
  simp

/-- The small-mass condition for `N(0, 2)` diagonal entries. -/
private lemma coupling_hS' :
    gaussianReal 0 2 {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} ≠ 0 := by
  intro h
  have h0 := gaussianReal_absolutelyContinuous' 0 (by norm_num : (2 : NNReal) ≠ 0) h
  have hsub : Set.Icc (-1 : ℝ) 1 ⊆
      {x : ℝ | |x| ≤ ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))} := fun x hx =>
    (abs_le.mpr ⟨hx.1, hx.2⟩).trans coupling_one_le_T
  have := measure_mono_null hsub h0
  rw [Real.volume_Icc] at this
  norm_num at this

/-- Degenerate case `α = 0`: the large-part law is the junk law `δ₀`. -/
example : truncLargeCentered rademacher (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))) =
    Measure.dirac 0 := by
  have hT' : (1 : ℝ) ≤ (1000 : ℝ) ^ ((2 : ℝ)⁻¹ - (100 : ℝ)⁻¹) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  have h0 : rademacher {x : ℝ | ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)) < |x|} = 0 := by
    simp only [rademacher, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply,
      smul_eq_mul]
    simp [hT']
  simp only [truncLargeCentered, h0, ↓reduceIte]

/-- The law on the auxiliary space is a probability measure at this point. -/
example : IsProbabilityMeasure (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000) := by
  have := rademacher_wignerLaws.prob
  exact isProbabilityMeasure_coupleLaw coupling_hS coupling_hS'

/-- (4.16) at this point: all hypotheses hold at once. -/
example : (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000).map
    (coupleMap (cutoffMean rademacher (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))))
      (cutoffMean (gaussianReal 0 2) (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))))) =
    entryLaw rademacher (gaussianReal 0 2) 1000 := by
  have := rademacher_wignerLaws.prob
  exact map_coupleMap_coupleLaw coupling_hS coupling_hS'

/-- The distribution function of `N^{2/3}(λ_N - 2)` at `s = 0` on the auxiliary space. -/
example : edgeCdf rademacher (gaussianReal 0 2) 1000 0 =
    (coupleLaw rademacher (gaussianReal 0 2) (1 / 100) 1000 {u | edgeScaled 1000 (coupleMap
      (cutoffMean rademacher (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))))
      (cutoffMean (gaussianReal 0 2) (((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ)))) u)
        ≤ 0}).toReal := by
  have := rademacher_wignerLaws.prob
  exact edgeCdf_eq_coupleLaw coupling_hS coupling_hS' 0

/-- The mass bounds and probability facts for the blocks of the auxiliary space at the Rademacher
law, `N = 1000`, `ε = 1/100`, with the cut-off `T = N^{1/2 - ε}`. -/
example (T : ℝ) (hT : T = ((1000 : ℕ) : ℝ) ^ (1 / 2 - (1 / 100 : ℝ))) :
    IsProbabilityMeasure (truncCentered rademacher T) ∧
    IsProbabilityMeasure (truncLargeCentered rademacher T) ∧
    ((cond rademacher {x : ℝ | |x| ≤ T}).map fun x => x - 1) Set.univ ≤ 1 ∧
    entryLaw (truncCentered rademacher T) (truncLargeCentered rademacher T) 1000 Set.univ ≤ 1 ∧
    Measurable (largeInd T) := by
  subst hT
  have := rademacher_wignerLaws.prob
  exact ⟨isProbabilityMeasure_truncCentered rademacher coupling_hS,
    isProbabilityMeasure_truncLargeCentered rademacher _,
    map_cond_univ_le_one rademacher _ _ (by fun_prop),
    entryLaw_univ_le_one 1000 (truncCentered_univ_le_one rademacher _)
      (truncLargeCentered_univ_le_one rademacher _),
    measurable_largeInd _⟩

#print axioms measurable_coupleMap
#print axioms isProbabilityMeasure_coupleLaw
#print axioms map_coupleMap_coupleLaw
#print axioms edgeCdf_eq_coupleLaw

end WEdgeNS
