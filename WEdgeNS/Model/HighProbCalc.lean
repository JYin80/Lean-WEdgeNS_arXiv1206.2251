import WEdgeNS.Model.HighProb

/-!
# Calculus of ζ-high probability (Definition 2.3)
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix

noncomputable section

namespace WEdgeNS

/-- Smaller class, larger events from some `N1` on. -/
theorem HighProbOn.mono_eventually {ζ : ℝ} {Cls Cls' : ∀ N : ℕ, EntryLaws N → Prop}
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

/-- "With ζ-high probability on `Ω₀`" combined with `Ω₀`. -/
theorem HighProbOn.of_imp {ζ : ℝ} {Cls : ∀ N : ℕ, EntryLaws N → Prop}
    {Ω₀ Ω : ∀ N : ℕ, EntryLaws N → Set (Entries N)} (h₀ : HighProbOn ζ Cls Ω₀)
    (h : HighProbOn ζ Cls (fun N L => (Ω₀ N L)ᶜ ∪ Ω N L)) : HighProbOn ζ Cls Ω := by
  refine HighProbOn.mono (h₀.inter h) (fun N L ω hω => ?_)
  rcases hω.2 with h2 | h2
  · exact absurd hω.1 h2
  · exact h2

/-- `(log N)^ξ = φ^ζ` for `ξ = ζ log log N` (the dictionary to [15]). -/
theorem log_rpow_mul_loglog {N : ℕ} (hN : 3 ≤ N) (ζ : ℝ) :
    Real.log N ^ (ζ * Real.log (Real.log N)) = phi N ^ ζ := by
  rw [mul_comm, Real.rpow_mul (Real.log_natCast_nonneg N)]
  rfl

/-! ### Compiled witnesses -/

/-- Witness for `HighProbOn.mono_eventually`: the larger events are the diagonal event for
`N ≥ 3` and empty below, so the threshold `N1 = 3` is used; the diagonal event is not trivial. -/
example :
    (diracLaws 3).IsProb ∧ (⋂ k : Fin 3, {ω : Entries 3 | ω.1 k = 0}) ≠ Set.univ ∧
      HighProbOn 1 diracCls (fun N _ => if 3 ≤ N then ⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}
        else ∅) :=
  ⟨diracLaws_isProb 3, diag_zero_ne_univ,
    HighProbOn.mono_eventually (Cls := diracCls) (Cls' := diracCls)
      (HighProbOn.inter (diag_highProb 1) (off_highProb 1)) (fun _ _ h => h)
      ⟨3, fun N hN _ _ ω hω => by simpa [hN] using hω.1⟩⟩

/-- Witness for `HighProbOn.of_imp`: `Ω₀` is the diagonal event and `Ω` its intersection with
the upper-entry event; both are nontrivial. -/
example :
    (diracLaws 3).IsProb ∧ (⋂ k : Fin 3, {ω : Entries 3 | ω.1 k = 0}) ≠ Set.univ ∧
      (⋂ p : OffDiag 3, {ω : Entries 3 | ω.2 p = 0}) ≠ Set.univ ∧
      HighProbOn 1 diracCls (fun N _ => (⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}) ∩
        (⋂ p : OffDiag N, {ω : Entries N | ω.2 p = 0})) := by
  refine ⟨diracLaws_isProb 3, diag_zero_ne_univ, off_zero_ne_univ, ?_⟩
  refine HighProbOn.of_imp (diag_highProb 1) ?_
  refine HighProbOn.mono (off_highProb 1) (fun N L ω hω => ?_)
  by_cases hD : ω ∈ ⋂ k : Fin N, {ω : Entries N | ω.1 k = 0}
  · exact Or.inr ⟨hD, hω⟩
  · exact Or.inl hD

/-- Numerical instance of the dictionary at `N = 3`, `ζ = 1`. -/
example : Real.log (3 : ℕ) ^ (1 * Real.log (Real.log (3 : ℕ))) = phi 3 ^ (1 : ℝ) :=
  log_rpow_mul_loglog (le_refl 3) 1

#print axioms HighProbOn.mono_eventually
#print axioms HighProbOn.of_imp
#print axioms log_rpow_mul_loglog

end WEdgeNS
