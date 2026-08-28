import Wikipedia.NoExoticSixSphere.CompactChartFundamentalSupport

/-!
# Finite unions of compact supports contained in actual charts

The intersection of two compact chart-contained supports is compact and
remains in either chart. The finite-union induction therefore supplies
the actual intersection properties required by relative Mayer--Vietoris,
including equality of the original restricted fundamental classes.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- Finite unions of compact chart-contained subsets have all compact-support properties. -/
theorem finiteUnion_compactChart_support {ι : Type*} (s : Finset ι)
    (e : ι → OpenPartialHomeomorph M E) (K : ι → Set M)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hS : ∀ i ∈ s, K i ⊆ (e i).source) :
    CompactFundamentalSupport (E := E) n (⋃ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
    simpa using (CompactFundamentalSupport.empty (E := E) (M := M) n)
  | @insert i s hi ih =>
    have hKi := hK i (Finset.mem_insert_self i s)
    have hSi := hS i (Finset.mem_insert_self i s)
    have hsmallK : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hsmallS : ∀ j ∈ s, K j ⊆ (e j).source :=
      fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hleft := compact_chart_fundamentalSupport n (e i) (K i) hKi hSi
    have hright := ih K hsmallK hsmallS
    have hinter := ih (fun j => K i ∩ K j)
      (fun j hj => hKi.inter_right (hsmallK j hj).isClosed)
      (fun j hj => Set.inter_subset_right.trans (hsmallS j hj))
    have hinter' : CompactFundamentalSupport (E := E) n (K i ∩ (⋃ j ∈ s, K j)) := by
      simpa only [Set.inter_iUnion] using hinter
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using
      (CompactFundamentalSupport.union n hleft hright hinter')

end NoExoticSixSphere.SupportedRelativeHomology
