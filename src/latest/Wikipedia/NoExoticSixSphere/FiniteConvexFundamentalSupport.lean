import Wikipedia.NoExoticSixSphere.CompactFundamentalSupportUnion

/-!
# Actual fundamental classes on finite unions of compact convex supports

Induction uses the proved closed-union theorem. The new intersection is
itself a finite union of compact convex sets, so its detection, vanishing,
and class are constructed by the same induction. Thus no intersection
agreement or homological vanishing is left as an input hypothesis.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- A finite union of actual compact convex Euclidean sets has all required support properties. -/
theorem finiteUnion_compactConvex_support {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hC : ∀ i ∈ s, Convex ℝ (K i)) :
    CompactFundamentalSupport (E := E) n (⋃ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
    simpa using (CompactFundamentalSupport.empty (E := E) (M := E) n)
  | @insert i s hi ih =>
    have hKi := hK i (Finset.mem_insert_self i s)
    have hCi := hC i (Finset.mem_insert_self i s)
    have hsmallK : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hsmallC : ∀ j ∈ s, Convex ℝ (K j) := fun j hj => hC j (Finset.mem_insert_of_mem hj)
    have hleft := compactConvex_fundamentalSupport n (K i) hKi hCi
    have hright := ih K hsmallK hsmallC
    have hinter := ih (fun j => K i ∩ K j)
      (fun j hj => hKi.inter_right (hsmallK j hj).isClosed)
      (fun j hj => hCi.inter (hsmallC j hj))
    have hinter' : CompactFundamentalSupport (E := E) n (K i ∩ (⋃ j ∈ s, K j)) := by
      simpa only [Set.inter_iUnion] using hinter
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using
      (CompactFundamentalSupport.union n hleft hright hinter')

/-- The unique actual relative mod-two fundamental class on the whole finite convex union. -/
theorem finiteUnion_existsUnique_fundamentalClass {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hC : ∀ i ∈ s, Convex ℝ (K i)) :
    ∃! c : Homology (ModuleCat.of ℤ (ZMod 2)) (⋃ i ∈ s, K i) (n + 3),
      IsFundamentalOn (E := E) n (⋃ i ∈ s, K i) c :=
  CompactFundamentalSupport.existsUnique n (finiteUnion_compactConvex_support n s K hK hC)

end NoExoticSixSphere.SupportedRelativeHomology
