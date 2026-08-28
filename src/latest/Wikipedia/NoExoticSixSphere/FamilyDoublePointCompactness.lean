import Wikipedia.NoExoticSixSphere.GenericFamilyUnorderedBoundary

/-!
# Compactness and finite diagonal boundary from a genuine compact container

If all actual ordered double points lie in a specified compact set, their
closure is compact in the original pair space. Its actual unordered quotient
is compact as well. For a regular family the diagonal orbit set is closed
and discrete, hence finite. The compact-container hypothesis is explicit;
no global compactness of an arbitrary Euclidean family is asserted.
-/

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open GLOrthonormalization OperatorRank

theorem compactSpace_unordered_of_compact_container
    {P E F : Type*} [TopologicalSpace P] [T2Space P] [TopologicalSpace E] [T2Space E]
    (f : P → E → F) {K : Set (P × (E × E))} (hK : IsCompact K)
    (hbound : doublePoints f ⊆ K) : CompactSpace (UnorderedClosedDoublePoints f) := by
  have hcl : IsCompact (closure (doublePoints f)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hbound hK.isClosed)
  let := isCompact_iff_compactSpace.mp hcl
  exact Function.Surjective.compactSpace
    (isOpenQuotientMap_unorderedProj f).continuous (isOpenQuotientMap_unorderedProj f).surjective

theorem finite_diagonalOrbits_of_compact_container (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun p : ℝ × Vector 3 ↦ fderiv ℝ (f p.1) p.2))
    {K : Set (ℝ × (Vector 3 × Vector 3))} (hK : IsCompact K)
    (hbound : doublePoints f ⊆ K) : (diagonalOrbits f).Finite := by
  let := compactSpace_unordered_of_compact_container f hK hbound
  exact (isClosed_diagonalOrbits f).isCompact.finite (isDiscrete_diagonalOrbits f hf hreg)

end NoExoticSixSphere.FamilyEmbedding
