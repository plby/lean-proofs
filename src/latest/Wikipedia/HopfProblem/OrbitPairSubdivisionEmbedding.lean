import Wikipedia.HopfProblem.OrbitPairSubdivisionInjectivity
import Wikipedia.HopfProblem.OrbitPairRealizationFiniteCompact

/-!
# The barycentric map is a closed embedding

The actual subdivided standard simplex is a finite-poset nerve, so its
realization is compact. The verified coordinate injectivity consequently
gives a closed embedding into the geometric simplex. Surjectivity remains
a separate obligation before this can be called a homeomorphism.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder Topology

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open RealizationSimplex

instance subdividedSimplexFinite (n : ℕ) : SSet.Finite (SimplexCategory.sd.{u}.obj ⦋n⦌) :=
  inferInstanceAs (SSet.Finite (nerve (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))))

theorem barycentricMap_isClosedEmbedding (n : ℕ) : IsClosedEmbedding (barycentricMap.{u} n) :=
  (barycentricMap n).continuous.isClosedEmbedding (barycentricMap_injective n)

theorem barycentricMap_isClosed_range (n : ℕ) : IsClosed (Set.range (barycentricMap.{u} n)) :=
  (barycentricMap_isClosedEmbedding n).isClosed_range

end Wikipedia.HopfProblem.OrbitPair.Subdivision
