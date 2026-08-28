import Wikipedia.HopfProblem.DegreeCollapseIntegralManifoldDuality
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenCapNaturality

/-!
# Bijectivity of the original constructed cap on every actual open subset

The native open-subset atlas has the proved manifold duality property.
Restricting the original ambient primitive family by original excision
therefore makes the already constructed open-subset cap bijective.
No compactness or closed-manifold hypothesis is imposed on the open subset.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass

open FirstHurewicz IntegralCoherentSupport

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M] (U : Opens M)

theorem dualityMap_bijective (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (dualityMap (E := E) n (U : Set M) U.isOpen p q h) := by
  rw [← capOnOpen_manifold (E := E) n (U : Set M) U.isOpen p q h]
  exact IntegralCapDuality.Duality.capOnOpen_bijective (U : Set M) U.isOpen
    (IntegralCapDuality.manifold_duality (E := E) n U)
    (manifoldFamily (E := E) n) (manifoldFamily_compatible (E := E) n)
    (manifoldFamily_primitive (E := E) n) p q h

def dualityEquiv (p q : ℕ) (h : p + q = n + 3) :
    IntegralCompactSupportCohomology.Cohomology U p ≃ₗ[ℤ] (singularComplex U).homology q :=
  LinearEquiv.ofBijective (dualityMap (E := E) n (U : Set M) U.isOpen p q h)
    (dualityMap_bijective (E := E) n U p q h)

theorem dualityEquiv_toLinearMap (p q : ℕ) (h : p + q = n + 3) :
    (dualityEquiv (E := E) n U p q h).toLinearMap =
      dualityMap (E := E) n (U : Set M) U.isOpen p q h := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass
