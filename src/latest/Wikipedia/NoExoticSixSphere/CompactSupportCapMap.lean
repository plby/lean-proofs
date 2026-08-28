import Wikipedia.NoExoticSixSphere.CompactSupportedCapMap
import Wikipedia.NoExoticSixSphere.CompactSupportCohomologyCompact

/-!
# The actual compact-support cap map

The constructed fundamental classes are compatible under support
restriction. Their cap maps therefore descend to the genuine directed
limit of compact-supported cohomology. On a compact manifold this is
exactly the original absolute cap map under the proved cohomology
equivalence. No bijectivity of either cap map is asserted here.
-/

noncomputable section

open TopologicalSpace
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- Cap with the compatible actual fundamental classes on all compact supports. -/
def dualityMap (p q : ℕ) (h : p + q = n + 3) :
    CompactSupportCohomology.Cohomology M p →ₗ[ℤ] ModHomology 2 M q :=
  CompactSupportCohomology.lift M p
    (fun K => CompactSupportedCapMap.dualityMap (E := E) n (K : Set M) K.isCompact p q h)
    (fun K L hKL a => CompactSupportedCapMap.dualityMap_extend (E := E) n hKL
      K.isCompact L.isCompact p q h a)

/-- Every compact-support representative retains its actual cap with its fundamental class. -/
theorem dualityMap_of (p q : ℕ) (h : p + q = n + 3) (K : Compacts M)
    (a : CompactSupportCohomology.Component M p K) :
    dualityMap (E := E) n M p q h (CompactSupportCohomology.of M p K a) =
      CompactSupportedCapMap.dualityMap (E := E) n (K : Set M) K.isCompact p q h a := rfl

/-- On a compact manifold this is exactly cap with the original global fundamental class. -/
theorem dualityMap_eq_absolute [CompactSpace M] (p q : ℕ) (h : p + q = n + 3)
    (a : CompactSupportCohomology.Cohomology M p) :
    dualityMap (E := E) n M p q h a = ManifoldCapMap.dualityMap (E := E) n M p q h
      (CompactSupportCohomology.absoluteEquiv M p a) := by
  obtain ⟨K, b, rfl⟩ := CompactSupportCohomology.exists_representative M p a
  rw [dualityMap_of, CompactSupportCohomology.absoluteEquiv_of]
  exact CompactSupportedCapMap.dualityMap_eq_absolute (E := E) n (K : Set M) K.isCompact p q h b

end NoExoticSixSphere.CompactSupportCapMap
