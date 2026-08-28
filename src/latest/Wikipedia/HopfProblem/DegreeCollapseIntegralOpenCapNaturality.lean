import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenFundamentalClass
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenSupportCohomology

/-!
# The actual integral cap square for an open inclusion

The original pair inclusion sends the constructed open-subset class to
the constructed ambient class. Original cohomology excision identifies
the pulled-back extended cochain class with the given class. Integral cap
naturality therefore gives the commuting square on original compact-support
cohomology and original absolute integral homology.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass

open FirstHurewicz SingularMayerVietoris IntegralOpenSupport

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  (U : Set M) (hU : IsOpen U)

/-- The original compact-supported cap formula commutes with inclusion and inverse excision. -/
theorem componentMap_inclusion (K : Set U) (hK : IsCompact K)
    (p q : ℕ) (h : p + q = n + 3) (a : IntegralSupportedCohomology.Cohomology K p) :
    singularHomologyMap (subtypeInclusion U) q
        (IntegralCompactSupportCap.componentMap K h (supportedClass (E := E) n U hU K hK) a) =
      IntegralCompactSupportCap.componentMap (imageSupport U K) h
        (IntegralManifoldFundamentalClass.supportedClass (E := E) n M (imageSupport U K))
        (extension U hU K hK p a) := by
  have he := RelativeIntegralCap.capProductInDegree_naturality (subtypeInclusion U)
    (inclusion_mapsTo U K) h (extension U hU K hK p a) (supportedClass (E := E) n U hU K hK)
  change singularHomologyMap (subtypeInclusion U) q
      (RelativeIntegralCap.capProductInDegree Kᶜ h
        (restrictionEquiv U hU K hK p (extension U hU K hK p a))
        (supportedClass (E := E) n U hU K hK)) =
    RelativeIntegralCap.capProductInDegree (imageSupport U K)ᶜ h (extension U hU K hK p a)
      (IntegralOpenSupport.inclusionMap U K (n + 3) (supportedClass (E := E) n U hU K hK)) at he
  rw [restriction_extension, supportedClass_inclusion] at he
  exact he

/-- The commuting cap square uses the original map on both compact support and homology. -/
theorem dualityMap_inclusion (p q : ℕ) (h : p + q = n + 3)
    (a : IntegralCompactSupportCohomology.Cohomology U p) :
    singularHomologyMap (subtypeInclusion U) q (dualityMap (E := E) n U hU p q h a) =
      IntegralCompactSupportCap.dualityMap (E := E) n M p q h
        (IntegralCompactSupportCohomology.inclusion U hU p a) := by
  obtain ⟨K, b, rfl⟩ := IntegralCompactSupportCohomology.exists_representative U p a
  have ht := (congrArg (IntegralCompactSupportCap.dualityMap (E := E) n M p q h)
    (IntegralCompactSupportCohomology.inclusion_of U hU p K b)).trans
      (IntegralCompactSupportCap.dualityMap_of (E := E) n M p q h
        (IntegralCompactSupportCohomology.imageCompact U K)
        (extension U hU (K : Set U) K.isCompact p b))
  exact (congrArg (singularHomologyMap (subtypeInclusion U) q)
    (dualityMap_of (E := E) n U hU p q h K b)).trans
      ((componentMap_inclusion (E := E) n U hU (K : Set U) K.isCompact p q h b).trans ht.symm)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenFundamentalClass
