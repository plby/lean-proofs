import Wikipedia.NoExoticSixSphere.SmallCapRelativeRepresentative
import Wikipedia.NoExoticSixSphere.CompactSupportedCapInclusion

/-!
# Localized cap is cap with the actual neighborhood fundamental class

The small-chain decomposition constructs a relative class inside the
open neighborhood. Its original pair-map image is the prescribed
ambient fundamental class. Actual relative excision and preservation
of the constructed fundamental class identify that local class.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.CompactSupportedCapMap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)
open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U : Set M) (hU : IsOpen U) [ChartedSpace E U]

/-- Localized cap of a supported fundamental representative is the actual neighborhood cap map. -/
theorem localized_cap_fundamental (K : Set M) (hK : IsCompact K) (hKU : K ⊆ U)
    (p q : ℕ) (h : p + q = n + 3) (α : RelativeModTwoCochains.Cocycle Kᶜ p)
    (c : SmallChains Coefficient U Kᶜ (n + 3))
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient Kᶜ) (n + 3))
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient Kᶜ (n + 3)
      (smallInclusionMap Coefficient U Kᶜ (n + 3) c))
    (hzclass : ModuleHomology.cycleClass _ (n + 3) z =
      CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK)
    (w : ModuleHomology.Cycle (modComplex 2 U) q)
    (hw : w.val = SmallModTwoCap.capInDegree U Kᶜ h α.val c) :
    ModuleHomology.cycleClass (modComplex 2 U) q w =
      dualityMap (E := E) n (supportIn U K) (supportIn_isCompact U K hK hKU) p q h
        (SupportedModTwoCohomology.neighborhoodEquiv U K hU hK.isClosed hKU p
          (SingularCohomologyFree.cocycleClass _ p α)) := by
  obtain ⟨b, hb, hcap⟩ := SmallModTwoCap.exists_relative_cap_class_inDegree U Kᶜ h α c z hz w hw
  have hbclass : b = CompactSupportedFundamentalClass.fundamentalClass (E := E) n
      (supportIn U K) (supportIn_isCompact U K hK hKU) := by
    apply (inclusionEquiv 2 (by decide) U K hU hK.isClosed hKU (n + 3)).injective
    exact hb.trans (hzclass.trans
      (CompactSupportedFundamentalClass.inclusion_fundamentalClass (E := E) n U hU K hK hKU).symm)
  exact hcap.trans (congrArg (fun t => RelativeModTwoCap.capProductInDegree
    (RelativeSingularHomology.overlapIn U Kᶜ) h
      (RelativeModTwoCochains.cohomologyPullback (subtypeInclusion U)
        (show Set.MapsTo (subtypeInclusion U) (RelativeSingularHomology.overlapIn U Kᶜ) Kᶜ
          from fun _ hx => hx) p (SingularCohomologyFree.cocycleClass _ p α)) t) hbclass)

end NoExoticSixSphere.CompactSupportedCapMap
