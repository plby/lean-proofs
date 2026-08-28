import Wikipedia.NoExoticSixSphere.CompactSupportedCapMap
import Wikipedia.NoExoticSixSphere.SupportedModTwoExcision
import Wikipedia.NoExoticSixSphere.SupportedNeighborhoodHomology

/-!
# Original compact-supported caps commute with open-neighborhood inclusion

The support remains compact in the actual neighborhood. Inclusion sends
its constructed fundamental class to the ambient class by the original
local evaluation square and uniqueness. Actual relative-cap naturality
then gives the cap square with the original cohomology excision map.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M] (U K : Set M)

/-- A compact support contained in a subspace is compact in that actual subspace. -/
theorem supportIn_isCompact (hK : IsCompact K) (hKU : K ⊆ U) : IsCompact (supportIn U K) :=
  Topology.IsInducing.subtypeVal.isCompact_preimage'
    hK (by simpa only [Subtype.range_coe] using hKU)

end NoExoticSixSphere.SupportedRelativeHomology

namespace NoExoticSixSphere.CompactSupportedFundamentalClass

open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U : Set M) (hU : IsOpen U) [ChartedSpace E U]

include hU in
/-- Inclusion of the original pair preserves the constructed compact-supported class. -/
theorem inclusion_fundamentalClass (K : Set M) (hK : IsCompact K) (hKU : K ⊆ U) :
    inclusionMap (ModuleCat.of ℤ (ZMod 2)) U K (n + 3)
        (fundamentalClass (E := E) n (supportIn U K) (supportIn_isCompact U K hK hKU)) =
      fundamentalClass (E := E) n K hK :=
  unique (E := E) n K hK _
    (IsFundamentalOn.inclusion (E := E) n U hU hKU
      (isFundamentalOn (E := E) n (supportIn U K) (supportIn_isCompact U K hK hKU)))

end NoExoticSixSphere.CompactSupportedFundamentalClass

namespace NoExoticSixSphere.CompactSupportedCapMap

open SupportedRelativeHomology SupportedModTwoCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U : Set M) (hU : IsOpen U) [ChartedSpace E U]

/-- The actual cap square for restriction to a neighborhood and absolute homology inclusion. -/
theorem dualityMap_neighborhood (K : Set M) (hK : IsCompact K) (hKU : K ⊆ U)
    (p q : ℕ) (h : p + q = n + 3) (a : SupportedModTwoCohomology.Cohomology K p) :
    modHomologyMap 2 (subtypeInclusion U) q
        (dualityMap (E := E) n (supportIn U K) (supportIn_isCompact U K hK hKU) p q h
          (neighborhoodEquiv U K hU hK.isClosed hKU p a)) =
      dualityMap (E := E) n K hK p q h a := by
  have he := RelativeModTwoCap.capProductInDegree_naturality (subtypeInclusion U)
    (show Set.MapsTo (subtypeInclusion U) (supportIn U K)ᶜ Kᶜ from fun _ hx => hx) h a
    (CompactSupportedFundamentalClass.fundamentalClass (E := E) n
      (supportIn U K) (supportIn_isCompact U K hK hKU))
  change modHomologyMap 2 (subtypeInclusion U) q
      (dualityMap (E := E) n (supportIn U K) (supportIn_isCompact U K hK hKU) p q h
        (neighborhoodEquiv U K hU hK.isClosed hKU p a)) =
    RelativeModTwoCap.capProductInDegree Kᶜ h a
      (inclusionMap (ModuleCat.of ℤ (ZMod 2)) U K (n + 3)
        (CompactSupportedFundamentalClass.fundamentalClass (E := E) n
          (supportIn U K) (supportIn_isCompact U K hK hKU))) at he
  rw [CompactSupportedFundamentalClass.inclusion_fundamentalClass (E := E) n U hU K hK hKU] at he
  exact he

end NoExoticSixSphere.CompactSupportedCapMap
