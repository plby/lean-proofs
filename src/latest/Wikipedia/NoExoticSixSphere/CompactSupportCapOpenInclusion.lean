import Wikipedia.NoExoticSixSphere.CompactSupportedCapInclusion
import Wikipedia.NoExoticSixSphere.CompactSupportOpenInclusion
import Wikipedia.NoExoticSixSphere.CompactSupportCapMap

/-!
# The original compact-support cap commutes with open inclusion

The fundamental class of a compact subset of the open subspace maps to
the class on its actual image. Relative-cap naturality and the inverse
excision formula prove compatibility on every compact-support component.
The actual representative formula then proves the direct-limit cap square.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportedFundamentalClass

open SupportedRelativeHomology OpenSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U : Set M) (hU : IsOpen U) [ChartedSpace E U]

include hU in
/-- Inclusion maps the class of the actual neighborhood support to its ambient image class. -/
theorem inclusion_image_fundamentalClass (K : Set U) (hK : IsCompact K) :
    (HomologicalComplex.homologyMap (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod 2))
        (subtypeInclusion U) (inclusion_mapsTo U K)) (n + 3)).hom
        (fundamentalClass (E := E) n K hK) =
      fundamentalClass (E := E) n (imageSupport U K) (hK.image continuous_subtype_val) := by
  have hgen (L : Set U) (hL : L = supportIn U (imageSupport U K)) (hLc : IsCompact L)
      (hf : Set.MapsTo (subtypeInclusion U) Lᶜ (imageSupport U K)ᶜ) :
      (HomologicalComplex.homologyMap
        (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod 2)) (subtypeInclusion U) hf)
          (n + 3)).hom (fundamentalClass (E := E) n L hLc) =
        fundamentalClass (E := E) n (imageSupport U K) (hK.image continuous_subtype_val) := by
    subst L
    exact inclusion_fundamentalClass (E := E) n U hU (imageSupport U K)
      (hK.image continuous_subtype_val) (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  exact hgen K (Set.preimage_image_eq K Subtype.val_injective).symm hK (inclusion_mapsTo U K)

end NoExoticSixSphere.CompactSupportedFundamentalClass

namespace NoExoticSixSphere.CompactSupportedCapMap

open OpenSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U : Set M) (hU : IsOpen U) [ChartedSpace E U]

/-- The original cap of an extended support class is the inclusion of its neighborhood cap. -/
theorem dualityMap_openExtension (K : Set U) (hK : IsCompact K)
    (p q : ℕ) (h : p + q = n + 3) (a : SupportedModTwoCohomology.Cohomology K p) :
    dualityMap (E := E) n (imageSupport U K) (hK.image continuous_subtype_val) p q h
        (extension U hU K hK p a) =
      modHomologyMap 2 (subtypeInclusion U) q (dualityMap (E := E) n K hK p q h a) := by
  have he := RelativeModTwoCap.capProductInDegree_naturality (subtypeInclusion U)
    (inclusion_mapsTo U K) h (extension U hU K hK p a)
    (CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK)
  change modHomologyMap 2 (subtypeInclusion U) q
      (dualityMap (E := E) n K hK p q h
        (restrictionEquiv U hU K hK p (extension U hU K hK p a))) =
    RelativeModTwoCap.capProductInDegree (imageSupport U K)ᶜ h (extension U hU K hK p a)
      ((HomologicalComplex.homologyMap (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod 2))
        (subtypeInclusion U) (inclusion_mapsTo U K)) (n + 3)).hom
          (CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK)) at he
  rw [restriction_extension,
    CompactSupportedFundamentalClass.inclusion_image_fundamentalClass (E := E) n U hU K hK] at he
  exact he.symm

end NoExoticSixSphere.CompactSupportedCapMap

namespace NoExoticSixSphere.CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U : Set M) (hU : IsOpen U) [ChartedSpace E U]

/-- Actual compact-support duality maps commute with open inclusion on every genuine class. -/
theorem dualityMap_openInclusion (p q : ℕ) (h : p + q = n + 3)
    (a : CompactSupportCohomology.Cohomology U p) :
    dualityMap (E := E) n M p q h (CompactSupportCohomology.inclusion U hU p a) =
      modHomologyMap 2 (subtypeInclusion U) q (dualityMap (E := E) n U p q h a) := by
  obtain ⟨K, b, rfl⟩ := CompactSupportCohomology.exists_representative U p a
  rw [CompactSupportCohomology.inclusion_of]
  apply (dualityMap_of (E := E) n M p q h (CompactSupportCohomology.imageCompact U K)
    (OpenSupportCohomology.extension U hU (K : Set U) K.isCompact p b)).trans
  exact (CompactSupportedCapMap.dualityMap_openExtension (E := E) n U hU (K : Set U)
    K.isCompact p q h b).trans
    (congrArg (modHomologyMap 2 (subtypeInclusion U) q)
      (dualityMap_of (E := E) n U p q h K b).symm)

end NoExoticSixSphere.CompactSupportCapMap
