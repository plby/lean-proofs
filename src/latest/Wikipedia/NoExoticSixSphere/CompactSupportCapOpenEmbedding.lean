import Wikipedia.NoExoticSixSphere.OpenEmbeddingSupportedHomology
import Wikipedia.NoExoticSixSphere.CompactSupportOpenEmbedding
import Wikipedia.NoExoticSixSphere.CompactSupportCapMap

/-!
# The original compact-support cap commutes with open embeddings

Original pair-map naturality, preservation of the constructed fundamental
classes, and the inverse-excision representative formula prove the
component square. Passing through the actual support representatives
gives naturality of the original direct-limit cap, for arbitrary open
embeddings between the original charted spaces.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportedCapMap

open OpenEmbeddingSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
  [ChartedSpace E X] [ChartedSpace E Y]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)

/-- Original cap naturality for extension to the actual compact image support. -/
theorem dualityMap_openEmbedding (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (p q : ℕ) (h : p + q = n + 3)
    (a : SupportedModTwoCohomology.Cohomology K p) :
    dualityMap (E := E) n L (hL ▸ hK.image f.continuous) p q h
        (extension f hf K hK L hL p a) =
      modHomologyMap 2 f q (dualityMap (E := E) n K hK p q h a) := by
  have he := RelativeModTwoCap.capProductInDegree_naturality f
    (mapsTo_compl f hf K L hL) h (extension f hf K hK L hL p a)
    (CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK)
  change modHomologyMap 2 f q
      (dualityMap (E := E) n K hK p q h
        (restrictionEquiv f hf K hK L hL p (extension f hf K hK L hL p a))) =
    RelativeModTwoCap.capProductInDegree Lᶜ h (extension f hf K hK L hL p a)
      (OpenEmbeddingSupportedHomology.map f hf (ModuleCat.of ℤ (ZMod 2)) K L hL (n + 3)
        (CompactSupportedFundamentalClass.fundamentalClass (E := E) n K hK)) at he
  rw [restriction_extension,
    CompactSupportedFundamentalClass.openEmbedding_fundamentalClass (E := E) n f hf K hK L hL]
    at he
  exact he.symm

end NoExoticSixSphere.CompactSupportedCapMap

namespace NoExoticSixSphere.CompactSupportCapMap

open CompactSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
  [ChartedSpace E X] [ChartedSpace E Y]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)

/-- The actual direct-limit cap square for the original open-embedding extension. -/
theorem dualityMap_openEmbedding (p q : ℕ) (h : p + q = n + 3) (a : Cohomology X p) :
    dualityMap (E := E) n Y p q h (openMap f hf p a) =
      modHomologyMap 2 f q (dualityMap (E := E) n X p q h a) := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  rw [openMap_of]
  apply (dualityMap_of (E := E) n Y p q h (mapCompact f K)
    (OpenEmbeddingSupportCohomology.extension f hf (K : Set X) K.isCompact
      (mapCompact f K : Set Y) rfl p b)).trans
  apply (CompactSupportedCapMap.dualityMap_openEmbedding (E := E) n f hf
    (K : Set X) K.isCompact (mapCompact f K : Set Y) rfl p q h b).trans
  exact congrArg (modHomologyMap 2 f q) (dualityMap_of (E := E) n X p q h K b).symm

end NoExoticSixSphere.CompactSupportCapMap
