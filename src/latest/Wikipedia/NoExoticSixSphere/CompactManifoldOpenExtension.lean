import Wikipedia.NoExoticSixSphere.CompactSupportCapOpenEmbedding
import Wikipedia.NoExoticSixSphere.SupportedCohomologyPairPullback
import Wikipedia.NoExoticSixSphere.EmptySupportedCohomology

/-!
# Actual cohomology extension from a compact open component

The existing inverse-excision extension on compact supports induces an
extension on absolute cohomology. Its pullback to the original component
is the identity, while pullback to a disjoint component is zero. The
original fundamental-class cap square is retained.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem toAbsolute_pullbackTo (f : C(X, Y)) (K : Set Y) (L : Set X)
    (h : f ⁻¹' K ⊆ L) (p : ℕ) (a : Cohomology K p) :
    RelativeModTwoCochains.toAbsoluteCohomology Lᶜ p (pullbackTo f K L h p a) =
      ModTwoCapProduct.cohomologyPullback f p
        (RelativeModTwoCochains.toAbsoluteCohomology Kᶜ p a) := by
  rw [pullbackTo_eq_extend, toAbsolute_extend, toAbsolute_pullback]

end NoExoticSixSphere.SupportedModTwoCohomology

namespace NoExoticSixSphere.CompactManifoldOpenExtension

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f) (p : ℕ)

def map : ModTwoCapProduct.Cohomology X p →ₗ[ℤ] ModTwoCapProduct.Cohomology Y p :=
  (CompactSupportCohomology.absoluteEquiv Y p).toLinearMap.comp
    ((CompactSupportCohomology.openMap f hf p).comp
      (CompactSupportCohomology.absoluteEquiv X p).symm.toLinearMap)

theorem map_apply (a : ModTwoCapProduct.Cohomology X p) :
    map f hf p a = CompactSupportCohomology.absoluteEquiv Y p
      (CompactSupportCohomology.openMap f hf p
        ((CompactSupportCohomology.absoluteEquiv X p).symm a)) := rfl

theorem map_supported (a : SupportedModTwoCohomology.Cohomology (univ : Set X) p) :
    map f hf p (SupportedModTwoCohomology.absoluteEquiv p a) =
      RelativeModTwoCochains.toAbsoluteCohomology (f '' univ)ᶜ p
        (OpenEmbeddingSupportCohomology.extension f hf univ isCompact_univ
          (f '' univ) rfl p a) := by
  have he : (CompactSupportCohomology.absoluteEquiv X p).symm
      (SupportedModTwoCohomology.absoluteEquiv p a) =
      CompactSupportCohomology.of X p ⊤ a := by
    apply (CompactSupportCohomology.absoluteEquiv X p).injective
    rw [LinearEquiv.apply_symm_apply, CompactSupportCohomology.absoluteEquiv_of]
    rfl
  rw [map_apply, he, CompactSupportCohomology.openMap_of,
    CompactSupportCohomology.absoluteEquiv_of]
  rfl

theorem pullback_map (a : ModTwoCapProduct.Cohomology X p) :
    ModTwoCapProduct.cohomologyPullback f p (map f hf p a) = a := by
  obtain ⟨a, rfl⟩ := (SupportedModTwoCohomology.absoluteEquiv (X := X) p).surjective a
  rw [map_supported]
  let h : f ⁻¹' (f '' univ) ⊆ (univ : Set X) :=
    (OpenEmbeddingSupportCohomology.preimage_support f hf univ (f '' univ) rfl).subset
  exact (SupportedModTwoCohomology.toAbsolute_pullbackTo f (f '' univ) univ h p _).symm.trans
    (congrArg (RelativeModTwoCochains.toAbsoluteCohomology (univ : Set X)ᶜ p)
      (OpenEmbeddingSupportCohomology.pullbackTo_extension f hf univ isCompact_univ
        (f '' univ) rfl p a))

theorem pullback_map_disjoint {Z : Type} [TopologicalSpace Z] (g : C(Z, Y))
    (hd : Disjoint (range f) (range g)) (a : ModTwoCapProduct.Cohomology X p) :
    ModTwoCapProduct.cohomologyPullback g p (map f hf p a) = 0 := by
  have he : g ⁻¹' (f '' univ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨x, -, hx⟩ := hz
    exact Set.disjoint_left.mp hd ⟨x, hx⟩ ⟨z, rfl⟩
  let : Subsingleton (SupportedModTwoCohomology.Cohomology (g ⁻¹' (f '' univ)) p) := by
    rw [he]
    exact SupportedModTwoCohomology.cohomology_empty_subsingleton Z p
  obtain ⟨a, rfl⟩ := (SupportedModTwoCohomology.absoluteEquiv (X := X) p).surjective a
  rw [map_supported, ← SupportedModTwoCohomology.toAbsolute_pullback]
  rw [Subsingleton.elim (SupportedModTwoCohomology.pullback g (f '' univ) p _) 0, map_zero]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  [ChartedSpace E X] [ChartedSpace E Y]

theorem cap_map (q : ℕ) (h : p + q = n + 3) (a : ModTwoCapProduct.Cohomology X p) :
    ManifoldCapMap.dualityMap (E := E) n Y p q h (map f hf p a) =
      modHomologyMap 2 f q (ManifoldCapMap.dualityMap (E := E) n X p q h a) := by
  rw [map_apply, ← CompactSupportCapMap.dualityMap_eq_absolute,
    CompactSupportCapMap.dualityMap_openEmbedding, CompactSupportCapMap.dualityMap_eq_absolute,
    LinearEquiv.apply_symm_apply]

end NoExoticSixSphere.CompactManifoldOpenExtension
