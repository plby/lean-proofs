import Wikipedia.NoExoticSixSphere.OpenEmbeddingSupportCohomology
import Wikipedia.NoExoticSixSphere.SupportedModTwoPullback
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Nonvanishing of original point pullbacks on local homeomorphism neighborhoods

Original excision makes pullback along an open embedding injective when
the compact support lies in its image. At a point, compactness of the
inverse image follows from injectivity. A genuine local homeomorphism
therefore gives a neighborhood where the original pullback of a nonzero
point class remains nonzero. No abstract replacement of the class is used.
-/

noncomputable section

open Set Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- Excision makes original pullback injective for a compact support contained in the image. -/
theorem pullback_injective_of_openEmbedding (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (K : Set Y) (hK : IsCompact (f ⁻¹' K)) (himage : K ⊆ range f) (p : ℕ) :
    Function.Injective (pullback f K p) := by
  have he : f '' (f ⁻¹' K) = K := image_preimage_eq_of_subset himage
  exact (OpenEmbeddingSupportCohomology.restrictionEquiv f hf (f ⁻¹' K) hK K he p).injective

omit [T2Space Y] in
/-- The actual singleton inverse image under an embedding is compact. -/
theorem isCompact_preimage_singleton_of_injective (f : C(X, Y)) (hf : Function.Injective f)
    (x : X) : IsCompact (f ⁻¹' ({f x} : Set Y)) := by
  have he : f ⁻¹' ({f x} : Set Y) = {x} := by
    ext z
    exact ⟨fun hz => hf hz, fun hz => congrArg f hz⟩
  rw [he]
  exact isCompact_singleton

/-- Original point-supported pullback along an open embedding preserves nonzero classes. -/
theorem pullback_point_ne_zero_of_openEmbedding (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (x : X) (p : ℕ) (a : Cohomology ({f x} : Set Y) p) (ha : a ≠ 0) :
    pullback f ({f x} : Set Y) p a ≠ 0 := by
  intro he
  apply ha
  apply pullback_injective_of_openEmbedding f hf {f x}
    (isCompact_preimage_singleton_of_injective f hf.injective x)
    (singleton_subset_iff.mpr ⟨x, rfl⟩) p
  exact he.trans (map_zero (pullback f ({f x} : Set Y) p)).symm

/-- A genuine local homeomorphism gives a nonzero original restriction near the point. -/
theorem exists_point_pullback_ne_zero_neighborhood (f : C(X, Y)) (x : X)
    (hf : IsLocalHomeomorphOn f ({x} : Set X)) (p : ℕ)
    (a : Cohomology ({f x} : Set Y) p) (ha : a ≠ 0) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      InjOn f U ∧ pullback (subtypeInclusion U) (f ⁻¹' ({f x} : Set Y)) p
        (pullback f ({f x} : Set Y) p a) ≠ 0 := by
  obtain ⟨e, hx, he⟩ := hf x rfl
  let g : C(e.source, Y) := f.comp (subtypeInclusion e.source)
  have hg : IsOpenEmbedding g := by
    change IsOpenEmbedding (e.source.domRestrict f)
    rw [he]
    exact e.isOpenEmbedding_restrict
  refine ⟨e.source, e.open_source, hx, ?_, ?_⟩
  · rw [he]
    exact e.injOn
  · have hn := pullback_point_ne_zero_of_openEmbedding g hg ⟨x, hx⟩ p a ha
    change pullback (f.comp (subtypeInclusion e.source)) ({f x} : Set Y) p a ≠ 0 at hn
    rw [pullback_comp] at hn
    exact hn

end NoExoticSixSphere.SupportedModTwoCohomology
