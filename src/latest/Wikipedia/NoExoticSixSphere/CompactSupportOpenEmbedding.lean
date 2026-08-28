import Wikipedia.NoExoticSixSphere.OpenEmbeddingSupportComposition
import Wikipedia.NoExoticSixSphere.CompactSupportOpenInclusion

/-!
# Functorial extension on genuine compact-support cohomology

An actual open embedding sends each compact support to its compact
image. Inverse excision is compatible with support enlargement and
therefore descends to the original directed limit. Identity,
composition, and agreement with the original open-subspace inclusion
are proved using the actual maps on representatives.
-/

noncomputable section

open TopologicalSpace
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.CompactSupportCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y))

/-- The original image of a compact support under the supplied continuous map. -/
def mapCompact (K : Compacts X) : Compacts Y := ⟨f '' (K : Set X), K.isCompact.image f.continuous⟩

variable [T2Space Y] (hf : Topology.IsOpenEmbedding f) (p : ℕ)

/-- Extend a genuine component to its actual compact image and insert it in the target limit. -/
def openMapComponent (K : Compacts X) : Component X p K →ₗ[ℤ] Cohomology Y p :=
  (of Y p (mapCompact f K)).comp (OpenEmbeddingSupportCohomology.extension
    f hf (K : Set X) K.isCompact (mapCompact f K : Set Y) rfl p)

theorem openMapComponent_transition (K L : Compacts X) (h : K ≤ L) (a : Component X p K) :
    openMapComponent f hf p L (transition X p K L h a) = openMapComponent f hf p K a := by
  change of Y p (mapCompact f L) (OpenEmbeddingSupportCohomology.extension
    f hf (L : Set X) L.isCompact (mapCompact f L : Set Y) rfl p
      (SupportedModTwoCohomology.extend h p a)) = _
  apply (congrArg (of Y p (mapCompact f L))
    (OpenEmbeddingSupportCohomology.extension_extend f hf h
      (show (mapCompact f K : Set Y) ⊆ mapCompact f L from Set.image_mono h)
      K.isCompact L.isCompact rfl rfl p a).symm).trans
  exact of_transition Y p (K := mapCompact f K) (L := mapCompact f L)
    (show mapCompact f K ≤ mapCompact f L from Set.image_mono h)
    (OpenEmbeddingSupportCohomology.extension f hf (K : Set X) K.isCompact
      (mapCompact f K : Set Y) rfl p a)

/-- Extension along an actual open embedding on the original compact-support direct limits. -/
def openMap : Cohomology X p →ₗ[ℤ] Cohomology Y p :=
  lift X p (openMapComponent f hf p) (openMapComponent_transition f hf p)

theorem openMap_of (K : Compacts X) (a : Component X p K) :
    openMap f hf p (of X p K a) = of Y p (mapCompact f K)
      (OpenEmbeddingSupportCohomology.extension f hf (K : Set X) K.isCompact
        (mapCompact f K : Set Y) rfl p a) := rfl

/-- The representative formula with a separately named actual compact image. -/
theorem openMap_of_image (K : Compacts X) (L : Compacts Y) (hL : f '' (K : Set X) = L)
    (a : Component X p K) :
    openMap f hf p (of X p K a) = of Y p L
      (OpenEmbeddingSupportCohomology.extension f hf (K : Set X) K.isCompact
        (L : Set Y) hL p a) := by
  have he : mapCompact f K = L := SetLike.coe_injective hL
  subst L
  rfl

end NoExoticSixSphere.CompactSupportCohomology

namespace NoExoticSixSphere.CompactSupportCohomology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [T2Space X] [T2Space Y] [T2Space Z]

omit [T2Space X] in
/-- Successive open-embedding extensions equal extension along the original composite. -/
theorem openMap_comp (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)
    (g : C(Y, Z)) (hg : Topology.IsOpenEmbedding g) (p : ℕ) (a : Cohomology X p) :
    openMap g hg p (openMap f hf p a) = openMap (g.comp f) (hg.comp hf) p a := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  let L := mapCompact f K
  let P := mapCompact g L
  have hP : (g.comp f) '' (K : Set X) = (P : Set Z) := (Set.image_image g f (K : Set X)).symm
  rw [openMap_of f hf p, openMap_of g hg p, openMap_of_image (g.comp f) (hg.comp hf) p K P hP]
  exact congrArg (of Z p P) (OpenEmbeddingSupportCohomology.extension_comp f hf g hg
    (K : Set X) K.isCompact (L : Set Y) L.isCompact (P : Set Z) rfl rfl hP p b)

/-- Extension by the actual identity map is the identity on the genuine directed limit. -/
theorem openMap_id (p : ℕ) (a : Cohomology X p) :
    openMap (ContinuousMap.id X) Topology.IsOpenEmbedding.id p a = a := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  have he : (ContinuousMap.id X) '' (K : Set X) = (K : Set X) := Set.image_id _
  rw [openMap_of_image (ContinuousMap.id X) Topology.IsOpenEmbedding.id p K K he,
    OpenEmbeddingSupportCohomology.extension_id]

/-- For subtype inclusion this is exactly the previously constructed inverse-excision map. -/
theorem openMap_subtype (U : Set X) (hU : IsOpen U) (p : ℕ) :
    openMap (subtypeInclusion U) hU.isOpenEmbedding_subtypeVal p = inclusion U hU p := by
  apply LinearMap.ext
  intro a
  obtain ⟨K, b, rfl⟩ := exists_representative U p a
  rfl

end NoExoticSixSphere.CompactSupportCohomology
