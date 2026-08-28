import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenEmbeddingComposition

/-!
# Functorial extension of actual integral compact-support cohomology

Inverse integral excision extends each actual compact representative
to its image support. Exact support compatibility descends the maps to
the original directed limits. Composition and identity retain those
original maps, including the already constructed subtype inclusion.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

open SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y))

def mapCompact (K : Compacts X) : Compacts Y := ⟨f '' (K : Set X), K.isCompact.image f.continuous⟩

variable [T2Space Y] (hf : Topology.IsOpenEmbedding f) (p : ℕ)

def openMapComponent (K : Compacts X) : Component X p K →ₗ[ℤ] Cohomology Y p :=
  (of Y p (mapCompact f K)).comp (IntegralOpenEmbeddingSupport.extension
    f hf (K : Set X) K.isCompact (mapCompact f K : Set Y) rfl p)

theorem openMapComponent_transition (K L : Compacts X) (h : K ≤ L) (a : Component X p K) :
    openMapComponent f hf p L (transition X p K L h a) = openMapComponent f hf p K a := by
  change of Y p (mapCompact f L) (IntegralOpenEmbeddingSupport.extension
    f hf (L : Set X) L.isCompact (mapCompact f L : Set Y) rfl p
      (IntegralSupportedCohomology.extend h p a)) = _
  apply (congrArg (of Y p (mapCompact f L))
    (IntegralOpenEmbeddingSupport.extension_extend f hf h
      (show (mapCompact f K : Set Y) ⊆ mapCompact f L from Set.image_mono h)
      K.isCompact L.isCompact rfl rfl p a).symm).trans
  exact of_transition Y p (K := mapCompact f K) (L := mapCompact f L)
    (show mapCompact f K ≤ mapCompact f L from Set.image_mono h)
    (IntegralOpenEmbeddingSupport.extension f hf (K : Set X) K.isCompact
      (mapCompact f K : Set Y) rfl p a)

/-- The original integral compact-support map of an actual open embedding. -/
def openMap : Cohomology X p →ₗ[ℤ] Cohomology Y p :=
  lift X p (openMapComponent f hf p) (openMapComponent_transition f hf p)

theorem openMap_of (K : Compacts X) (a : Component X p K) :
    openMap f hf p (of X p K a) = of Y p (mapCompact f K)
      (IntegralOpenEmbeddingSupport.extension f hf (K : Set X) K.isCompact
        (mapCompact f K : Set Y) rfl p a) := rfl

theorem openMap_of_image (K : Compacts X) (L : Compacts Y) (hL : f '' (K : Set X) = L)
    (a : Component X p K) :
    openMap f hf p (of X p K a) = of Y p L
      (IntegralOpenEmbeddingSupport.extension f hf (K : Set X) K.isCompact
        (L : Set Y) hL p a) := by
  have he : mapCompact f K = L := SetLike.coe_injective hL
  subst L
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

open SingularMayerVietoris

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [T2Space X] [T2Space Y] [T2Space Z]

omit [T2Space X] in
theorem openMap_comp (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)
    (g : C(Y, Z)) (hg : Topology.IsOpenEmbedding g) (p : ℕ) (a : Cohomology X p) :
    openMap g hg p (openMap f hf p a) = openMap (g.comp f) (hg.comp hf) p a := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  let L := mapCompact f K
  let P := mapCompact g L
  have hP : (g.comp f) '' (K : Set X) = (P : Set Z) := (Set.image_image g f (K : Set X)).symm
  rw [openMap_of f hf p, openMap_of g hg p, openMap_of_image (g.comp f) (hg.comp hf) p K P hP]
  exact congrArg (of Z p P) (IntegralOpenEmbeddingSupport.extension_comp f hf g hg
    (K : Set X) K.isCompact (L : Set Y) L.isCompact (P : Set Z) rfl rfl hP p b)

theorem openMap_id (p : ℕ) (a : Cohomology X p) :
    openMap (ContinuousMap.id X) Topology.IsOpenEmbedding.id p a = a := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  have he : (ContinuousMap.id X) '' (K : Set X) = (K : Set X) := Set.image_id _
  rw [openMap_of_image (ContinuousMap.id X) Topology.IsOpenEmbedding.id p K K he,
    IntegralOpenEmbeddingSupport.extension_id]

/-- This functor retains the already constructed original open-subspace inclusion map. -/
theorem openMap_subtype (U : Set X) (hU : IsOpen U) (p : ℕ) :
    openMap (subtypeInclusion U) hU.isOpenEmbedding_subtypeVal p = inclusion U hU p := by
  apply LinearMap.ext
  intro a
  obtain ⟨K, b, rfl⟩ := exists_representative U p a
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology
