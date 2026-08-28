import Wikipedia.NoExoticSixSphere.CompactAdjunctionGluing
import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionPushout

/-!
# The actual adjunction quotient is a categorical topological pushout

The previously constructed gluing map supplies the universal property.
Both legs are the original quotient map and the embedded attached
target; this identifies the concrete quotient with the native pushout.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace NoExoticSixSphere.CompactAdjunction

variable {A X Y : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace A] [T2Space Y] (D : Data A X Y)

theorem square : TopCat.ofHom D.embedding ≫ TopCat.ofHom (quotientMap D) =
    TopCat.ofHom D.attaching ≫ TopCat.ofHom (inclusion D) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact quotientMap_embedding D

theorem isPushout : IsPushout (TopCat.ofHom D.embedding) (TopCat.ofHom D.attaching)
    (TopCat.ofHom (quotientMap D)) (TopCat.ofHom (inclusion D)) := by
  apply IsPushout.mk' (square D)
  · intro Z φ ψ hq _
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    obtain ⟨x, rfl⟩ := projection_surjective D p
    exact congrArg (fun m ↦ m x) hq
  · intro Z F G h
    have hc : ∀ a, F (D.embedding a) = G (D.attaching a) :=
      fun a ↦ congrArg (fun m ↦ m a) h
    let L : TopCat.of (Space D) ⟶ Z := TopCat.ofHom (glue D F.hom G.hom hc)
    refine ⟨L, ?_, ?_⟩
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      exact glue_quotientMap D F.hom G.hom hc
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      exact glue_inclusion D F.hom G.hom hc

end NoExoticSixSphere.CompactAdjunction
