import Wikipedia.HopfProblem.OrbitPairClosedPushoutGluing

/-!
# Closed embeddings remain closed embeddings after an actual pushout

The native colimit topology detects closed sets on its cocone legs.
Set-level pushout injectivity and intersection witnesses then show that
the image of every closed subset of the base is closed in the pushout.
No separation or compactness assumption on the spaces is needed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.ClosedPushout

variable {S A B P : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {i : A ⟶ P} {j : B ⟶ P} (hP : IsPushout f g i j)

include hP in
theorem isClosed_iff (U : Set P) : IsClosed U ↔ IsClosed (i ⁻¹' U) ∧ IsClosed (j ⁻¹' U) := by
  constructor
  · intro h
    exact ⟨h.preimage i.hom.continuous, h.preimage j.hom.continuous⟩
  · rintro ⟨hi, hj⟩
    apply (TopCat.isClosed_iff_of_isColimit hP.cocone hP.isColimit U).mpr
    intro k
    cases k with
    | none => exact hi.preimage f.hom.continuous
    | some k =>
      cases k with
      | left => exact hi
      | right => exact hj

include hP in
theorem base_injective (hg : Function.Injective g) : Function.Injective i :=
  Types.pushoutCocone_inr_injective_of_isColimit ((hP.flip.map (forget TopCat)).isColimit) hg

include hP in
theorem overlap_witness (hg : Function.Injective g) (a : A) (b : B) (h : i a = j b) :
    ∃ s, f s = a ∧ g s = b :=
  Types.exists_of_isPullback
    (Types.isPullback_of_isPushout (hP.flip.map (forget TopCat)) hg).flip a b h

include hP in
theorem preimage_image_other (hg : Function.Injective g) (C : Set A) :
    j ⁻¹' (i '' C) = g '' (f ⁻¹' C) := by
  ext b
  constructor
  · rintro ⟨a, ha, hab⟩
    obtain ⟨s, hsa, hsb⟩ := overlap_witness hP hg a b hab
    refine ⟨s, ?_, hsb⟩
    change f s ∈ C
    rw [hsa]
    exact ha
  · rintro ⟨s, hs, rfl⟩
    exact ⟨f s, hs, congrArg (fun m ↦ m s) hP.w⟩

include hP in
theorem base_isClosedMap (hg : IsClosedEmbedding g) : IsClosedMap i := by
  intro C hC
  apply (isClosed_iff hP (i '' C)).mpr
  constructor
  · rw [Set.preimage_image_eq _ (base_injective hP hg.injective)]
    exact hC
  · rw [preimage_image_other hP hg.injective]
    exact hg.isClosedMap _ (hC.preimage f.hom.continuous)

include hP in
theorem base_isClosedEmbedding (hg : IsClosedEmbedding g) : IsClosedEmbedding i :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap i.hom.continuous
    (base_injective hP hg.injective) (base_isClosedMap hP hg)

include hP in
theorem other_isClosedEmbedding (hf : IsClosedEmbedding f) : IsClosedEmbedding j :=
  base_isClosedEmbedding hP.flip hf

end Wikipedia.HopfProblem.OrbitPair.ClosedPushout
