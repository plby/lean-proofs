import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingBasic

/-!
# Exactness of actual restriction along an open embedding

Coverings lift by literal inverse images, using only injectivity and
openness of the given embedding. The actual restriction functor has
both adjoints, hence preserves finite limits and finite colimits.
No separation or compactness condition is imposed on either space.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.Embedding

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)

/-- Every original ambient cover lifts through literal inverse-image opens. -/
instance openImage_cocontinuous :
    (openImage f hf).IsCocontinuous (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology X) where
  cover_lift {V S} hS := by
    intro t ht
    obtain ⟨W, i, hi, htW⟩ := hS (f t) ⟨t, ht, rfl⟩
    let W' := preimageOpen f W
    have hW'V : W' ≤ V := preimage_le_of_le_image f hf i.le
    let k : (openImage f hf).obj W' ⟶ W := homOfLE (imagePreimage_le f hf W)
    refine ⟨W', homOfLE hW'V, ?_, htW⟩
    exact S.downward_closed hi k

/-- The actual continuous image-open functor supplies the left adjoint
to the actual restriction functor. -/
instance restriction_rightAdjoint : (restriction f hf).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (openImage f hf)
    AddCommGrpCat (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)).isRightAdjoint

/-- The actual lifted-cover construction supplies the right adjoint
to the same original restriction functor. -/
instance restriction_leftAdjoint : (restriction f hf).IsLeftAdjoint :=
  ((openImage f hf).sheafAdjunctionCocontinuous AddCommGrpCat
    (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)).isLeftAdjoint

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction f hf) := by
  infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction f hf) := by
  infer_instance

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.Embedding
