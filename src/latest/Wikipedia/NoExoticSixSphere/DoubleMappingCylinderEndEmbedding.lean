import Wikipedia.NoExoticSixSphere.DoubleMappingCylinder
import Wikipedia.NoExoticSixSphere.PushoutOutsideAttachment

/-!
# The actual end spaces embed as closed subspaces of the double cylinder

The one endpoint avoids the zero endpoint in the inner cylinder pushout.
The original target then avoids that source in the outer pushout. The
outside-attachment lemma proves both end inclusions are closed embeddings
without requiring either of the original attaching maps to be injective.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DoubleMappingCylinder

theorem endpoint_isClosedEmbedding (A : TopCat.{u}) (t : I) :
    IsClosedEmbedding (HomotopyExtension.cylinderEndpoint A t) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_const.prodMk continuous_id) (fun _ _ h ↦ congrArg Prod.snd h)
    (isClosedMap_prodMk_left t)

theorem endpoint_avoids_endpoint (A : TopCat.{u}) (s t : I) (hst : s ≠ t) (a : A) :
    HomotopyExtension.cylinderEndpoint A s a ∉
      Set.range (HomotopyExtension.cylinderEndpoint A t) := by
  rintro ⟨b, h⟩
  exact hst (congrArg Prod.fst h).symm

variable {A X Y : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)

theorem mappingCylinder_target_isClosedEmbedding : IsClosedEmbedding (MappingCylinder.target f) :=
  ClosedPushout.base_isClosedEmbedding (MappingCylinder.square f) (endpoint_isClosedEmbedding A 0)

theorem mappingCylinder_source_isClosedEmbedding : IsClosedEmbedding (MappingCylinder.source f) :=
  PushoutOutsideAttachment.comp_isClosedEmbedding (MappingCylinder.square f)
    (HomotopyExtension.cylinderEndpoint A 1) (endpoint_isClosedEmbedding A 1)
    (endpoint_avoids_endpoint A 1 0 one_ne_zero)

theorem mappingCylinder_target_avoids_source (y : Y) :
    MappingCylinder.target f y ∉ Set.range (MappingCylinder.source f) := by
  rintro ⟨a, h⟩
  exact PushoutOutsideAttachment.ne_other_of_notMem_range (MappingCylinder.square f)
    (endpoint_avoids_endpoint A 1 0 one_ne_zero a) y h

theorem left_isClosedEmbedding : IsClosedEmbedding (left e f) :=
  ClosedPushout.base_isClosedEmbedding (square e f) (mappingCylinder_source_isClosedEmbedding f)

theorem right_isClosedEmbedding : IsClosedEmbedding (right e f) :=
  PushoutOutsideAttachment.comp_isClosedEmbedding (square e f)
    (MappingCylinder.target f) (mappingCylinder_target_isClosedEmbedding f)
    (mappingCylinder_target_avoids_source f)

theorem middle_isClosedEmbedding (he : IsClosedEmbedding e) : IsClosedEmbedding (middle e f) :=
  ClosedPushout.other_isClosedEmbedding (square e f) he

end NoExoticSixSphere.DoubleMappingCylinder
