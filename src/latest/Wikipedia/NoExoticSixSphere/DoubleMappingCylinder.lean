import Wikipedia.HopfProblem.OrbitPairMappingCylinderCofibration

/-!
# The actual double mapping cylinder of a span

Two native topological pushouts attach the zero end of a cylinder to
the right space and its one end to the left space. Maps glue from the
two ends and the intervening cylinder, with their exact endpoint
compatibilities retained. No homotopy-pushout equivalence is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)

def space : TopCat.{u} := pushout e (MappingCylinder.source f)

def left : X ⟶ space e f := pushout.inl e (MappingCylinder.source f)

def middle : MappingCylinder.space f ⟶ space e f := pushout.inr e (MappingCylinder.source f)

def right : Y ⟶ space e f := MappingCylinder.target f ≫ middle e f

def tube : TopCat.of (I × A) ⟶ space e f := MappingCylinder.cylinder f ≫ middle e f

theorem square : IsPushout e (MappingCylinder.source f) (left e f) (middle e f) :=
  IsPushout.of_hasPushout _ _

theorem tube_zero (a : A) : tube e f (0, a) = right e f (f a) := by
  have h : MappingCylinder.cylinder f (0, a) = MappingCylinder.target f (f a) :=
    (congrArg (fun m ↦ m a) (MappingCylinder.square f).w).symm
  exact congrArg (middle e f) h

theorem tube_one (a : A) : tube e f (1, a) = left e f (e a) :=
  (congrArg (fun m ↦ m a) (square e f).w).symm

theorem jointly_surjective (p : space e f) :
    (∃ x, left e f x = p) ∨ (∃ y, right e f y = p) ∨ (∃ t a, tube e f (t, a) = p) := by
  obtain (⟨x, rfl⟩ | ⟨m, rfl⟩) := PushoutHomotopy.jointly_surjective (square e f) p
  · exact Or.inl ⟨x, rfl⟩
  · obtain (⟨y, rfl⟩ | ⟨⟨t, a⟩, rfl⟩) :=
      PushoutHomotopy.jointly_surjective (MappingCylinder.square f) m
    · exact Or.inr (Or.inl ⟨y, rfl⟩)
    · exact Or.inr (Or.inr ⟨t, a, rfl⟩)

variable {Z : TopCat.{u}} (G : C(Y, Z)) (H : C(I × A, Z))
    (h0 : ∀ a, H (0, a) = G (f a))

include h0 in
theorem middle_compatible : f ≫ TopCat.ofHom G =
    HomotopyExtension.cylinderEndpoint A 0 ≫ TopCat.ofHom H := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  exact (h0 a).symm

def glueMiddle : MappingCylinder.space f ⟶ Z :=
  (MappingCylinder.square f).desc (TopCat.ofHom G) (TopCat.ofHom H) (middle_compatible f G H h0)

theorem target_glueMiddle : MappingCylinder.target f ≫ glueMiddle f G H h0 = TopCat.ofHom G :=
  (MappingCylinder.square f).inl_desc _ _ (middle_compatible f G H h0)

theorem cylinder_glueMiddle : MappingCylinder.cylinder f ≫ glueMiddle f G H h0 = TopCat.ofHom H :=
  (MappingCylinder.square f).inr_desc _ _ (middle_compatible f G H h0)

variable (F : C(X, Z)) (h1 : ∀ a, H (1, a) = F (e a))

include h1 in
theorem outer_compatible : e ≫ TopCat.ofHom F = MappingCylinder.source f ≫ glueMiddle f G H h0 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  have ht : glueMiddle f G H h0 (MappingCylinder.cylinder f (1, a)) = H (1, a) :=
    congrArg (fun m ↦ m (1, a)) (cylinder_glueMiddle f G H h0)
  exact (h1 a).symm.trans ht.symm

def glue : space e f ⟶ Z :=
  (square e f).desc (TopCat.ofHom F) (glueMiddle f G H h0) (outer_compatible e f G H h0 F h1)

theorem left_glue : left e f ≫ glue e f G H h0 F h1 = TopCat.ofHom F :=
  (square e f).inl_desc _ _ (outer_compatible e f G H h0 F h1)

theorem middle_glue : middle e f ≫ glue e f G H h0 F h1 = glueMiddle f G H h0 :=
  (square e f).inr_desc _ _ (outer_compatible e f G H h0 F h1)

theorem right_glue : right e f ≫ glue e f G H h0 F h1 = TopCat.ofHom G := by
  rw [right, Category.assoc, middle_glue, target_glueMiddle]

theorem tube_glue : tube e f ≫ glue e f G H h0 F h1 = TopCat.ofHom H := by
  rw [tube, Category.assoc, middle_glue, cylinder_glueMiddle]

end NoExoticSixSphere.DoubleMappingCylinder
