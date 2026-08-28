import Wikipedia.NoExoticSixSphere.DoubleMappingCylinder

/-!
# Jointly continuous families on the actual double mapping cylinder

Currying into compact-open path space lets the ordinary gluing theorem
assemble homotopies without assuming that arbitrary products preserve
topological pushouts. The family is recovered exactly on all three
original pieces.
-/

noncomputable section

universe u

open CategoryTheory Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y Z : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)
    (F : C(I × X, Z)) (G : C(I × Y, Z)) (H : C(I × (I × A), Z))
    (h0 : ∀ s a, H (s, (0, a)) = G (s, f a))
    (h1 : ∀ s a, H (s, (1, a)) = F (s, e a))

def tubePaths : TopCat.of (I × A) ⟶ TopCat.of C(I, Z) :=
  PushoutHomotopy.familyPaths (A := TopCat.of (I × A)) H

include h0 in
theorem family_zero_compatible (a : A) :
    tubePaths H (0, a) = PushoutHomotopy.familyPaths G (f a) := by
  apply ContinuousMap.ext
  intro s
  exact h0 s a

include h1 in
theorem family_one_compatible (a : A) :
    tubePaths H (1, a) = PushoutHomotopy.familyPaths F (e a) := by
  apply ContinuousMap.ext
  intro s
  exact h1 s a

def familyMap : space e f ⟶ TopCat.of C(I, Z) :=
  glue e f (PushoutHomotopy.familyPaths G).hom (tubePaths H).hom
    (family_zero_compatible f G H h0) (PushoutHomotopy.familyPaths F).hom
    (family_one_compatible e F H h1)

theorem left_familyMap : left e f ≫ familyMap e f F G H h0 h1 =
    PushoutHomotopy.familyPaths F :=
  left_glue e f (PushoutHomotopy.familyPaths G).hom (tubePaths H).hom
    (family_zero_compatible f G H h0) (PushoutHomotopy.familyPaths F).hom
    (family_one_compatible e F H h1)

theorem right_familyMap : right e f ≫ familyMap e f F G H h0 h1 =
    PushoutHomotopy.familyPaths G :=
  right_glue e f (PushoutHomotopy.familyPaths G).hom (tubePaths H).hom
    (family_zero_compatible f G H h0) (PushoutHomotopy.familyPaths F).hom
    (family_one_compatible e F H h1)

theorem tube_familyMap : tube e f ≫ familyMap e f F G H h0 h1 =
    tubePaths H :=
  tube_glue e f (PushoutHomotopy.familyPaths G).hom (tubePaths H).hom
    (family_zero_compatible f G H h0) (PushoutHomotopy.familyPaths F).hom
    (family_one_compatible e F H h1)

def family : C(I × space e f, Z) :=
  (familyMap e f F G H h0 h1).hom.uncurry.comp ⟨Prod.swap, continuous_swap⟩

theorem family_left (s : I) (x : X) : family e f F G H h0 h1 (s, left e f x) = F (s, x) :=
  congrArg (fun m ↦ m x s) (left_familyMap e f F G H h0 h1)

theorem family_right (s : I) (y : Y) : family e f F G H h0 h1 (s, right e f y) = G (s, y) :=
  congrArg (fun m ↦ m y s) (right_familyMap e f F G H h0 h1)

theorem family_tube (s t : I) (a : A) :
    family e f F G H h0 h1 (s, tube e f (t, a)) = H (s, (t, a)) :=
  congrArg (fun m ↦ m (t, a) s) (tube_familyMap e f F G H h0 h1)

end NoExoticSixSphere.DoubleMappingCylinder
