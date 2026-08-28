import Wikipedia.HopfProblem.OrbitPairMappingCylinderCofibration

/-!
# Exact evaluations of the native mapping-cylinder deformation

These formulas retain the source and target maps of the actual pushout.
They allow a boundary homotopy to be matched to the deformation before
gluing it through a further pushout.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

theorem deformation_inr {S A B P : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {i : A ⟶ P} {j : B ⟶ P} (hP : IsPushout f g i j) (R : P ⟶ A) (r : B ⟶ S)
    (hi : i ≫ R = 𝟙 _) (hj : j ≫ R = r ≫ f)
    (H : (ContinuousMap.id B).HomotopyRel (r ≫ g).hom (Set.range g)) (t : I) (b : B) :
    deformation hP R r hi hj H (t, j b) = j (H (t, b)) :=
  glue_inr hP (baseDeformation R hi) (cellDeformation hP R r hj H)
    (deformations_compatible hP R r hi hj H) t b

end Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

namespace Wikipedia.HopfProblem.OrbitPair.MappingCylinder

variable {A B : TopCat.{u}} (f : A ⟶ B)

theorem cylinder_zero (a : A) : cylinder f (0, a) = target f (f a) :=
  (congrArg (fun m ↦ m a) (square f).w).symm

theorem projection_target (b : B) : projection f (target f b) = b :=
  congrArg (fun m ↦ m b) (target_projection f)

theorem projection_cylinder (t : I) (a : A) : projection f (cylinder f (t, a)) = f a :=
  congrArg (fun m ↦ m (t, a)) (cylinder_projection f)

theorem deformation_target (t : I) (b : B) : deformation f (t, target f b) = target f b :=
  (deformation f).eq_fst t ⟨b, rfl⟩

theorem deformation_cylinder (t s : I) (a : A) :
    deformation f (t, cylinder f (s, a)) = cylinder f (σ t * s, a) :=
  PushoutHomotopy.deformation_inr (square f) (projection f)
    (TopCat.ofHom (ContinuousMap.snd : C(I × A, A)))
    (target_projection f) (cylinder_projection f) (cylinderDeformation A) t (s, a)

theorem deformation_source (t : I) (a : A) :
    deformation f (t, source f a) = cylinder f (σ t, a) := by
  change deformation f (t, cylinder f (1, a)) = _
  rw [deformation_cylinder, mul_one]

theorem projection_deformation (t : I) (m : space f) :
    projection f (deformation f (t, m)) = projection f m := by
  obtain (⟨b, rfl⟩ | ⟨p, rfl⟩) := PushoutHomotopy.jointly_surjective (square f) m
  · rw [deformation_target]
  · rw [deformation_cylinder, projection_cylinder, projection_cylinder]

end Wikipedia.HopfProblem.OrbitPair.MappingCylinder
