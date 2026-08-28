import Wikipedia.NoExoticSixSphere.DeformationRetractionNativeHomotopy
import Wikipedia.NoExoticSixSphere.MappingCylinderHomology
import Wikipedia.HopfProblem.OrbitPairMappingCylinderEvaluation
import Wikipedia.HopfProblem.OrbitPairHigherHomotopyHomeomorph

/-!
# Transport from the actual mapping-cylinder inclusion to the original native map

The projection's native map is bijective at every cylinder point by its
actual contractible fibers. The source homeomorphism and projection
factor the original map exactly. The factorization is checked on native
cube representatives, including the target-basepoint equality.
-/

noncomputable section

open CategoryTheory
open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.MappingCylinderNativeHomotopy

theorem map_bijective_of_eq_target {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (d : ℕ) (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (hf : Function.Bijective (HigherHomotopy.map (N := Fin d) f (y := x) rfl)) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) f h) := by
  subst y
  exact hf

variable {A B : TopCat.{0}} (f : A ⟶ B)

theorem projection_pi_bijective (d : ℕ) (hd : 0 < d) (m : MappingCylinder.space f) :
    Function.Bijective
      (HigherHomotopy.map (N := Fin d) (MappingCylinder.projection f).hom (y := m) rfl) :=
  DeformationRetractionNativeHomotopy.map_bijective
    (MappingCylinder.projection f).hom (MappingCylinder.target f).hom
    (MappingCylinder.projection_target f) (MappingCylinder.deformation f) d hd m

theorem source_projection_point (x : A) :
    MappingCylinder.projection f (MappingCylinder.source f x) = f x :=
  congrArg (fun g : A ⟶ B ↦ g x) (MappingCylinder.source_projection f)

theorem source_pi_bijective (d : ℕ)
    (hi : ∀ a : MappingCylinderHomology.sourceImage f, Function.Bijective
      (HigherHomotopy.map (N := Fin d)
        (subtypeInclusion (MappingCylinderHomology.sourceImage f)) (y := a) rfl)) (x : A) :
    Function.Bijective
      (HigherHomotopy.map (N := Fin d) (MappingCylinder.source f).hom (y := x) rfl) := by
  let E := MappingCylinderHomology.sourceHomeomorph f
  have he := (HigherHomotopyCoordinates.homeomorphEquiv (Fin d) E x).bijective
  have hcomp := (hi (E x)).comp he
  have hm :
      HigherHomotopy.map (N := Fin d) (subtypeInclusion (MappingCylinderHomology.sourceImage f))
          (y := E x) rfl ∘ HigherHomotopy.map (E : C(A, MappingCylinderHomology.sourceImage f))
            (y := x) rfl =
        HigherHomotopy.map (N := Fin d) (MappingCylinder.source f).hom (y := x) rfl := by
    funext c
    refine Quotient.inductionOn c fun p ↦ ?_
    rfl
  exact hm ▸ hcomp

theorem original_pi_bijective (d : ℕ) (hd : 0 < d)
    (hi : ∀ a : MappingCylinderHomology.sourceImage f, Function.Bijective
      (HigherHomotopy.map (N := Fin d)
        (subtypeInclusion (MappingCylinderHomology.sourceImage f)) (y := a) rfl)) (x : A) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) f.hom (y := x) rfl) := by
  have hs := source_pi_bijective f d hi x
  have hp := map_bijective_of_eq_target d (MappingCylinder.projection f).hom
    (source_projection_point f x)
    (projection_pi_bijective f d hd (MappingCylinder.source f x))
  have hm : HigherHomotopy.map (N := Fin d) (MappingCylinder.projection f).hom
        (source_projection_point f x) ∘
          HigherHomotopy.map (N := Fin d) (MappingCylinder.source f).hom (y := x) rfl =
      HigherHomotopy.map (N := Fin d) f.hom (y := x) rfl := by
    funext c
    refine Quotient.inductionOn c fun p ↦ ?_
    apply congrArg (fun q : GenLoop (Fin d) B (f x) ↦ (Quotient.mk' q : π_ d B (f x)))
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact source_projection_point f (p t)
  exact hm ▸ hp.comp hs

end NoExoticSixSphere.MappingCylinderNativeHomotopy
