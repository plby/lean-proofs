import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Projections of the actual homology cross product

Projection onto the right factor kills a product with a positive-dimensional
left class: it factors through the actual vanishing of `H₁` of a point. The
same argument applies to the left projection when the right degree is positive.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The right projection annihilates the actual cross product with a one-class. -/
theorem crossProductHomology_snd (n : ℕ)
    (a : SingularHomology X 1) (b : SingularHomology Y n) :
    singularHomologyMap (ContinuousMap.snd : C(X × Y, Y)) (n + 1)
      (crossProductHomology X Y n a b) = 0 := by
  let : Subsingleton (SingularHomology Unit 1) := point_homology_subsingleton 1 (by decide)
  let f : C(X, Unit) := ContinuousMap.const X ()
  have hz : singularHomologyMap f 1 a = 0 := Subsingleton.elim _ _
  have hn := crossProductHomology_natural f (ContinuousMap.id Y) n a b
  change singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
      (crossProductHomology X Y n a b) =
    crossProductHomology Unit Y n (singularHomologyMap f 1 a)
      (singularHomologyMap (ContinuousMap.id Y) n b) at hn
  rw [hz, map_zero, LinearMap.zero_apply] at hn
  calc
    _ = singularHomologyMap (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1)
        (singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
          (crossProductHomology X Y n a b)) := by
      exact LinearMap.congr_fun (singularHomologyMap_comp
        (f.prodMap (ContinuousMap.id Y)) (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1))
        (crossProductHomology X Y n a b)
    _ = 0 := by rw [hn, map_zero]

/-- The left projection annihilates a cross product when the right degree is positive. -/
theorem crossProductHomology_fst (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology X 1) (b : SingularHomology Y n) :
    singularHomologyMap (ContinuousMap.fst : C(X × Y, X)) (n + 1)
      (crossProductHomology X Y n a b) = 0 := by
  let : Subsingleton (SingularHomology Unit n) := point_homology_subsingleton n hn
  let g : C(Y, Unit) := ContinuousMap.const Y ()
  have hz : singularHomologyMap g n b = 0 := Subsingleton.elim _ _
  have he := crossProductHomology_natural (ContinuousMap.id X) g n a b
  change singularHomologyMap ((ContinuousMap.id X).prodMap g) (n + 1)
      (crossProductHomology X Y n a b) =
    crossProductHomology X Unit n (singularHomologyMap (ContinuousMap.id X) 1 a)
      (singularHomologyMap g n b) at he
  rw [hz, map_zero] at he
  calc
    _ = singularHomologyMap (ContinuousMap.fst : C(X × Unit, X)) (n + 1)
        (singularHomologyMap ((ContinuousMap.id X).prodMap g) (n + 1)
          (crossProductHomology X Y n a b)) := by
      exact LinearMap.congr_fun (singularHomologyMap_comp
        ((ContinuousMap.id X).prodMap g) (ContinuousMap.fst : C(X × Unit, X)) (n + 1))
        (crossProductHomology X Y n a b)
    _ = 0 := by rw [he, map_zero]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
