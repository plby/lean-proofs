import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass

/-!
# The actual integral singular homology of the circle

The explicit circle-product splitting, applied to a point, computes the
actual homology of `AddCircle 1`: degree zero and degree one are integral
coefficient modules, and every higher-degree homology group is zero.
The degree-one marking uses the signed connecting coordinate from the
actual two-arc Mayer–Vietoris sequence.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris CircleTopology

private def trivialFirstEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Module ℤ B] [Subsingleton A] : (A × B) ≃ₗ[ℤ] B :=
  ({ toFun a := a.2
     invFun b := (0, b)
     left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
     right_inv _ := rfl
     map_add' _ _ := rfl } : (A × B) ≃+ B).toIntLinearEquiv

/-- Degree-zero actual circle homology, with the canonical augmentation marking. -/
abbrev circleHomologyZeroEquiv : SingularHomology Circle 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv Circle

/-- The actual circle has one integral first-homology generator, marked
by the negative lower-component connecting coordinate. -/
def circleHomologyOneEquiv : SingularHomology Circle 1 ≃ₗ[ℤ] ℤ := by
  letI := point_homology_subsingleton 1 (by decide)
  exact
    ((homeomorphHomologyEquiv (Homeomorph.prodUnique Circle Unit).symm 1).trans
      (circleProductHomologyEquiv Unit 0)).trans
      ((trivialFirstEquiv (SingularHomology Unit 1) (SingularHomology Unit 0)).trans
        pointHomologyZeroEquiv)

/-- This marking is literally the actual signed connecting map, followed
by the canonical augmentation of the point's degree-zero homology. -/
theorem circleHomologyOneEquiv_apply (a : SingularHomology Circle 1) :
    circleHomologyOneEquiv a =
      pointHomologyZeroEquiv
        (circleBoundary Unit 0
          (homeomorphHomologyEquiv (Homeomorph.prodUnique Circle Unit).symm 1 a)) := rfl

/-- Every actual circle homology group above degree one is trivial. -/
theorem circle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology Circle (n + 2)) := by
  let := point_homology_subsingleton (n + 2) (Nat.succ_ne_zero _)
  let := point_homology_subsingleton (n + 1) (Nat.succ_ne_zero _)
  exact
    ((homeomorphHomologyEquiv (Homeomorph.prodUnique Circle Unit).symm (n + 2)).trans
      (circleProductHomologyEquiv Unit (n + 1))).injective.subsingleton

theorem circle_homology_isZero (n : ℕ) : IsZero (SingularHomology Circle (n + 2)) := by
  let := circle_homology_subsingleton n
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual higher circle homology is explicitly equivalent to the zero free module. -/
def circleHomologyHigherEquivZero (n : ℕ) :
    SingularHomology Circle (n + 2) ≃ₗ[ℤ] (Fin 0 → ℤ) := by
  letI := circle_homology_subsingleton n
  exact LinearEquiv.ofSubsingleton _ _

/-- The full actual integral singular homology calculation for the circle. -/
theorem circle_homology :
    Nonempty (SingularHomology Circle 0 ≃ₗ[ℤ] ℤ) ∧
      Nonempty (SingularHomology Circle 1 ≃ₗ[ℤ] ℤ) ∧
      ∀ n, Subsingleton (SingularHomology Circle (n + 2)) :=
  ⟨⟨circleHomologyZeroEquiv⟩, ⟨circleHomologyOneEquiv⟩, circle_homology_subsingleton⟩

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
