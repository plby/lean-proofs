import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImagePeriodClasses

/-!
# Explicit actual lifts of all degree-one fibre classes

The genuine period-character classes give a right inverse to the
actual stalk-to-fibre evaluation as additive groups. The formula uses
the inverse of the already proved original Dolbeault marking. This
proves surjectivity, not injectivity of the raw stalk map: base change
and local freeness require the original base-function module structure
and residue-field specialization.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage

open PeriodFamilyHolomorphicCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Literal constant-character stalk classes lift prescribed native fibre coordinates. -/
def oneFibreLift (P : HolomorphicPeriodMap V B) (b : B) :
    (Fin 2 → ℂ) →+ ↥(higherDirectImageStalk P b 1) :=
  (firstPeriodStalkClass P b).comp
    (-(MarkedLinear.firstDbarEquiv (P.point b)).symm.toLinearMap).toAddMonoidHom

@[simp] theorem oneFibreLift_apply (P : HolomorphicPeriodMap V B) (b : B) (c : Fin 2 → ℂ) :
    oneFibreLift P b c =
      firstPeriodStalkClass P b (-(MarkedLinear.firstDbarEquiv (P.point b)).symm c) := rfl

/-- The original marked cohomology class, not merely its coordinate vector,
has this explicit actual higher-direct-image stalk lift. -/
def cohomologyFibreLift (P : HolomorphicPeriodMap V B) (b : B) :
    PeriodTorusHolomorphicCohomology.H (P.point b) 1 →+
      ↥(higherDirectImageStalk P b 1) :=
  (oneFibreLift P b).comp
    (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)).toAddEquiv.toAddMonoidHom

@[simp] theorem cohomologyFibreLift_apply (P : HolomorphicPeriodMap V B) (b : B)
    (a : PeriodTorusHolomorphicCohomology.H (P.point b) 1) :
    cohomologyFibreLift P b a =
      oneFibreLift P b (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b) a) := rfl

variable [T2Space B]

/-- The actual fibre coordinates of the literal lift are exactly the prescribed pair. -/
theorem oneFibreCoordinates_oneFibreLift (P : HolomorphicPeriodMap V B) (b : B)
    (c : Fin 2 → ℂ) :
    oneFibreCoordinates P b (oneFibreLift P b c) = c := by
  rw [oneFibreLift_apply, oneFibreCoordinates_firstPeriodStalkClass,
    map_neg, LinearEquiv.apply_symm_apply, neg_neg]

/-- Evaluation of the explicit native lift recovers the original native fibre Ext class. -/
theorem fibreEvaluation_cohomologyFibreLift (P : HolomorphicPeriodMap V B) (b : B)
    (a : PeriodTorusHolomorphicCohomology.H (P.point b) 1) :
    fibreEvaluation P b 1 (cohomologyFibreLift P b a) = a := by
  apply (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)).injective
  exact oneFibreCoordinates_oneFibreLift P b
    (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b) a)

/-- Every actual degree-one fibre cohomology class is realized by a
genuine germ of the original first higher-direct-image sheaf. -/
theorem fibreEvaluation_one_surjective (P : HolomorphicPeriodMap V B) (b : B) :
    Function.Surjective (fibreEvaluation P b 1) := by
  intro a
  exact ⟨cohomologyFibreLift P b a, fibreEvaluation_cohomologyFibreLift P b a⟩

/-- The original coordinate evaluation is surjective by its genuine explicit lifts. -/
theorem oneFibreCoordinates_surjective (P : HolomorphicPeriodMap V B) (b : B) :
    Function.Surjective (oneFibreCoordinates P b) := by
  intro c
  exact ⟨oneFibreLift P b c, oneFibreCoordinates_oneFibreLift P b c⟩

/-- The two literal constant-character classes remain independent in the actual stalk. -/
theorem firstPeriodStalkClass_injective (P : HolomorphicPeriodMap V B) (b : B) :
    Function.Injective (firstPeriodStalkClass P b) := by
  intro c d h
  apply (MarkedLinear.firstDbarEquiv (P.point b)).injective
  apply neg_injective
  exact (oneFibreCoordinates_firstPeriodStalkClass P b c).symm.trans
    ((congrArg (oneFibreCoordinates P b) h).trans
      (oneFibreCoordinates_firstPeriodStalkClass P b d))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage
