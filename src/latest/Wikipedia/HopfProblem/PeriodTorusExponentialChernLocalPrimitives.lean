import Wikipedia.HopfProblem.PeriodTorusExponentialChernLocalLogs
import Wikipedia.HopfProblem.ExponentialChernComparisonLocalCochains
import Wikipedia.HopfProblem.ExponentialChernComparisonCochainZero

/-!
# Actual local singular primitives of the factor bundle's winding cochain

The cochains use the actual chart lifts, fixed vertex representatives,
and original factor logarithms.  Their differentials and overlap
differences follow from the genuine covering-edge and group-cocycle
identities.  The later-minus-earlier difference is the differential of
the original holomorphic coordinate logarithm.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open FirstHurewicz PeriodTorusAppellHumbert PeriodTorusLineBundleChernLog
  ConstantSheafSingularComparison ExponentialChernComparison.LocalCochains
  PeriodTorusLineBundle.ChernCocycle

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The actual first inclusion of an original chart overlap. -/
def overlapLeft (p : PeriodDomain) (i j : p.Torus) :
    C(↥(chartCover p i ⊓ chartCover p j), chartCover p i) :=
  ((Opens.toTopCat (TopCat.of p.Torus)).map
    (homOfLE (show chartCover p i ⊓ chartCover p j ≤ chartCover p i from inf_le_left))).hom

/-- The actual second inclusion of the same original overlap. -/
def overlapRight (p : PeriodDomain) (i j : p.Torus) :
    C(↥(chartCover p i ⊓ chartCover p j), chartCover p j) :=
  ((Opens.toTopCat (TopCat.of p.Torus)).map
    (homOfLE (show chartCover p i ⊓ chartCover p j ≤ chartCover p j from inf_le_right))).hom

theorem localEdgeCocycle_overlap_left (p : PeriodDomain) (i j : p.Torus) :
    (localEdgeCocycle p (chartCover p i)).pullback (overlapLeft p i j) =
      localEdgeCocycle p (chartCover p i ⊓ chartCover p j) := by
  apply EdgeCocycle.ext
  intro σ
  rfl

theorem localEdgeCocycle_overlap_right (p : PeriodDomain) (i j : p.Torus) :
    (localEdgeCocycle p (chartCover p j)).pullback (overlapRight p i j) =
      localEdgeCocycle p (chartCover p i ⊓ chartCover p j) := by
  apply EdgeCocycle.ext
  intro σ
  rfl

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The actual local one-cochain from the original lift and factor logarithm. -/
def localPrimitive (i : p.Torus) : Cochains (chartCover p i) (AddCommGrpCat.of ℂ) 1 :=
  logarithmicOneCochain (localEdgeCocycle p (chartCover p i)) (factorCocycle F)
    (liftDisplacement p i) (localLogValue F i) logPeriod

/-- Its genuine differential is the restriction of the original
negative factor-defect cochain with the original exponential period. -/
theorem localPrimitive_d (i : p.Torus) :
    (singularCochainComplex (chartCover p i) (AddCommGrpCat.of ℂ)).d 1 2
      (localPrimitive F i) =
      (singularPullback (AddCommGrpCat.of ℂ) (openInclusion p (chartCover p i))).f 2
        (-periodTwoCochain (latticeEdgeCocycle p) (factorCocycle F) logPeriod) := by
  rw [map_neg, periodTwoCochain_pullback]
  exact logarithmicOneCochain_d_eq_neg (localEdgeCocycle p (chartCover p i))
    (factorCocycle F) (liftDisplacement p i)
    (localEdgeCocycle_eq_displacement p i) (localLogValue F i) logPeriod

/-- On the original overlap, actual restrictions of the later and
earlier local primitives differ by the actual coordinate-log differential. -/
theorem localPrimitive_difference (i j : p.Torus) :
    (cochainPresheaf (TopCat.of p.Torus) (AddCommGrpCat.of ℂ) 1).map
        (homOfLE (show chartCover p i ⊓ chartCover p j ≤ chartCover p j from inf_le_right)).op
          (localPrimitive F j) -
      (cochainPresheaf (TopCat.of p.Torus) (AddCommGrpCat.of ℂ) 1).map
        (homOfLE (show chartCover p i ⊓ chartCover p j ≤ chartCover p i from inf_le_left)).op
          (localPrimitive F i) =
      (singularCochainComplex ↥(chartCover p i ⊓ chartCover p j) (AddCommGrpCat.of ℂ)).d 0 1
        (ExponentialChernComparison.CochainZero.evaluateSections IC p.Torus
          (chartCover p i ⊓ chartCover p j) (coordinateLogSection F i j)) := by
  change (singularPullback (AddCommGrpCat.of ℂ) (overlapRight p i j)).f 1
      (localPrimitive F j) -
    (singularPullback (AddCommGrpCat.of ℂ) (overlapLeft p i j)).f 1
      (localPrimitive F i) = _
  have hj := logarithmicOneCochain_pullback
    (localEdgeCocycle p (chartCover p j)) (factorCocycle F)
    (liftDisplacement p j) (localLogValue F j) logPeriod (overlapRight p i j)
  rw [localEdgeCocycle_overlap_right] at hj
  have hi := logarithmicOneCochain_pullback
    (localEdgeCocycle p (chartCover p i)) (factorCocycle F)
    (liftDisplacement p i) (localLogValue F i) logPeriod (overlapLeft p i j)
  rw [localEdgeCocycle_overlap_left] at hi
  refine (congrArg₂
    (fun a b : Cochains ↥(chartCover p i ⊓ chartCover p j) (AddCommGrpCat.of ℂ) 1 =>
      a - b) hj hi).trans ?_
  have hr : ∀ σ : SingularSimplex ↥(chartCover p i ⊓ chartCover p j) 1,
      localEdgeCocycle p (chartCover p i ⊓ chartCover p j) σ =
        liftDisplacement p i (overlapLeft p i j (vertex σ 1)) -
          liftDisplacement p i (overlapLeft p i j (vertex σ 0)) := by
    intro σ
    exact localEdgeCocycle_eq_displacement p i ((overlapLeft p i j).comp σ)
  have h := logarithmicOneCochain_difference
    (localEdgeCocycle p (chartCover p i ⊓ chartCover p j)) (factorCocycle F)
    (fun x => liftDisplacement p i (overlapLeft p i j x))
    (fun x => liftDisplacement p j (overlapRight p i j x))
    (fun x => Core.deck p i j x) hr (liftDisplacement_overlap p i j)
    (fun σ => deck_constant_on_overlap_edge p i j σ _ _)
    (fun x => localLogValue F i (overlapLeft p i j x))
    (fun x => localLogValue F j (overlapRight p i j x)) logPeriod
  refine h.trans ?_
  apply congrArg ((singularCochainComplex ↥(chartCover p i ⊓ chartCover p j)
    (AddCommGrpCat.of ℂ)).d 0 1)
  apply cochain_ext ↥(chartCover p i ⊓ chartCover p j) (AddCommGrpCat.of ℂ) 0
  intro σ
  rw [ExponentialChernComparison.LocalCochains.pointCochain_simplex,
    ExponentialChernComparison.CochainZero.evaluateSections_simplex]
  exact (coordinateLog_eq_local_difference F i j (vertex σ 0)).symm

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
