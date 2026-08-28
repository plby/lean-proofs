import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorusOneProjection
import Wikipedia.HopfProblem.SingularCohomologyCup
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupPairs

/-!
# Native cup products and the central base torus

The cup product below is the Alexander--Whitney operation on the actual
singular cochain cohomology.  Its comparison with the original marking
uses naturality for the independently prescribed collapse, transported
through the same genuine fibre homeomorphism.  The positive period-pair
calculation identifies the geometric base-torus dual with the actual cup
of the two central one-classes; no complex-orientation comparison is used.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction SingularCohomologyFree SingularCohomologyCup
open PeriodTorusHigherHomology CuspCentralHomology.SpecializationModel
open PeriodTorusCohomologyCup

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- The actual marked collapse preserves the native cup product of the central one-classes. -/
theorem centralBaseOneClass_cup_markedPullback (i j : Fin 2) :
    singularCohomologyPullback (markedCollapse C r hr) 2
        (cupProduct (QuotientCentralFibre C r) 1 1
          (centralBaseOneClass C r hr hC i) (centralBaseOneClass C r hr hC j)) =
      cupProduct (ProductTorus 4) 1 1
        (coordinateTorusH1DualClass (Fin.castLE (by decide) i))
        (coordinateTorusH1DualClass (Fin.castLE (by decide) j)) := by
  rw [cupProduct_pullback (markedCollapse C r hr) 1 1,
    centralBaseOneClass_markedPullback,
    centralBaseOneClass_markedPullback]

/-- The geometric base-torus dual is the genuine cup of the two original central base classes. -/
theorem baseTorusDualClass_eq_cup :
    baseTorusDualClass C r hr hC =
      cupProduct (QuotientCentralFibre C r) 1 1
        (centralGammaClass C r hr hC) (centralUClass C r hr hC) := by
  apply markedPullback_injective C r hr hC 2
  rw [baseTorusDualClass_markedPullback, centralGammaClass, centralUClass,
    centralBaseOneClass_cup_markedPullback]
  exact coordinateDualCup_gamma_u.symm

section Pullback

variable {X : Type} [TopologicalSpace X] (f : C(X, QuotientCentralFibre C r))

/-- The identity pulls back along every actual continuous map, including the prescribed collapse. -/
theorem baseTorusDualClass_pullback_eq_cup :
    singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC) =
      cupProduct X 1 1
        (singularCohomologyPullback f 1 (centralGammaClass C r hr hC))
        (singularCohomologyPullback f 1 (centralUClass C r hr hC)) := by
  rw [baseTorusDualClass_eq_cup, cupProduct_pullback f 1 1]

end Pullback

section Transport

variable {X : Type} [TopologicalSpace X] (E : ProductTorus 4 ≃ₜ X)
    (f : C(X, QuotientCentralFibre C r))
    (h : (markedCollapse C r hr).Homotopic (f.comp (E : C(ProductTorus 4, X))))

include h

/-- The actual complex-fibre comparison preserves both factors and their native cup product
in one and the same original marking. -/
theorem centralBaseOneClass_cup_specialization_pullback (i j : Fin 2) :
    homeomorphCohomologyEquiv E 2
        (singularCohomologyPullback f 2
          (cupProduct (QuotientCentralFibre C r) 1 1
            (centralBaseOneClass C r hr hC i) (centralBaseOneClass C r hr hC j))) =
      cupProduct (ProductTorus 4) 1 1
        (coordinateTorusH1DualClass (Fin.castLE (by decide) i))
        (coordinateTorusH1DualClass (Fin.castLE (by decide) j)) := by
  rw [markedSpecialization_pullback C r hr E f h 2,
    centralBaseOneClass_cup_markedPullback C r hr hC i j]

/-- The source's displayed `γu` is the genuine degree-one cup in the same actual fibre marking. -/
theorem baseTorusDualClass_specialization_eq_nativeCup :
    homeomorphCohomologyEquiv E 2
        (singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC)) =
      cupProduct (ProductTorus 4) 1 1
        (coordinateTorusH1DualClass 0) (coordinateTorusH1DualClass 1) := by
  rw [baseTorusDualClass_eq_cup, centralGammaClass, centralUClass,
    centralBaseOneClass_cup_specialization_pullback C r hr hC E f h 0 1]
  rfl

/-- The equality holds before replacing the two actual pullback factors
by their coordinates. -/
theorem baseTorusDualClass_specialization_cup_factors :
    homeomorphCohomologyEquiv E 2
        (singularCohomologyPullback f 2 (baseTorusDualClass C r hr hC)) =
      cupProduct (ProductTorus 4) 1 1
        (homeomorphCohomologyEquiv E 1
          (singularCohomologyPullback f 1 (centralGammaClass C r hr hC)))
        (homeomorphCohomologyEquiv E 1
          (singularCohomologyPullback f 1 (centralUClass C r hr hC))) := by
  rw [centralGammaClass_specialization_pullback C r hr hC E f h,
    centralUClass_specialization_pullback C r hr hC E f h,
    baseTorusDualClass_specialization_eq_nativeCup C r hr hC E f h]

end Transport

end Wikipedia.HopfProblem.CuspCentralCohomology
