import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorusOneClasses
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOneClasses

/-!
# The central one-classes come from the actual base projection

The unique specialization lifts are the pullbacks of the native
coordinate cocycles along the genuine central base projection.  The
proof uses the literal projection of positive vector loops and the
already proved equality of the actual base-projection/collapse maps.
Thus the names `γ` and `u` refer to the original two oriented base
circles, not to an arbitrary basis of a rank-two group.
-/

noncomputable section

open scoped ContDiff ContinuousMap Matrix

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction CuspCentralHomology FirstHurewicz
open SingularCohomologyFree SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusCohomologyCup CuspCentralHomology.SpecializationModel

/-- The geometric projection preserves the actual positive vector-loop homology classes. -/
theorem markedBaseProjection_periodLoop_homology (v : Fin 4 → ℤ) :
    singularHomologyMap markedBaseProjection 1
        (loopHomologyClass (coordinatePeriodLoop 4 v)) =
      loopHomologyClass (coordinatePeriodLoop 2 ![v 0, v 1]) := by
  let q : C(ProductTorus 4, ProductTorus 2) :=
    ⟨fun x i => x (Fin.castLE (by decide) i), by
      apply continuous_pi
      intro i
      exact continuous_apply _⟩
  have hq : markedBaseProjection = q := by
    apply ContinuousMap.ext
    intro x
    funext i
    fin_cases i <;> rfl
  have hp : (coordinatePeriodLoop 4 v).map q.continuous =
      coordinatePeriodLoop 2 ![v 0, v 1] := by
    apply Path.ext
    funext t
    change q (coordinatePeriodLoop 4 v t) = coordinatePeriodLoop 2 ![v 0, v 1] t
    funext i
    fin_cases i <;> simp [q, coordinatePeriodLoop_apply]
  rw [hq, singularHomologyMap_one, inducedHomology_loopHomologyClass, hp]

/-- The genuine two-circle coordinate cocycle pulls back to its original native marked class. -/
theorem markedBaseProjection_pullback_coordinateOneClass (i : Fin 2) :
    singularCohomologyPullback markedBaseProjection 1 (coordinateOneClass 2 i) =
      coordinateTorusH1DualClass (Fin.castLE (by decide) i) := by
  apply (coordinateTorusEvaluationEquiv 1).injective
  apply LinearMap.ext
  intro a
  obtain ⟨v, rfl⟩ := coordinateTorusH1Coordinates.symm.surjective a
  change singularEvaluation (ProductTorus 4) 1
      (singularCohomologyPullback markedBaseProjection 1 (coordinateOneClass 2 i))
        (coordinateTorusH1Coordinates.symm v) =
    singularEvaluation (ProductTorus 4) 1
      (coordinateTorusH1DualClass (Fin.castLE (by decide) i))
        (coordinateTorusH1Coordinates.symm v)
  rw [coordinateTorusH1Coordinates_symm_apply,
    coordinateH1_four_apply (Elliptic.examplePeriod .four),
    singularEvaluation_naturality, markedBaseProjection_periodLoop_homology,
    coordinateOneClass_periodLoop, coordinateTorusH1DualClass_evaluate,
    coordinateTorusH1Coordinates_loop]
  fin_cases i <;> rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- The actual central one-classes are geometrically the pullbacks of the oriented base circles. -/
theorem centralBaseOneClass_eq_projection_pullback (i : Fin 2) :
    centralBaseOneClass C r hr hC i =
      singularCohomologyPullback (baseTorusProjectionMap C r hr hC) 1
        (coordinateOneClass 2 i) := by
  apply markedPullback_injective C r hr hC 1
  rw [centralBaseOneClass_markedPullback]
  change coordinateTorusH1DualClass (Fin.castLE (by decide) i) =
    ((singularCohomologyPullback (markedCollapse C r hr) 1).comp
      (singularCohomologyPullback (baseTorusProjectionMap C r hr hC) 1))
        (coordinateOneClass 2 i)
  rw [← singularCohomologyPullback_comp, baseTorusProjectionMap_comp_markedCollapse,
    markedBaseProjection_pullback_coordinateOneClass]

theorem centralGammaClass_eq_projection_pullback :
    centralGammaClass C r hr hC =
      singularCohomologyPullback (baseTorusProjectionMap C r hr hC) 1
        (coordinateOneClass 2 0) :=
  centralBaseOneClass_eq_projection_pullback C r hr hC 0

theorem centralUClass_eq_projection_pullback :
    centralUClass C r hr hC =
      singularCohomologyPullback (baseTorusProjectionMap C r hr hC) 1
        (coordinateOneClass 2 1) :=
  centralBaseOneClass_eq_projection_pullback C r hr hC 1

end Wikipedia.HopfProblem.CuspCentralCohomology
