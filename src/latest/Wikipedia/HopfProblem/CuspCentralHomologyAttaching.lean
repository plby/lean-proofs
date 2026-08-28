import Wikipedia.HopfProblem.CuspCentralHomologyBoundaryH1
import Wikipedia.HopfProblem.CuspCentralHomologyPhaseActionBoundary
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCross

/-!
# The genuine central-boundary attaching map kills positive-degree homology

The boundary attaching map is the actual compact-phase action on its
actual direction loop.  The loop has zero first homology in the double
locus, and its fixed-parameter phase orbit has an explicit nullhomotopy
there.  The proved integral circle-product decomposition and genuine
cross-product naturality therefore make every positive-degree attaching
map vanish.  No attaching matrix or vanishing premise is assumed.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace SingularMayerVietoris

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))

/-- The orbit in the general circle-product calculation is exactly the
already constructed actual phase orbit, including its chosen base point. -/
theorem boundaryPhaseAction_parametrizedOrbit :
    circleParametrizedOrbit (boundaryPhaseActionMap C ε hε hC) (boundaryLoop C ε hε) =
      boundaryPhaseOrbit C ε hε := by
  apply ContinuousMap.ext
  intro u
  exact (circleBoundaryCellMap_phaseAction C ε hε u 1).symm

variable (hR : SmallDrift C ε)

include hε1 hC hR in
/-- The actual attaching map of the constructed open cover induces zero
on all positive-degree integral singular homology groups. -/
theorem circleBoundaryCellMap_homology_eq_zero (n : ℕ) :
    singularHomologyMap (circleBoundaryCellMap C ε hε) (n + 1) = 0 := by
  rw [circleBoundaryCellMap_eq_phaseAction C ε hε hC]
  change singularHomologyMap
    (circleParametrizedMap (boundaryPhaseActionMap C ε hε hC) (boundaryLoop C ε hε))
      (n + 1) = 0
  apply circleParametrizedHomologyMap_eq_zero_of_nullhomotopic
  · exact boundaryLoop_homology_one_eq_zero C ε hε hε1 hC hR
  · rw [boundaryPhaseAction_parametrizedOrbit]
    exact boundaryPhaseOrbit_nullhomotopic C ε hε

include hε1 hC hR in
theorem circleBoundaryCellMap_homology_one_eq_zero :
    singularHomologyMap (circleBoundaryCellMap C ε hε) 1 = 0 :=
  circleBoundaryCellMap_homology_eq_zero C ε hε hε1 hC hR 0

include hε1 hC hR in
theorem circleBoundaryCellMap_homology_two_eq_zero :
    singularHomologyMap (circleBoundaryCellMap C ε hε) 2 = 0 :=
  circleBoundaryCellMap_homology_eq_zero C ε hε hε1 hC hR 1

end Wikipedia.HopfProblem.CuspCentralHomology
