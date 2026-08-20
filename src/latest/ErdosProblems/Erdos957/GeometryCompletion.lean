/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.Case4KernelAggregation
import ErdosProblems.Erdos957.GeometryTransfer
import ErdosProblems.Erdos957.WeightedCompletion
import ErdosProblems.Erdos957.WeightedRoleCollisions

/-!
# Final geometric completion for Erdős problem 957

This leaf module isolates the last composition step.  The geometric work is
expressed by the two exact residual records for the produced dependent row
family; once those records are supplied, the checked role-collision assembly
and the source-empty branch yield `GeometryProducesTransfer`.
-/

open Erdos957
open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957RoleCollisions

namespace Erdos957GeometryCompletion

noncomputable section

/-- The two produced residual kernels are the exact final inputs to the
paper-style recipient-side collision argument. -/
theorem geometryProducesTransfer_of_residuals
    (case2 : ∀ {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
      (R : Erdos957.RadiallySortedCyclicHullOrder A)
      (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
      (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L)),
      Erdos957Case2SecondaryNoThree.Case2SecondarySameSideResiduals
        (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
        (F := Erdos957DirectSameSide.ProducedFrame hA R L)
        (Erdos957DirectSameSide.ProducedRows hA R L W))
    (case4 : ∀ {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
      (R : Erdos957.RadiallySortedCyclicHullOrder A)
      (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
      (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L)),
      Erdos957Case4KernelAggregation.Case4SplitRightResidualKernels
        (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
        (F := Erdos957DirectSameSide.ProducedFrame hA R L)
        (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
          hA R L W)) :
    GeometryProducesTransfer :=
  Erdos957GeometryTransfer.geometryProducesTransfer_of_nonempty_roleCollisionWitnesses
    (by
      intro A hA R L W _hsource
      let rows := Erdos957DirectSameSide.ProducedRows hA R L W
      let hlocal := localCasesOfRealizedRows
        (F := Erdos957DirectSameSide.ProducedFrame hA R L) rows
      refine ⟨hlocal, ⟨?_⟩⟩
      exact Erdos957Case4KernelAggregation.producedRoleCollisionWitnesses
        hA R L W (case2 hA R L W) (case4 hA R L W))

/-- Honest weight-aware completion.  This is the final route used by the
public theorem: legitimate half-plus-half collisions are retained, and the
geometric residual record supplies only the sharp three- and four-source
capacity statements needed by `WeightedCollisionWitnesses`. -/
theorem geometryProducesTransfer_of_weighted_residuals
    (residuals : ∀ {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
      (R : Erdos957.RadiallySortedCyclicHullOrder A)
      (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
      (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L)),
      Erdos957WeightedRoleCollisions.WeightedRoleCollisionResiduals
        (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
        (F := Erdos957DirectSameSide.ProducedFrame hA R L)
        (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
          hA R L W)) :
    GeometryProducesTransfer :=
  Erdos957GeometryTransfer.geometryProducesTransfer_of_nonempty_weightedCollisionWitnesses
    (by
      intro A hA R L W _hsource
      let rows := Erdos957DirectSameSide.ProducedRows hA R L W
      let hlocal := localCasesOfRealizedRows
        (F := Erdos957DirectSameSide.ProducedFrame hA R L) rows
      refine ⟨hlocal, ⟨?_⟩⟩
      exact Erdos957WeightedRoleCollisions.producedWeightedCollisionWitnesses
        hA R L W (residuals hA R L W))

/-- Final produced weighted assembly with every Case-4 input discharged.
The only remaining geometric parameter is the two-field mixed Case-2
degree-five split record. -/
theorem geometryProducesTransfer_of_case2_split_residuals
    (case2 : ∀ {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
      (R : Erdos957.RadiallySortedCyclicHullOrder A)
      (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
      (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L)),
      Erdos957Case2SecondaryNoThree.Case2SecondarySplitDegreeFiveResiduals
        (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
        (F := Erdos957DirectSameSide.ProducedFrame hA R L)
        (Erdos957DirectSameSide.ProducedRows hA R L W)) :
    GeometryProducesTransfer :=
  geometryProducesTransfer_of_weighted_residuals
    (fun hA R L W ↦
      Erdos957WeightedCompletion.producedWeightedRoleCollisionResiduals_of_case2
        hA R L W (case2 hA R L W))

end

end Erdos957GeometryCompletion

#print axioms Erdos957GeometryCompletion.geometryProducesTransfer_of_residuals
#print axioms Erdos957GeometryCompletion.geometryProducesTransfer_of_weighted_residuals
#print axioms Erdos957GeometryCompletion.geometryProducesTransfer_of_case2_split_residuals
