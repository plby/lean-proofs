import ErdosProblems.Erdos957.Case2WeightedAssembly
import ErdosProblems.Erdos957.Case4ProducedResiduals
import ErdosProblems.Erdos957.WeightedRoleCollisions

/-!
# Final weight-aware residual aggregation for Erdős 957

This leaf keeps the two genuinely geometric inputs explicit: the two
degree-five mixed Case-2 triples and the Case-4 residual records.  All
source-count, quadruple-capacity, and direct-role dispatch is supplied by
checked generic theorems.
-/

noncomputable section

namespace Erdos957WeightedCompletion

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CollisionInstantiation
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions
open Erdos957Case2SecondaryNoThree
open Erdos957Case4KernelAggregation
open Erdos957Case4SplitClassification
open Erdos957WeightedRoleCollisions

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- The exact componentwise constructor for the final weight-aware role
record.  In particular it never assumes the false mixed Case-2/Case-4
pairwise uniqueness statement. -/
theorem weightedRoleCollisionResiduals_of_components
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (direct_direct : ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v),
      IsDirectTargetRole S.target.role →
      IsDirectTargetRole T.target.role →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t)
    (case2 : Case2SecondarySplitDegreeFiveResiduals (F := F) Q.rows)
    (case4 : Case4SplitRightResidualKernels Q)
    (case4_weighted : Case4WeightedCollisionResiduals Q) :
    WeightedRoleCollisionResiduals Q where
  case2_degree_five :=
    case2SecondaryDegreeFiveResiduals_of_split_residuals hA case2
  case4_weighted := case4_weighted
  case2_quadruple_fits :=
    Erdos957Case2WeightedAssembly.case2AnchoredQuadrupleFits_of_pairwise_and_split_residuals
      hA Q locality direct_direct case4 case2
  case2_same_association_triple :=
    Erdos957Case2WeightedAssembly.case2AnchoredSameAssociationTriple_of_pairwise
      Q locality direct_direct case4

/-- Produced weighted role residuals with the entire Case-4 side
discharged.  The sole remaining input is the genuine mixed Case-2 split
degree-five record. -/
noncomputable def producedWeightedRoleCollisionResiduals_of_case2
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L))
    (case2 : Case2SecondarySplitDegreeFiveResiduals
      (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
      (F := Erdos957DirectSameSide.ProducedFrame hA R L)
      (Erdos957DirectSameSide.ProducedRows hA R L W)) :
    WeightedRoleCollisionResiduals
      (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
      (F := Erdos957DirectSameSide.ProducedFrame hA R L)
      (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
        hA R L W) :=
  weightedRoleCollisionResiduals_of_components hA
    (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
      hA R L W)
    ⟨Erdos957GeometryTransfer.producedCyclicWindowGeometry hA R L W⟩
    (Erdos957DirectSameSide.produced_direct_direct hA R L W)
    case2
    (Erdos957Case4ProducedResiduals.producedCase4SplitRightResidualKernels
      hA R L W)
    (Erdos957Case4ProducedResiduals.producedCase4WeightedCollisionResiduals
      hA R L W)

end Erdos957WeightedCompletion

#print axioms Erdos957WeightedCompletion.weightedRoleCollisionResiduals_of_components
#print axioms Erdos957WeightedCompletion.producedWeightedRoleCollisionResiduals_of_case2
