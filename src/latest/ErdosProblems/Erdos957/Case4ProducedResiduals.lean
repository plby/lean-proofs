import ErdosProblems.Erdos957.Case4OuterDirect
import ErdosProblems.Erdos957.Case4KernelAggregation

/-!
# The final produced Case-4 residual package

All finite source-position and direct-form branches are discharged here.
The only remaining geometric input is stated at the exact formula level:
the non-hull equilateral proxy of an `OuterDirectFormula` at either of the
two near source slots has the opposite recipient-relative association.
-/

noncomputable section

namespace Erdos957Case4ProducedResiduals

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CollisionInstantiation
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions
open Erdos957Case4CollisionLeaves
open Erdos957DirectSameSide
open Erdos957Case4KernelAggregation
open Erdos957Case4SplitClassification

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- Exact remaining K4 direct geometry after the checked singleton and
paired forms have been removed. -/
def OuterDirectNearKernel
    (Q : CommonCoherentRealizedSourceRows P W F.chart) : Prop :=
  ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htDirect : IsDirectTargetRole T.target.role)
    (O : OuterDirectFormula F.chart (sourceIndex P W t.1 t.property) v
      T.descriptor.association),
    DirectNearTwo (t := t) Q S hsRole →
      S.descriptor.association ≠ T.descriptor.association

/-- The outer-proxy geometry supplies the last direct-form kernel for every
coherent selected row family. -/
theorem outerDirectNearKernel
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart) :
    OuterDirectNearKernel Q := by
  intro s t v S T hsRole htDirect O hnear
  exact Erdos957Case4OuterDirect.outer_direct_near_two_associations_ne
    hA Q S T hsRole htDirect O hnear

/-- The one explicit outer-proxy leaf, together with the checked direct-form
dispatch and the final split/split theorem, constructs the exact residual
record consumed by `Case4KernelAggregation`. -/
theorem case4SplitRightResidualKernels_of_outer
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (outer : OuterDirectNearKernel Q) :
    Case4SplitRightResidualKernels Q where
  direct_near_two := by
    intro s t v S T hsRole htDirect hnear hassoc
    by_cases hst : s = t
    · exact hst
    generalize hformula : directArrivalFormula T.target T.descriptor htDirect = G
    cases G with
    | singleton hone middleCoord htarget hassociation =>
        exact (Erdos957Case4DirectDisplacement.singleton_direct_near_two_associations_ne
          hA Q S T hsRole htDirect middleCoord htarget hassociation hnear hassoc).elim
    | outer O =>
        exact (outer S T hsRole htDirect O hnear hassoc).elim
    | paired middle twoExtreme htarget hassociation =>
        exact (Erdos957Case4DirectSameSide.paired_direct_near_two_associations_ne
          Q S T hsRole twoExtreme htarget hassociation hnear hassoc).elim
  split_right_competitor := by
    intro s t v S T hsRole htRole htWindow hassoc
    exact Erdos957Case4SplitClassification.split_right_same_association_source_eq_in_window
      hA Q S T hsRole htRole htWindow hassoc

/-- No-residual K4 package: all singleton, outer, paired, and split
competitor branches are now discharged from genuine selected geometry. -/
theorem case4SplitRightResidualKernels
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart) :
    Case4SplitRightResidualKernels Q :=
  case4SplitRightResidualKernels_of_outer hA Q
    (outerDirectNearKernel hA Q)

/-- Canonical produced-hull specialization requested by final assembly. -/
noncomputable def producedCase4SplitRightResidualKernels
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L)) :
    Case4SplitRightResidualKernels
      (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
      (F := Erdos957DirectSameSide.ProducedFrame hA R L)
      (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
        hA R L W) :=
  case4SplitRightResidualKernels hA
    (P := Erdos957DirectSameSide.ProducedHull R L)
    (W := W)
    (F := Erdos957DirectSameSide.ProducedFrame hA R L)
    (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
      hA R L W)

/-! ## Weight-aware Case-4 package

The pairwise K4 result is stronger than each of the six weight-aware
residual fields: among three Boolean associations some pair agrees, and
that pair is either split/split or split/direct.  Consequently the two
degree-five triples are impossible, while the two four-source `Fits`
goals follow by eliminating an impossible split triple. -/

/-- Every weight-aware Case-4 residual follows from the checked pairwise
K4 package.  This theorem deliberately says nothing about a mixed
Case-2-secondary/Case-4-split pair. -/
theorem case4WeightedCollisionResiduals
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (locality : SourceLocalityCertificates P W F)
    (K : Case4SplitRightResidualKernels Q) :
    Case4WeightedCollisionResiduals Q := by
  let T3 := Erdos957Case4KernelAggregation.case4SplitRightNoThreeResidual_of_pairwise
    Q locality K
  refine {
    split_split_half_direct_degree_five := ?_
    three_split_right_degree_five := ?_
    three_split_right_one_direct_quadruple_fits := ?_
    four_split_right_quadruple_fits := ?_
    three_split_right_same_association := ?_
    two_split_right_one_direct_same_association := ?_ }
  · intro s t u v S T U hsRole htRole huDirect _ _ htWindow huWindow
      hst hsu htu
    exact T3.split_right_with_direct S T U hsRole htRole huDirect
      htWindow huWindow hst hsu htu
  · intro s t u v S T U hsRole htRole huRole _ htWindow huWindow
      hst hsu htu
    exact T3.three_split_right S T U hsRole htRole huRole
      htWindow huWindow hst hsu htu
  · intro s t u d v S T U D hsRole htRole huRole _
      htWindow huWindow _ hst hsu _ htu _ _
    exact (T3.three_split_right S T U hsRole htRole huRole
      htWindow huWindow hst hsu htu).elim
  · intro s t u d v S T U D hsRole htRole huRole _
      htWindow huWindow _ hst hsu _ htu _ _
    exact (T3.three_split_right S T U hsRole htRole huRole
      htWindow huWindow hst hsu htu).elim
  · intro s t u v S T U hsRole htRole huRole _ _ htWindow huWindow
      hst hsu htu
    exact T3.three_split_right S T U hsRole htRole huRole
      htWindow huWindow hst hsu htu
  · intro s t u v S T U hsRole htRole huDirect _ _ htWindow huWindow
      hst hsu htu
    exact T3.split_right_with_direct S T U hsRole htRole huDirect
      htWindow huWindow hst hsu htu

/-- Produced, premise-free Case-4 weight-aware residual record. -/
noncomputable def producedCase4WeightedCollisionResiduals
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (Erdos957DirectSameSide.ProducedHull R L)) :
    Case4WeightedCollisionResiduals
      (P := Erdos957DirectSameSide.ProducedHull R L) (W := W)
      (F := Erdos957DirectSameSide.ProducedFrame hA R L)
      (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
        hA R L W) :=
  case4WeightedCollisionResiduals
    (P := Erdos957DirectSameSide.ProducedHull R L)
    (W := W)
    (F := Erdos957DirectSameSide.ProducedFrame hA R L)
    (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
      hA R L W)
    ⟨Erdos957GeometryTransfer.producedCyclicWindowGeometry hA R L W⟩
    (producedCase4SplitRightResidualKernels hA R L W)

end Erdos957Case4ProducedResiduals

#print axioms Erdos957Case4ProducedResiduals.case4SplitRightResidualKernels_of_outer
#print axioms Erdos957Case4ProducedResiduals.outerDirectNearKernel
#print axioms Erdos957Case4ProducedResiduals.case4SplitRightResidualKernels
#print axioms Erdos957Case4ProducedResiduals.producedCase4SplitRightResidualKernels
#print axioms Erdos957Case4ProducedResiduals.case4WeightedCollisionResiduals
#print axioms Erdos957Case4ProducedResiduals.producedCase4WeightedCollisionResiduals
