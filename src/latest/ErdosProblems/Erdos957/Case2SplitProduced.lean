import ErdosProblems.Erdos957.Case2SplitCompletion
import ErdosProblems.Erdos957.GeometryCompletion

/-!
# Produced completion of the degree-five Case-2 split residual

This final leaf specializes the checked generic Case-2/split residual to the
canonical produced hull, frame, and coherent row family.  It then discharges
the last parameter of the weighted geometry completion theorem.
-/

noncomputable section

namespace Erdos957Case2SplitProduced

open Erdos957GeometryCore
open Erdos957Case2SecondaryNoThree
open Erdos957DirectSameSide

abbrev Point := Erdos957GeometryCore.Point

/-- The canonical produced rows satisfy both degree-five Case-2/split
residual fields, with no remaining geometric input. -/
noncomputable def producedCase2SecondarySplitDegreeFiveResiduals
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (ProducedHull R L)) :
    Case2SecondarySplitDegreeFiveResiduals
      (P := ProducedHull R L) (W := W) (F := ProducedFrame hA R L)
      (ProducedRows hA R L W) :=
  Erdos957Case2SplitCompletion.case2SecondarySplitDegreeFiveResiduals hA
    (A := A) (P := ProducedHull R L) (W := W)
    (F := ProducedFrame hA R L)
    (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
      hA R L W)

/-- All geometric transfer certificates required by the charging argument
are now produced without residual assumptions. -/
theorem geometryProducesTransfer : Erdos957GeometryCore.GeometryProducesTransfer :=
  Erdos957GeometryCompletion.geometryProducesTransfer_of_case2_split_residuals
    (fun hA R L W ↦
      producedCase2SecondarySplitDegreeFiveResiduals hA R L W)

end Erdos957Case2SplitProduced

#print axioms Erdos957Case2SplitProduced.producedCase2SecondarySplitDegreeFiveResiduals
#print axioms Erdos957Case2SplitProduced.geometryProducesTransfer
