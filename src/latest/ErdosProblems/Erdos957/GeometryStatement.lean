import ErdosProblems.Erdos957.HullGeometryBridge

/-!
# Genuine geometric transfer statement for Erdős problem 957

The transfer theorem is quantified over the radial cyclic hull order and
the once-around lift of its concrete edge directions.  Thus the
`CyclicHullData` passed to the certificate is the record actually produced
by `cyclicHullDataOfOrder`, rather than an arbitrary abstract record.

This file only states the remaining proposition.  It adds no geometric
hypothesis, transfer certificate, arrival bound, or capacity assumption.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957GeometryCore

open Erdos957
open Erdos957HullGeometryBridge
open Erdos957TurnSum.HullOrderBridge

/--
The exact remaining global geometry statement over the genuine cyclic hull
geometry produced from a radial order and its lifted edge directions.

Proving it requires constructing the four paper transfers and using the ten
checked case-pair exclusions to establish the target capacities.
-/
def GeometryProducesTransfer : Prop :=
  ∀ (A : Finset Point) (_hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order),
    let P := cyclicHullDataOfOrder R.order L
    ∀ W : DiameterWitnessData P,
      Nonempty (Erdos957.TransferCert (unitDistanceGraph A) P.H
        (distinguishedVertices P W) (sourceVertices P W))

end Erdos957GeometryCore
