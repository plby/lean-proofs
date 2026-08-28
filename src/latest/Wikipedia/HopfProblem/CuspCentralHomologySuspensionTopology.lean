import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopologyCharts
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopologyContractions

/-!
# The geometric suspension cover for singular Mayer--Vietoris

`CuspCentralHomology.Suspension X` is the actual quotient of the cylinder
`unitInterval × X` with its two end slices collapsed separately.  The open
sets `Suspension.northOpen` and `Suspension.southOpen` cover this quotient,
each is contractible, and their overlap has a proved homeomorphism to
`(1/4,3/4) × X` and a proved homotopy equivalence to `X`.

All these facts are constructed from the quotient topology.  No geometric
or homotopy-equivalence hypotheses are added to the suspended space.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.Suspension

variable {X : Type*} [TopologicalSpace X]

/-- The homotopy equivalence on the overlap forgets only its height coordinate. -/
@[simp] theorem middleBandHomotopyEquiv_apply (p : middleBand X) :
    middleBandHomotopyEquiv p = (middleBandHomeomorph p).2 := rfl

/-- Suspending a compact space again gives a compact space. -/
instance suspension_compactSpace [CompactSpace X] : CompactSpace (Suspension X) :=
  mk_surjective.compactSpace continuous_mk

variable [Nonempty X]

/-- The northern cone is homotopy equivalent to a point via its constructed contraction. -/
def northOpenHomotopyEquivUnit : (northOpen : Set (Suspension X)) ≃ₕ Unit :=
  Classical.choice (ContractibleSpace.hequiv_unit _)

/-- The southern cone is homotopy equivalent to a point via its constructed contraction. -/
def southOpenHomotopyEquivUnit : (southOpen : Set (Suspension X)) ≃ₕ Unit :=
  Classical.choice (ContractibleSpace.hequiv_unit _)

end Wikipedia.HopfProblem.CuspCentralHomology.Suspension
