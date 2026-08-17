/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The finite generalized-parking predicate

This small dependency-free module lets both the finite enumeration and the
continuous grid-volume bridge use the same predicate without an import cycle.
-/

namespace Erdos896.Ford

/-- The finite generalized-parking event used to discretize `orderQSet`.

There are `k` labelled balls and `k - U + W` ordered boxes.  The value
`r = 0` is included deliberately; under `1 ≤ U` its inequality is automatic.
-/
def generalizedParkingGood (k U W : ℕ)
    (f : Fin k → Fin (k - U + W)) : Prop :=
  ∀ r : Fin (k - U + 1),
    ((Finset.univ.filter fun i ↦ (f i).val < r.val).card ≤ U + r.val - 1)

noncomputable instance (k U W : ℕ) :
    DecidablePred (@generalizedParkingGood k U W) :=
  Classical.decPred _

end Erdos896.Ford
