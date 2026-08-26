import Mathlib

/-!
# Scalar precision for the generated affine high-k table

The crossing and derivative certificates have their own fixed precisions.
This record controls only the scalar interval expressions, in particular the
expensive affine-corner lower bound.  The table generator rewrites the single
value below when explicit `--scalar-*` options are supplied.
-/

set_option warningAsError false

namespace Erdos1038.HighKPlatformAffinePrecision

/-- Independently configurable truncation depths for affine scalar checks. -/
structure ScalarPrecision where
  logTerms : ℕ
  sqrtSteps : ℕ
  trigDoubles : ℕ
  fourierTerms : ℕ
deriving DecidableEq, Repr

/-- Production scalar precision.  Changing it is an explicit generator option
rather than an incidental edit to the generic certificate module. -/
def scalarPrecision : ScalarPrecision where
  logTerms := 80
  sqrtSteps := 64
  trigDoubles := 12
  fourierTerms := 56

end Erdos1038.HighKPlatformAffinePrecision
