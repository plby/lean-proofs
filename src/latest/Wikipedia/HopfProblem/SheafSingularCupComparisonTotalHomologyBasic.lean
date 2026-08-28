import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalComplex
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Canonical short complexes of the original total differential

The categorical maps are the literal additive total maps on the
original product groups. Their square-zero proofs are the already
proved identities of that same total complex.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex.Data

universe u

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [AddCommGroup R00] [AddCommGroup R10] [AddCommGroup R01]
  [AddCommGroup R20] [AddCommGroup R11] [AddCommGroup R02]
  [AddCommGroup R30] [AddCommGroup R21] [AddCommGroup R12] [AddCommGroup R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

/-- The original degree-one total short complex in additive groups. -/
def oneComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (AddCommGrpCat.ofHom D.d0) (AddCommGrpCat.ofHom D.d1) (by
    apply AddCommGrpCat.hom_ext
    exact D.d1_comp_d0)

/-- The original degree-two total short complex in additive groups. -/
def twoComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (AddCommGrpCat.ofHom D.d1) (AddCommGrpCat.ofHom D.d2) (by
    apply AddCommGrpCat.hom_ext
    exact D.d2_comp_d1)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex.Data
