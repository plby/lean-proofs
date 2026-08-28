import Wikipedia.HopfProblem.SheafCupProductCofaceBasic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Algebra.Category.Ring.Basic

/-!
# The coface interface from an actual cosimplicial commutative ring

The finite interface is obtained from Mathlib's genuine cosimplicial
object by forgetting the unused degrees and codegeneracies. Its two
coface identities are the corresponding functorial identities.
-/

universe u

open CategoryTheory
open scoped Simplicial

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface

def ofCosimplicial (X : CosimplicialObject CommRingCat.{u}) :
    Data (X ^⦋0⦌) (X ^⦋1⦌) (X ^⦋2⦌) (X ^⦋3⦌) where
  δ0 i := (X.δ i).hom
  δ1 i := (X.δ i).hom
  δ2 i := (X.δ i).hom
  coface01 i j hij := congrArg (fun f => f.hom) (X.δ_comp_δ (i := i) (j := j) hij)
  coface12 i j hij := congrArg (fun f => f.hom) (X.δ_comp_δ (i := i) (j := j) hij)

end Wikipedia.HopfProblem.SheafCupProduct.Coface
