import Wikipedia.HopfProblem.FirstHurewiczChains
import Wikipedia.HopfProblem.SheafCupProductCofaceBasic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Ring cofaces on the original singular-simplex values

The cochains here are functions on the actual continuous singular
simplices. Each coface is literal restriction along the original affine
simplex face. Their identities come from the actual topological simplex
functor, not from an assumed comparison of cochain complexes.
-/

noncomputable section

open CategoryTheory
open scoped Simplicial

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Singular

open FirstHurewicz

/-- The original simplex-value function ring in a specified degree. -/
abbrev Values (X : Type) [TopologicalSpace X] (R : Type) (n : ℕ) :=
  SingularSimplex X n → R

/-- The actual face maps satisfy the original cosimplicial identity. -/
theorem simplexFace_comp (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    (simplexFace (n + 1) j.succ).comp (simplexFace n i) =
      (simplexFace (n + 1) i.castSucc).comp (simplexFace n j) :=
  congrArg (fun f => f.hom) (SimplexCategory.toTop₀.δ_comp_δ (i := i) (j := j) hij)

variable (X : Type) [TopologicalSpace X] (R : Type) [CommRing R]

/-- Literal restriction of cochain values along an original simplex face. -/
def face (n : ℕ) (i : Fin (n + 2)) : Values X R n →+* Values X R (n + 1) where
  toFun a σ := a (σ.comp (simplexFace n i))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem face_apply (n : ℕ) (i : Fin (n + 2))
    (a : Values X R n) (σ : SingularSimplex X (n + 1)) :
    face X R n i a σ = a (σ.comp (simplexFace n i)) := rfl

theorem face_comp_face (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    (face X R (n + 1) j.succ).comp (face X R n i) =
      (face X R (n + 1) i.castSucc).comp (face X R n j) := by
  ext a σ
  change a ((σ.comp (simplexFace (n + 1) j.succ)).comp (simplexFace n i)) =
    a ((σ.comp (simplexFace (n + 1) i.castSucc)).comp (simplexFace n j))
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, simplexFace_comp n i j hij]

/-- The actual low-degree coface data on the original singular-simplex function rings. -/
def cofaceData : SheafCupProduct.Coface.Data
    (Values X R 0) (Values X R 1) (Values X R 2) (Values X R 3) where
  δ0 := face X R 0
  δ1 := face X R 1
  δ2 := face X R 2
  coface01 i j hij := face_comp_face X R 0 i j hij
  coface12 i j hij := face_comp_face X R 1 i j hij

end Wikipedia.HopfProblem.SheafSingularCupComparison.Singular
