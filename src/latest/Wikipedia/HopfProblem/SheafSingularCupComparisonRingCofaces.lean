import Wikipedia.HopfProblem.SheafSingularCupComparisonRingPresheaf
import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularBasic

/-!
# Genuine singular cofaces as morphisms of ring presheaves

The maps restrict a cochain to an actual face of a singular simplex.
Their identities come from the original topological simplex maps, and
they commute with restriction to every open subspace.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open FirstHurewicz

variable (X : TopCat.{0})

/-- Restrict an actual singular cochain to an actual simplex face. -/
def cofacePresheaf (n : ℕ) (i : Fin (n + 2)) :
    presheaf X n ⟶ presheaf X (n + 1) where
  app U := CommRingCat.ofHom (Singular.face U.unop ℂ n i)
  naturality _ _ j := by ext φ; rfl

@[simp] theorem cofacePresheaf_app_apply (n : ℕ) (i : Fin (n + 2))
    (U : Opens X) (φ : SingularSimplex U n → ℂ) (σ : SingularSimplex U (n + 1)) :
    (cofacePresheaf X n i).app (op U) φ σ = φ (σ.comp (simplexFace n i)) := rfl

/-- The actual cosimplicial face identity holds before sheafification. -/
theorem cofacePresheaf_comp (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    cofacePresheaf X n i ≫ cofacePresheaf X (n + 1) j.succ =
      cofacePresheaf X n j ≫ cofacePresheaf X (n + 1) i.castSucc := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  exact Singular.face_comp_face U.unop ℂ n i j hij

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
