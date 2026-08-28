import Wikipedia.HopfProblem.SheafSingularCupComparisonRingForget
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPresheafBasic

/-!
# The actual ring-valued singular-cochain presheaf

A section is an arbitrary complex-valued function on the original
singular simplices of the open subspace. Restrictions are actual
simplex pullbacks and preserve pointwise ring operations. The native
singular-chain basis gives a natural additive isomorphism with the
previously constructed presheaf of additive chain homomorphisms.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open FirstHurewicz ConstantSheafSingularComparison
open CuspNormalization.SheafForgetStalk (forgetToAdd)

variable {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]

/-- Precomposition with the actual singular-simplex map preserves the function ring. -/
def pullback (f : C(Y, Z)) (n : ℕ) :
    (SingularSimplex Z n → ℂ) →+* (SingularSimplex Y n → ℂ) where
  toFun φ σ := φ (f.comp σ)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The same pullback on the original free-chain cochains under basis extension. -/
theorem fromValues_pullback (f : C(Y, Z)) (n : ℕ) (φ : SingularSimplex Z n → ℂ) :
    cochainFromValues Y (AddCommGrpCat.of ℂ) n (pullback f n φ) =
      (singularPullback (AddCommGrpCat.of ℂ) f).f n
        (cochainFromValues Z (AddCommGrpCat.of ℂ) n φ) := by
  apply cochain_ext Y (AddCommGrpCat.of ℂ) n
  intro σ
  rw [cochainFromValues_simplex, singularPullback_simplex, cochainFromValues_simplex]
  rfl

variable (X : TopCat.{0})

/-- Pointwise complex rings on the actual singular simplices of each open. -/
def presheaf (n : ℕ) : TopCat.Presheaf CommRingCat.{0} X where
  obj U := CommRingCat.of (SingularSimplex U.unop n → ℂ)
  map i := CommRingCat.ofHom (pullback ((Opens.toTopCat X).map i.unop).hom n)
  map_id U := by ext φ σ; rfl
  map_comp i j := by ext φ σ; rfl

@[simp] theorem presheaf_map_apply (n : ℕ) {U V : Opens X} (i : U ⟶ V)
    (φ : SingularSimplex V n → ℂ) (σ : SingularSimplex U n) :
    (presheaf X n).map i.op φ σ = φ (((Opens.toTopCat X).map i).hom.comp σ) := rfl

/-- The genuine additive presheaf comparison uses the original simplex basis. -/
def presheafAddIso (n : ℕ) :
    presheaf X n ⋙ forgetToAdd ≅ cochainPresheaf X (AddCommGrpCat.of ℂ) n :=
  NatIso.ofComponents
    (fun U => (cochainEvalEquiv U.unop (AddCommGrpCat.of ℂ) n).symm.toAddCommGrpIso)
    (fun i => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro φ
      exact fromValues_pullback ((Opens.toTopCat X).map i.unop).hom n φ)

@[simp] theorem presheafAddIso_hom_apply (n : ℕ) (U : Opens X)
    (φ : SingularSimplex U n → ℂ) :
    (presheafAddIso X n).hom.app (op U) φ = cochainFromValues U (AddCommGrpCat.of ℂ) n φ := rfl

/-- The comparison sends each simplex value to its original generator evaluation. -/
@[simp] theorem presheafAddIso_hom_simplex (n : ℕ) (U : Opens X)
    (φ : SingularSimplex U n → ℂ) (σ : SingularSimplex U n) :
    (presheafAddIso X n).hom.app (op U) φ (simplexChain U n σ) = φ σ :=
  cochainFromValues_simplex U (AddCommGrpCat.of ℂ) n φ σ

@[simp] theorem presheafAddIso_inv_apply (n : ℕ) (U : Opens X)
    (φ : Cochains U (AddCommGrpCat.of ℂ) n) (σ : SingularSimplex U n) :
    (presheafAddIso X n).inv.app (op U) φ σ = φ (simplexChain U n σ) := rfl

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
