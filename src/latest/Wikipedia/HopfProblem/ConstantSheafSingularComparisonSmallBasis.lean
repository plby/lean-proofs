import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallComplex
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The marked free basis of genuine small singular chains

The basis consists of the original singular-simplex generators with the
property of lying in one member of the family.  Consequently every small
chain module is free and projective, without a homology or finiteness
assumption on the underlying space or the family.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {ι : Type*}

theorem smallSimplexChain_linearIndependent (U : ι → Set X) (n : ℕ) :
    LinearIndependent ℤ (fun σ : SmallSimplex U n => simplexChain X n σ.1) :=
  (simplexChain_linearIndependent X n).comp (fun σ : SmallSimplex U n => σ.1)
    Subtype.val_injective

theorem smallSimplexChain_range (U : ι → Set X) (n : ℕ) :
    range (fun σ : SmallSimplex U n => simplexChain X n σ.1) =
      simplexChain X n '' {σ : SingularSimplex X n | ∃ i, range σ ⊆ U i} := by
  ext c
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ.1, σ.2, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, rfl⟩

/-- The subset of the genuine singular-simplex basis corresponding to
small simplices, with its actual submodule as target. -/
def smallChainBasis (U : ι → Set X) (n : ℕ) :
    Module.Basis (SmallSimplex U n) ℤ (smallChainSubmodule U n) := by
  letI : Module ℤ
      (Submodule.span ℤ (range (fun σ : SmallSimplex U n => simplexChain X n σ.1))) :=
    (Submodule.span ℤ (range (fun σ : SmallSimplex U n => simplexChain X n σ.1))).module
  exact (Module.Basis.span (smallSimplexChain_linearIndependent U n)).map
    (LinearEquiv.ofEq _ _ (congrArg (Submodule.span ℤ) (smallSimplexChain_range U n)))

/-- The marked basis vector is literally its original singular chain. -/
@[simp] theorem smallChainBasis_apply_val (U : ι → Set X) (n : ℕ)
    (σ : SmallSimplex U n) : (smallChainBasis U n σ).1 = simplexChain X n σ.1 := by
  let : Module ℤ
      (Submodule.span ℤ (range (fun σ : SmallSimplex U n => simplexChain X n σ.1))) :=
    (Submodule.span ℤ (range (fun σ : SmallSimplex U n => simplexChain X n σ.1))).module
  change ((Module.Basis.span (smallSimplexChain_linearIndependent U n)) σ : Chains X n) =
    simplexChain X n σ.1
  exact Module.Basis.coe_span_apply (smallSimplexChain_linearIndependent U n) σ

theorem smallChain_free (U : ι → Set X) (n : ℕ) :
    Module.Free ℤ (smallChainSubmodule U n) :=
  Module.Free.of_basis (smallChainBasis U n)

theorem smallChain_projective (U : ι → Set X) (n : ℕ) :
    CategoryTheory.Projective ((smallComplex U).X n) :=
  ModuleCat.projective_of_free (smallChainBasis U n)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
