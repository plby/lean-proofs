import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallCochainBasic

/-!
# Extension from actual small singular chains

Every additive cochain on small chains extends to all singular chains:
use its given values on small simplex generators, and use zero on the
remaining generators.  This is a degreewise additive splitting of literal
restriction, valid for arbitrary coefficient groups and arbitrary families
of subsets.  It is not asserted to commute with the differential.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {ι : Type*}
variable (A : AddCommGrpCat.{0}) (U : ι → Set X) (n : ℕ)

/-- The original small simplex generators determine a small cochain. -/
theorem smallCochain_ext {φ ψ : SmallCochains U A n}
    (h : ∀ σ : SmallSimplex U n, φ (smallChainBasis U n σ) =
      ψ (smallChainBasis U n σ)) : φ = ψ := by
  have he : addHomToIntLinearMap φ = addHomToIntLinearMap ψ :=
    (smallChainBasis U n).ext h
  exact congrArg LinearMap.toAddMonoidHom he

/-- The simplex-value extension of an actual small cochain. -/
def smallCochainExtend (φ : SmallCochains U A n) : Cochains X A n := by
  classical
  exact cochainFromValues X A n fun σ =>
    if hσ : ∃ i, range σ ⊆ U i then
      φ ⟨simplexChain X n σ, simplexChain_mem_small U n σ hσ⟩ else 0

@[simp]
theorem smallCochainExtend_small_simplex (φ : SmallCochains U A n)
    (σ : SingularSimplex X n) (hσ : ∃ i, range σ ⊆ U i) :
    smallCochainExtend A U n φ (simplexChain X n σ) =
      φ ⟨simplexChain X n σ, simplexChain_mem_small U n σ hσ⟩ := by
  classical
  simp only [smallCochainExtend, cochainFromValues_simplex, dif_pos hσ]

@[simp]
theorem smallCochainExtend_nonsmall_simplex (φ : SmallCochains U A n)
    (σ : SingularSimplex X n) (hσ : ¬ ∃ i, range σ ⊆ U i) :
    smallCochainExtend A U n φ (simplexChain X n σ) = 0 := by
  classical
  simp only [smallCochainExtend, cochainFromValues_simplex, dif_neg hσ]

/-- The extension has exactly its prescribed original values on small chains. -/
@[simp]
theorem smallCochainRestriction_extend (φ : SmallCochains U A n) :
    (smallCochainRestriction A U).f n (smallCochainExtend A U n φ) = φ := by
  apply smallCochain_ext A U n
  intro σ
  change smallCochainExtend A U n φ (smallChainBasis U n σ).1 =
    φ (smallChainBasis U n σ)
  rw [smallChainBasis_apply_val, smallCochainExtend_small_simplex A U n φ σ.1 σ.2]
  apply congrArg φ
  apply Subtype.ext
  exact (smallChainBasis_apply_val U n σ).symm

/-- Actual restriction is surjective in every degree, with no assumption
on the cover or the coefficient group. -/
theorem smallCochainRestriction_surjective :
    Function.Surjective ((smallCochainRestriction A U).f n) := fun φ =>
  ⟨smallCochainExtend A U n φ, smallCochainRestriction_extend A U n φ⟩

/-- The degreewise extension is additive. -/
def smallCochainExtension : SmallCochains U A n →+ Cochains X A n where
  toFun := smallCochainExtend A U n
  map_zero' := by
    apply cochain_ext X A n
    intro σ
    by_cases hσ : ∃ i, range σ ⊆ U i
    · rw [smallCochainExtend_small_simplex A U n 0 σ hσ]
      rfl
    · rw [smallCochainExtend_nonsmall_simplex A U n 0 σ hσ]
      rfl
  map_add' φ ψ := by
    apply cochain_ext X A n
    intro σ
    by_cases hσ : ∃ i, range σ ⊆ U i
    · simp only [smallCochainExtend_small_simplex A U n _ σ hσ,
        AddMonoidHom.add_apply]
      rfl
    · simp only [smallCochainExtend_nonsmall_simplex A U n _ σ hσ,
        AddMonoidHom.add_apply, add_zero]

@[simp]
theorem smallCochainExtension_apply (φ : SmallCochains U A n) :
    smallCochainExtension A U n φ = smallCochainExtend A U n φ := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
