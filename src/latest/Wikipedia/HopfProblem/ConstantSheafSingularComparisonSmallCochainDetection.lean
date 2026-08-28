import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallCochainExtension

/-!
# Detection of small-cochain restrictions on actual simplex generators

Equality and vanishing of the literal small-chain restriction are detected
on precisely the original singular simplices carried by a member of the
given family.  Neither openness nor a covering hypothesis is needed.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {ι : Type*}
variable (A : AddCommGrpCat.{0}) (U : ι → Set X) (n : ℕ)

/-- Equality of actual restrictions is equality on all small simplex generators. -/
theorem smallCochainRestriction_eq_iff (φ ψ : Cochains X A n) :
    (smallCochainRestriction A U).f n φ = (smallCochainRestriction A U).f n ψ ↔
      ∀ σ : SingularSimplex X n, (∃ i, range σ ⊆ U i) →
        φ (simplexChain X n σ) = ψ (simplexChain X n σ) := by
  constructor
  · intro h σ hσ
    exact congrArg (fun χ : SmallCochains U A n =>
      χ ⟨simplexChain X n σ, simplexChain_mem_small U n σ hσ⟩) h
  · intro h
    apply smallCochain_ext A U n
    intro σ
    change φ (smallChainBasis U n σ).1 = ψ (smallChainBasis U n σ).1
    rw [smallChainBasis_apply_val]
    exact h σ.1 σ.2

/-- Literal restriction vanishes exactly when every small simplex value vanishes. -/
theorem smallCochainRestriction_eq_zero_iff (φ : Cochains X A n) :
    (smallCochainRestriction A U).f n φ = 0 ↔
      ∀ σ : SingularSimplex X n, (∃ i, range σ ⊆ U i) →
        φ (simplexChain X n σ) = 0 := by
  constructor
  · intro h σ hσ
    exact congrArg (fun χ : SmallCochains U A n =>
      χ ⟨simplexChain X n σ, simplexChain_mem_small U n σ hσ⟩) h
  · intro h
    apply smallCochain_ext A U n
    intro σ
    change φ (smallChainBasis U n σ).1 = 0
    rw [smallChainBasis_apply_val]
    exact h σ.1 σ.2

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
