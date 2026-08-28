import Wikipedia.SmoothSixDPoincare.FiniteSignedCancellation

/-!
# Opposite-pair agreement determines a finite unit count up to overall sign

Two unit-sign functions on the same actual finite set that recognize
exactly the same opposite pairs differ by one global sign. In particular
their integer sums have the same absolute value. No cardinality or
geometric count is supplied as an algebraic input.
-/

open scoped BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.SignComparison

variable {X : Type*}

theorem equal_or_neg_on_finite (s : Finset X) (σ τ : X → SignType)
    (hσ : ∀ x ∈ s, σ x = 1 ∨ σ x = -1)
    (hτ : ∀ x ∈ s, τ x = 1 ∨ τ x = -1)
    (hop : ∀ x ∈ s, ∀ y ∈ s, (σ x * σ y = -1) ↔ (τ x * τ y = -1)) :
    (∀ x ∈ s, τ x = σ x) ∨ (∀ x ∈ s, τ x = -σ x) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact Or.inl (by simp)
  by_cases he : σ x = τ x
  · left
    intro y hy
    have ho := hop x hx y hy
    rcases hσ x hx with hsx | hsx <;> rcases hτ x hx with htx | htx <;>
      rcases hσ y hy with hsy | hsy <;> rcases hτ y hy with hty | hty <;> simp_all
  · right
    intro y hy
    have ho := hop x hx y hy
    rcases hσ x hx with hsx | hsx <;> rcases hτ x hx with htx | htx <;>
      rcases hσ y hy with hsy | hsy <;> rcases hτ y hy with hty | hty <;> simp_all

theorem natAbs_sum_eq_of_opposite_iff (s : Finset X) (σ τ : X → SignType)
    (hσ : ∀ x ∈ s, σ x = 1 ∨ σ x = -1)
    (hτ : ∀ x ∈ s, τ x = 1 ∨ τ x = -1)
    (hop : ∀ x ∈ s, ∀ y ∈ s, (σ x * σ y = -1) ↔ (τ x * τ y = -1)) :
    (∑ x ∈ s, (σ x : ℤ)).natAbs = (∑ x ∈ s, (τ x : ℤ)).natAbs := by
  rcases equal_or_neg_on_finite s σ τ hσ hτ hop with he | he
  · have hsum : (∑ x ∈ s, (τ x : ℤ)) = ∑ x ∈ s, (σ x : ℤ) :=
      Finset.sum_congr rfl (fun x hx => congrArg (fun a : SignType => (a : ℤ)) (he x hx))
    rw [hsum]
  · have hsum : (∑ x ∈ s, (τ x : ℤ)) = -(∑ x ∈ s, (σ x : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [he x hx, SignType.coe_neg]
    rw [hsum, Int.natAbs_neg]

end Wikipedia.HopfProblem.DegreeCollapse.SignComparison
