import ErdosProblems.Erdos4.FGKMTMaskedFourier
import ErdosProblems.Erdos4.FiniteCharacterSupport

/-! Exact conductor support of the combined small-mask and rational-sieve transform. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical FiniteCharacterSupport

section SingleFamily

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ p, Fact (ell p).Prime]

noncomputable def localConductorProduct (χ : ∀ p, DirichletCharacter ℂ (ell p)) : ℕ :=
  ∏ p ∈ support ell χ, ell p

theorem localConductorProduct_le_full (χ : ∀ p, DirichletCharacter ℂ (ell p)) :
    localConductorProduct ell χ ≤ ∏ p, ell p := by
  apply Nat.le_of_dvd (Finset.prod_pos (fun p _ => (Fact.out : (ell p).Prime).pos))
  exact Finset.prod_dvd_prod_of_subset (support ell χ) Finset.univ ell (Finset.subset_univ _)

end SingleFamily

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

theorem localConductorProduct_sum
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s)) :
    localConductorProduct (Sum.elim ell₀ ell₁) χ =
      localConductorProduct ell₀ (fun p => χ (.inl p)) *
        localConductorProduct ell₁ (fun q => χ (.inr q)) := by
  unfold localConductorProduct support
  simp only [Finset.prod_filter]
  exact Fintype.prod_sum_type _

theorem maskedUnitFourier_high_conductor_le (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q)) (j : Fin k)
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hne : maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j χ ≠ 0) :
    localConductorProduct ell₁ (fun q => χ (.inr q)) ≤ R ^ 2 := by
  by_contra hn
  have hz := rationalUnitFourier_eq_zero_of_large_conductor ell₁ b R h₁ j
    (fun q => χ (.inr q)) (support ell₁ (fun q => χ (.inr q)))
    (fun q hq => (mem_support ell₁ (fun q => χ (.inr q)) q).mp hq)
    (lt_of_not_ge hn)
  exact hne (mul_eq_zero_of_right _ hz)

theorem maskedUnitFourier_conductor_le (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q)) (j : Fin k)
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hne : maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j χ ≠ 0) :
    localConductorProduct (Sum.elim ell₀ ell₁) χ ≤ (∏ p, ell₀ p) * R ^ 2 := by
  rw [localConductorProduct_sum]
  exact Nat.mul_le_mul (localConductorProduct_le_full ell₀ (fun p => χ (.inl p)))
    (maskedUnitFourier_high_conductor_le ell₀ ell₁ b R h₀ h₁ j χ hne)

theorem aggregateUnitFourier_conductor_le (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hne : aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ χ ≠ 0) :
    localConductorProduct (Sum.elim ell₀ ell₁) χ ≤ (∏ p, ell₀ p) * R ^ 2 := by
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact maskedUnitFourier_conductor_le ell₀ ell₁ b R h₀ h₁ j χ hj

theorem aggregateUnitFourier_zero_of_large_conductor (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hlarge : (∏ p, ell₀ p) * R ^ 2 < localConductorProduct (Sum.elim ell₀ ell₁) χ) :
    aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ χ = 0 := by
  by_contra hn
  exact (not_le_of_gt hlarge) (aggregateUnitFourier_conductor_le ell₀ ell₁ b R h₀ h₁ χ hn)

theorem aggregateUnitFourier_zero_outside (b : ℝ) (R M : ℕ)
    (hM : (∏ p, ell₀ p) * R ^ 2 ≤ M ^ 2)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hne : χ ≠ fun _ => 1) (hout : χ ∉ smallCharacters (Sum.elim ell₀ ell₁) M) :
    aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ χ = 0 := by
  by_contra hn
  apply hout
  apply (mem_smallCharacters (Sum.elim ell₀ ell₁) M χ).mpr
  exact ⟨hne, (aggregateUnitFourier_conductor_le ell₀ ell₁ b R h₀ h₁ χ hn).trans hM⟩

end Erdos4.FGKMT
