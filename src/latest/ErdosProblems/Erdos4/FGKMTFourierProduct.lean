import ErdosProblems.Erdos4.FGKMTSmallMaskProduct

/-! Fourier inversion respects a disjoint union of local prime families. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductFourierInversion

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

instance sumLocalPrime (s : P ⊕ Q) : Fact (Sum.elim ell₀ ell₁ s).Prime := by
  cases s with
  | inl p => exact inferInstanceAs (Fact (ell₀ p).Prime)
  | inr q => exact inferInstanceAs (Fact (ell₁ q).Prime)

theorem fourierValue_sum
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) :
    value (Sum.elim ell₀ ell₁) χ u =
      value ell₀ (fun p => χ (.inl p)) (fun p => u (.inl p)) *
        value ell₁ (fun q => χ (.inr q)) (fun q => u (.inr q)) := by
  exact Fintype.prod_sum_type _

theorem productFourier_inversion
    (F₀ : (∀ p, (ZMod (ell₀ p))ˣ) → ℂ)
    (F₁ : (∀ q, (ZMod (ell₁ q))ˣ) → ℂ)
    (c₀ : (∀ p, DirichletCharacter ℂ (ell₀ p)) → ℂ)
    (c₁ : (∀ q, DirichletCharacter ℂ (ell₁ q)) → ℂ)
    (hc₀ : ∀ u, (∑ χ, c₀ χ * value ell₀ χ u) = F₀ u)
    (hc₁ : ∀ u, (∑ χ, c₁ χ * value ell₁ χ u) = F₁ u)
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) :
    (∑ χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s),
      (c₀ (fun p => χ (.inl p)) * c₁ (fun q => χ (.inr q))) *
        value (Sum.elim ell₀ ell₁) χ u) =
      F₀ (fun p => u (.inl p)) * F₁ (fun q => u (.inr q)) := by
  calc
    _ = ∑ χ : (∀ p, DirichletCharacter ℂ (ell₀ p)) ×
          (∀ q, DirichletCharacter ℂ (ell₁ q)),
        (c₀ χ.1 * value ell₀ χ.1 (fun p => u (.inl p))) *
          (c₁ χ.2 * value ell₁ χ.2 (fun q => u (.inr q))) := by
      apply Fintype.sum_equiv
        (Equiv.sumPiEquivProdPi (fun s => DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s)))
      intro χ
      rw [fourierValue_sum]
      exact mul_mul_mul_comm _ _ _ _
    _ = (∑ χ, c₀ χ * value ell₀ χ (fun p => u (.inl p))) *
          (∑ χ, c₁ χ * value ell₁ χ (fun q => u (.inr q))) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      dsimp only
      exact (Finset.mul_sum Finset.univ
        (fun ψ => c₁ ψ * value ell₁ ψ (fun q => u (.inr q)))
        (c₀ χ * value ell₀ χ (fun p => u (.inl p)))).symm
    _ = _ := congrArg₂ (fun a b : ℂ => a * b)
      (hc₀ (fun p => u (.inl p))) (hc₁ (fun q => u (.inr q)))

end Erdos4.FGKMT
