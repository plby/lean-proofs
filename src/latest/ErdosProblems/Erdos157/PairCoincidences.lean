import ErdosProblems.Erdos157.PrefixDecoding

/-! Polynomial coincidences forced by a sufficiently long common prefix. -/

namespace Erdos157.Elementary

open Polynomial PolynomialCharacters AuxiliaryModuli

theorem unordered_pair_eq_of_monic_irreducible_products {K : Type*} [Field K]
    {f₁ f₂ f₃ f₄ : K[X]} (h₁ : Irreducible f₁) (h₂ : Irreducible f₂)
    (h₃ : Irreducible f₃) (h₄ : Irreducible f₄)
    (m₁ : f₁.Monic) (m₂ : f₂.Monic) (m₃ : f₃.Monic) (m₄ : f₄.Monic)
    (heq : f₁ * f₂ = f₃ * f₄) : (f₁ = f₃ ∧ f₂ = f₄) ∨ (f₁ = f₄ ∧ f₂ = f₃) := by
  have hdvd : f₁ ∣ f₃ * f₄ := ⟨f₂, heq.symm⟩
  rcases h₁.prime.dvd_mul.mp hdvd with h13 | h14
  · have e13 := Polynomial.eq_of_monic_of_associated m₁ m₃ (h₁.associated_of_dvd h₃ h13)
    subst f₃
    exact Or.inl ⟨rfl, mul_left_cancel₀ h₁.ne_zero heq⟩
  · have e14 := Polynomial.eq_of_monic_of_associated m₁ m₄ (h₁.associated_of_dvd h₄ h14)
    subst f₄
    exact Or.inr ⟨rfl, mul_left_cancel₀ h₁.ne_zero (by simpa only [mul_comm] using heq)⟩

theorem label_pair_eq_of_polynomial_products {K : Type*} [Field K]
    (f₁ f₂ f₃ f₄ : Label K)
    (heq : f₁.polynomial * f₂.polynomial = f₃.polynomial * f₄.polynomial) :
    (f₁ = f₃ ∧ f₂ = f₄) ∨ (f₁ = f₄ ∧ f₂ = f₃) := by
  rcases unordered_pair_eq_of_monic_irreducible_products f₁.irreducible f₂.irreducible
    f₃.irreducible f₄.irreducible f₁.monic f₂.monic f₃.monic f₄.monic heq with h | h
  · exact Or.inl ⟨Label.polynomial_injective h.1, Label.polynomial_injective h.2⟩
  · exact Or.inr ⟨Label.polynomial_injective h.1, Label.polynomial_injective h.2⟩

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem label_pair_eq_of_encoded_pair_eq_of_degree_bound (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (m : ℕ)
    (h₁ : m ≤ f₁.level) (h₂ : m ≤ f₂.level) (h₃ : m ≤ f₃.level) (h₄ : m ≤ f₄.level)
    (hdegree : max (levelDegree f₁.level + levelDegree f₂.level)
      (levelDegree f₃.level + levelDegree f₄.level) < m ^ 2)
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    (f₁ = f₃ ∧ f₂ = f₄) ∨ (f₁ = f₄ ∧ f₂ = f₃) := by
  have hdiv := product_dvd_of_encoded_pair_eq K τ ω f₁ f₂ f₃ f₄ m h₁ h₂ h₃ h₄ heq
  apply label_pair_eq_of_polynomial_products
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt hdiv
  rw [product_natDegree]
  apply (Polynomial.natDegree_sub_le _ _).trans_lt
  rw [Polynomial.natDegree_mul f₁.irreducible.ne_zero f₂.irreducible.ne_zero,
    Polynomial.natDegree_mul f₃.irreducible.ne_zero f₄.irreducible.ne_zero,
    Label.natDegree, Label.natDegree, Label.natDegree, Label.natDegree]
  exact hdegree

theorem common_modulus_degree_le_of_nontrivial_pair (τ : MaskChoice K) (ω : IntegerParameters K)
    (f₁ f₂ f₃ f₄ : Label K) (m : ℕ)
    (h₁ : m ≤ f₁.level) (h₂ : m ≤ f₂.level) (h₃ : m ≤ f₃.level) (h₄ : m ≤ f₄.level)
    (hne : ¬((f₁ = f₃ ∧ f₂ = f₄) ∨ (f₁ = f₄ ∧ f₂ = f₃)))
    (heq : encoded K τ ω f₁ + encoded K τ ω f₂ = encoded K τ ω f₃ + encoded K τ ω f₄) :
    m ^ 2 ≤ max (levelDegree f₁.level + levelDegree f₂.level)
      (levelDegree f₃.level + levelDegree f₄.level) := by
  by_contra h
  exact hne (label_pair_eq_of_encoded_pair_eq_of_degree_bound K τ ω f₁ f₂ f₃ f₄ m
    h₁ h₂ h₃ h₄ (by omega) heq)

end Erdos157.Elementary
