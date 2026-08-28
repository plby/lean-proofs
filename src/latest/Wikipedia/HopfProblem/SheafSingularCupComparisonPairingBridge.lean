import Mathlib.Logic.Equiv.Basic

/-!
# Reflecting the two proved product diagrams

This elementary lemma only composes commuting maps and actual product
identities. Its sheaf application supplies both identities from the
literal first-column and last-row Alexander--Whitney formulas in the
genuine total resolution.
-/

namespace Wikipedia.HopfProblem.SheafSingularCupComparison

universe u₁ u₂ v₁ v₂ w₁ w₂

/-- Two actual product diagrams into an injective comparison determine
the product under the original comparison equivalence. -/
theorem pairing_comparison
    {A₁ : Type u₁} {A₂ : Type u₂} {B₁ : Type v₁} {B₂ : Type v₂}
    {T₁ : Type w₁} {T₂ : Type w₂}
    (e₁ : A₁ → B₁) (e₂ : A₂ ≃ B₂)
    (n₁ : A₁ → T₁) (n₂ : A₂ → T₂) (m₁ : B₁ → T₁) (m₂ : B₂ → T₂)
    (hn₂ : Function.Injective n₂)
    (h₁ : ∀ a, m₁ (e₁ a) = n₁ a) (h₂ : ∀ a, m₂ (e₂ a) = n₂ a)
    (p : A₁ → A₁ → A₂) (q : B₁ → B₁ → B₂) (t : T₁ → T₁ → T₂)
    (hp : ∀ a b, n₂ (p a b) = t (n₁ a) (n₁ b))
    (hq : ∀ a b, m₂ (q a b) = t (m₁ a) (m₁ b)) (a b : A₁) :
    e₂ (p a b) = q (e₁ a) (e₁ b) := by
  have hm₂ : Function.Injective m₂ := by
    intro x y h
    obtain ⟨x, rfl⟩ := e₂.surjective x
    obtain ⟨y, rfl⟩ := e₂.surjective y
    apply congrArg e₂
    apply hn₂
    exact (h₂ x).symm.trans (h.trans (h₂ y))
  apply hm₂
  calc
    m₂ (e₂ (p a b)) = n₂ (p a b) := h₂ (p a b)
    _ = t (n₁ a) (n₁ b) := hp a b
    _ = t (m₁ (e₁ a)) (m₁ (e₁ b)) := by rw [h₁, h₁]
    _ = m₂ (q (e₁ a) (e₁ b)) := (hq (e₁ a) (e₁ b)).symm

end Wikipedia.HopfProblem.SheafSingularCupComparison
