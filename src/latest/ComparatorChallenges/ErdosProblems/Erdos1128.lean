/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Cardinal Set Ordinal Order

namespace Erdos1128

def IsMonochromaticBox {A B C : Type*} (f : A → B → C → Fin 2)
    (A₁ : Set A) (B₁ : Set B) (C₁ : Set C) : Prop :=
  ∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ c' ∈ C₁, f a b c' = c

theorem erdos_1128 : ¬
    ∀ (A B C : Type) (_ : #A = aleph 1) (_ : #B = aleph 1)
      (_ : #C = aleph 1) (f : A → B → C → Fin 2),
      ∃ (A₁ : Set A) (B₁ : Set B) (C₁ : Set C),
        #A₁ = aleph 0 ∧ #B₁ = aleph 0 ∧ #C₁ = aleph 0 ∧
        IsMonochromaticBox f A₁ B₁ C₁ := by
  sorry

end Erdos1128
