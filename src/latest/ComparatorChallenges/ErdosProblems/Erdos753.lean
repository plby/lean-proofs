/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos753

def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (L : V → Finset ℕ), (∀ v, (L v).card = k) →
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v

noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

theorem not_erdos_753 :
    ¬∃ c : ℝ, c > 0 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)),
        (n : ℝ) ^ ((1 : ℝ) / 2 + c) <
          ((listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ)) := by
  sorry

end Erdos753
