import Mathlib

open scoped BigOperators
open scoped Classical
open Nat List Finset

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos948

def Erdos948Statement : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
    ∀ colouring : ℤ → Fin k,
      ∃ a : ℕ → ℤ, StrictMono a ∧
        {n | a n < (f n : ℤ)}.Infinite ∧
        ∃ omitted : Fin k, ∀ I : Finset ℕ,
          colouring (∑ i ∈ I, a i) ≠ omitted

end Erdos948

namespace Erdos948

theorem erdos_948 : ¬ Erdos948Statement := by
  sorry

end Erdos948

end
