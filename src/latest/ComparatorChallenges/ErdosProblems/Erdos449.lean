/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace Erdos449

def closeDivisorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.divisors.product n.divisors).filter fun p ↦
    p.1 < p.2 ∧ p.2 < 2 * p.1

def r (n : ℕ) : ℕ := (closeDivisorPairs n).card

def tau (n : ℕ) : ℕ := n.divisors.card

end Erdos449

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos449

theorem not_erdos_449 : ¬
    ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (r n : ℝ) < ε * (tau n : ℝ)}.HasDensity 1 := by
  sorry

end Erdos449
