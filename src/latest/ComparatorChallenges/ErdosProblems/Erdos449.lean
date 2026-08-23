import Mathlib

open Filter
open scoped Topology BigOperators

noncomputable section


namespace Erdos449

open scoped Classical in
def closeDivisorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.divisors.product n.divisors).filter fun p ↦
    p.1 < p.2 ∧ p.2 < 2 * p.1

end Erdos449

namespace Erdos449

open scoped Classical in
def r (n : ℕ) : ℕ := (closeDivisorPairs n).card

end Erdos449

namespace Erdos449

open scoped Classical in
def tau (n : ℕ) : ℕ := n.divisors.card

end Erdos449

namespace Set

open scoped Classical in
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

open scoped Classical in
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos449

open scoped Classical in
theorem erdos_449 : ¬
    ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (r n : ℝ) < ε * (tau n : ℝ)}.HasDensity 1 := by
  sorry

end Erdos449

end
