/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace Erdos682

noncomputable abbrev nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

end Erdos682

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos682

theorem erdos_682 :
    {n : ℕ | ∃ m : ℕ,
      nthPrime n < m ∧ m < nthPrime (n + 1) ∧
        nthPrime (n + 1) - nthPrime n ≤ Nat.minFac m}.HasDensity 1 := by
  sorry

end Erdos682
