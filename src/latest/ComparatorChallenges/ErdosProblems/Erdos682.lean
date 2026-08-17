import Mathlib

open Filter Set
open scoped Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos682

noncomputable abbrev nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

end Erdos682

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

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

end
