import Mathlib.Combinatorics.Additive.SubsetSum
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Erdos469

def Nat.IsSumDivisors (n : ℕ) : Prop :=
  ∃ S ⊆ n.properDivisors, ∑ d ∈ S, d = n

open Erdos469

theorem erdos_469 :
    letI A := {n : ℕ | 0 < n ∧ n.IsSumDivisors ∧
      ∀ m < n, m ∣ n → ¬m.IsSumDivisors}
    Summable fun n : A ↦ 1 / (n : ℝ) := by
  sorry

end Erdos469

open Filter

open scoped Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos469

def Semiperfect (n : ℕ) : Prop :=
  0 < n ∧ n ∈ n.properDivisors.subsetSum

def semiperfectNumbers : Set ℕ := {n | Semiperfect n}

theorem semiperfect_density_exists_between_zero_and_one :
    ∃ d : ℝ, semiperfectNumbers.HasDensity d ∧ 0 < d ∧ d < 1 := by
  sorry

end Erdos469
