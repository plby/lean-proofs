/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Topology

namespace Erdos253

def subsetSums {M : Type*} [AddCommMonoid M] (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

def Set.IsAPOfLengthWith {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def Set.IsAPOfLength {α : Type*} [AddCommMonoid α]
    (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, Set.IsAPOfLengthWith s l a d

@[inline]
def RepresentsAPs (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ ∀ l, Set.IsAPOfLength l ⊤ → (subsetSums (Set.range a) ∩ l).Infinite

theorem not_erdos_253 : ¬ ∀ a : ℕ → ℕ, 0 < a 0 →
    RepresentsAPs a → (Filter.atTop.Tendsto (fun n ↦ (a <| n + 1 : ℝ) / a n) (𝓝 1)) →
      subsetSums (Set.range a) ∈ Filter.cofinite := by
  sorry

end Erdos253
