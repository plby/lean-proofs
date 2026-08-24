/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos772

def IsSidon {α : Type*} [DecidableEq α] (a : α → ℕ) (S : Finset α) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ u ∈ S, ∀ v ∈ S,
    a i + a j = a u + a v → ({i, j} : Finset α) = {u, v}

def Guarantees (k n r : ℕ) : Prop :=
  ∀ (A : Finset ℕ), A.card = n →
    (∀ t, ((A.product A).filter (fun p => p.1 + p.2 = t)).card ≤ k) →
    ∃ S : Finset ℕ, S ⊆ A ∧ IsSidon id S ∧ r ≤ S.card

noncomputable def guaranteedSizes (k n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (Guarantees k n)

lemma guaranteedSizes_nonempty (k n : ℕ) : (guaranteedSizes k n).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp [guaranteedSizes, Guarantees]
  intro A hA hrep
  exact ⟨∅, by simp [IsSidon]⟩

noncomputable def H (k n : ℕ) : ℕ :=
  (guaranteedSizes k n).max' (guaranteedSizes_nonempty k n)

theorem erdos_772 (k : ℕ) (_hk : 1 ≤ k) :
    Tendsto (fun n : ℕ =>
      (H k n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ ((1 : ℝ) / 2 + c) < H k n := by
  sorry

end Erdos772
