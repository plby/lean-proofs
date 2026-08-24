/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos186

def IsNonaveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ,
    S ⊆ A.erase a → 2 ≤ S.card → S.card * a ≠ S.sum id

noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (Finset.Icc 1 N).powerset.filter IsNonaveraging

noncomputable def F (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

theorem erdos_186 :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  sorry

end Erdos186
