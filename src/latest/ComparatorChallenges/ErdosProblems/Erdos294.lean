/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Real

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos294

def Represents (N t : ℕ) : Prop :=
  1 ≤ t ∧ ∃ A : Finset ℕ, t ∈ A ∧
    (∀ n ∈ A, t ≤ n ∧ n ≤ N) ∧ UnitFractions.rec_sum A = 1

lemma exists_positive_not_represents (N : ℕ) :
    ∃ t : ℕ, 1 ≤ t ∧ ¬ Represents N t := by
  refine ⟨N + 1, Nat.succ_le_succ (Nat.zero_le N), ?_⟩
  rintro ⟨-, A, htA, hbounds, -⟩
  exact (Nat.not_succ_le_self N) (hbounds (N + 1) htA).2

open scoped Classical in
noncomputable def firstForbidden (N : ℕ) : ℕ :=
  Nat.find (exists_positive_not_represents N)

noncomputable def lowerProfile (k : ℕ) (N : ℕ) : ℝ :=
  (N : ℝ) /
    (log (N : ℝ) * (log (log (N : ℝ))) ^ 3 *
      (log (log (log (N : ℝ)))) ^ k)

noncomputable def upperProfile (N : ℕ) : ℝ :=
  (N : ℝ) / log (N : ℝ)

theorem erdos_294 :
    ∃ (k : ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        c * Erdos294.lowerProfile k N ≤ Erdos294.firstForbidden N ∧
          (Erdos294.firstForbidden N : ℝ) ≤ C * Erdos294.upperProfile N := by
  sorry

end Erdos294
