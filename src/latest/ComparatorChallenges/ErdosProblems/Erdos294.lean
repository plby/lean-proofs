import Mathlib

open Filter Real
open scoped BigOperators Topology

noncomputable section


namespace UnitFractions

open scoped Classical in
def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos294

open scoped Classical in
def Represents (N t : ℕ) : Prop :=
  1 ≤ t ∧ ∃ A : Finset ℕ, t ∈ A ∧
    (∀ n ∈ A, t ≤ n ∧ n ≤ N) ∧ UnitFractions.rec_sum A = 1

open scoped Classical in
lemma exists_positive_not_represents (N : ℕ) :
    ∃ t : ℕ, 1 ≤ t ∧ ¬ Represents N t := by
  refine ⟨N + 1, by omega, ?_⟩
  rintro ⟨-, A, htA, hbounds, -⟩
  exact (Nat.not_succ_le_self N) (hbounds (N + 1) htA).2

end Erdos294

namespace Erdos294

open scoped Classical in
def firstForbidden (N : ℕ) : ℕ :=
  Nat.find (exists_positive_not_represents N)

end Erdos294

namespace Erdos294

open scoped Classical in
def lowerProfile (k : ℕ) (N : ℕ) : ℝ :=
  (N : ℝ) /
    (log (N : ℝ) * (log (log (N : ℝ))) ^ 3 *
      (log (log (log (N : ℝ)))) ^ k)

end Erdos294

namespace Erdos294

open scoped Classical in
def upperProfile (N : ℕ) : ℝ :=
  (N : ℝ) / log (N : ℝ)

end Erdos294

namespace Erdos294

open scoped Classical in
def Resolution : Prop :=
  ∃ (k : ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ᶠ N : ℕ in atTop,
      c * lowerProfile k N ≤ firstForbidden N ∧
        (firstForbidden N : ℝ) ≤ C * upperProfile N

end Erdos294

namespace Erdos294

open scoped Classical in
theorem erdos_294 : Resolution := by
  sorry

end Erdos294

end
