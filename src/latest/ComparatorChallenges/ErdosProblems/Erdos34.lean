/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Erdos34

def perm_consecutive_sums (n : ℕ) (p : Equiv.Perm (Fin n)) : Finset ℕ :=
  (Finset.univ.filter (fun x : Fin n × Fin n => x.1 ≤ x.2)).image
    (fun x => ∑ k ∈ Finset.Icc x.1 x.2, (p k + 1))
def erdos_34 : Prop :=
  ∀ (c : ℝ), c > 0 → ∃ N, ∀ n ≥ N, ∀ (p : Equiv.Perm (Fin n)),
      (perm_consecutive_sums n p).card < c * n^2
end Erdos34

open scoped Classical in
theorem Erdos34.not_erdos_34 :
    Not Erdos34.erdos_34
  := by
  sorry
