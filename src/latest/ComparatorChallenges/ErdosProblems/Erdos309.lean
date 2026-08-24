/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos309

def IsRepresentable (N m : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ UnitFractions.rec_sum A = (m : ℚ)

open scoped Classical in
noncomputable def representableIntegers (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (IsRepresentable N)

noncomputable def F (N : ℕ) : ℕ := (representableIntegers N).card

theorem not_erdos_309 :
    Tendsto (fun N : ℕ ↦ (F N : ℝ) / Real.log (N : ℝ)) atTop (𝓝 1) ∧
      ¬ ((fun N : ℕ ↦ (F N : ℝ)) =o[atTop]
          (fun N : ℕ ↦ Real.log (N : ℝ))) := by
  sorry

end Erdos309
