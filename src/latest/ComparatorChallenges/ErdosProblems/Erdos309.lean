/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Real
open scoped BigOperators Topology

noncomputable section

namespace UnitFractions

open scoped Classical in
def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos309

open scoped Classical in
def IsRepresentable (N m : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ UnitFractions.rec_sum A = (m : ℚ)

end Erdos309

namespace Erdos309

open scoped Classical in
def representableIntegers (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (IsRepresentable N)

end Erdos309

namespace Erdos309

open scoped Classical in
def F (N : ℕ) : ℕ := (representableIntegers N).card

end Erdos309

namespace Erdos309

open scoped Classical in
theorem erdos_309 :
    Tendsto (fun N : ℕ ↦ (F N : ℝ) / Real.log (N : ℝ)) atTop (𝓝 1) ∧
      ¬ ((fun N : ℕ ↦ (F N : ℝ)) =o[atTop]
          (fun N : ℕ ↦ Real.log (N : ℝ))) := by
  sorry

end Erdos309

end
