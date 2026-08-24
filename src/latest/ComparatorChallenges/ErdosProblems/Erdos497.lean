/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos497

def PP (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset

open scoped Classical in
noncomputable def antichains (n : ℕ) : Finset (Finset (Finset (Fin n))) :=
  (PP n).powerset.filter (fun ℱ => IsAntichain (· ⊆ ·) (ℱ : Set (Finset (Fin n))))

noncomputable def A (n : ℕ) : ℕ :=
  (antichains n).card

theorem erdos_497 :
    Asymptotics.IsEquivalent Filter.atTop (fun n => Real.logb 2 (A n)) (fun n =>
      (n.choose (n / 2) : ℝ)) := by
  sorry

end Erdos497
