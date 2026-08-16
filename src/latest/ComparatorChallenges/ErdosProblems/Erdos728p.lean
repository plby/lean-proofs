import Mathlib

namespace Erdos728p

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option linter.flexible false
set_option linter.style.multiGoal false

attribute [local instance] Classical.propDecidable

def property_thm_1_1 (m : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)), Nat.descFactorial (m + k) k ∣ Nat.choose (2 * m) m
noncomputable def bad_set_thm_1_1 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬ property_thm_1_1 m)
open Real

open Real

open Real

open Matrix

noncomputable def K_small (x : ℝ) : ℕ := Nat.floor (Real.exp (0.5 * Real.sqrt (Real.log x)))
noncomputable def bad_set_intrinsic_1_2 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ k ∈ Finset.Icc 1 (K_small m), ¬ (Nat.choose (m + k) k ∣ Nat.choose (2 * m) m))
end Erdos728p

attribute [local instance] Classical.propDecidable

open Real
open Matrix

namespace Erdos728p

theorem theorem_1_1 :
    (fun x => ((bad_set_thm_1_1 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
  sorry


theorem theorem_1_2 :
    (fun x => ((bad_set_intrinsic_1_2 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
  sorry

end Erdos728p
