/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos728p

def property_thm_1_1 (m : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 (Nat.floor (0.7 * Real.log m)), Nat.descFactorial (m + k) k ∣ Nat.choose (2 * m) m
open scoped Classical in
noncomputable def bad_set_thm_1_1 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m => ¬ property_thm_1_1 m)

noncomputable def K_small (x : ℝ) : ℕ := Nat.floor (Real.exp (0.5 * Real.sqrt (Real.log x)))
noncomputable def bad_set_intrinsic_1_2 (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor x)).filter (fun m =>
    ∃ k ∈ Finset.Icc 1 (K_small m), ¬ (Nat.choose (m + k) k ∣ Nat.choose (2 * m) m))

theorem erdos_728 :
    (fun x => ((bad_set_thm_1_1 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
  sorry

theorem erdos_728_intrinsic :
    (fun x => ((bad_set_intrinsic_1_2 x).card : ℝ)) =o[Filter.atTop] (fun x => x) := by
  sorry

end Erdos728p
