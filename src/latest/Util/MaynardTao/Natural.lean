/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos6.MaynardParameters
import BoundedGaps.Maynard.ImprovedGPY.Positivity

/-!
# Natural-shift Maynard extraction

This module contains the tuple-generic endpoint used by the integral
Maynard--Tao theorem.  The analytic construction only has to produce a
positive sieve excess above m - 1; the elementary positivity argument below
then extracts arbitrarily large translates with at least m prime shifts.
-/

namespace MaynardTao

open Filter

/-- A positive Maynard excess above m - 1 gives arbitrarily large
translates with at least m prime shifts. -/
theorem infinitelyOftenAtLeastPrimeShifts_of_eventuallyPositiveSieveExcess
    {H : Finset ℕ} {m : ℕ}
    (hpos : BoundedGaps.Maynard.HasEventuallyPositiveSieveExcess H
      ((m - 1 : ℕ) : ℝ)) :
    ∀ T : ℕ, ∃ n : ℕ, T < n ∧
      m ≤ BoundedGaps.primeShiftCount H n := by
  obtain ⟨N₀, hN₀⟩ := hpos
  intro T
  let N := max N₀ (T + 1)
  obtain ⟨w, hw, hexcess⟩ := hN₀ N (le_max_left _ _)
  obtain ⟨n, hn, hcount⟩ :=
    BoundedGaps.Maynard.exists_primeShiftCount_gt_of_sieveExcess_pos
      hw hexcess
  refine ⟨n, ?_, ?_⟩
  · have hNn := (Finset.mem_Ico.mp hn).1
    have hTN : T + 1 ≤ N := le_max_right _ _
    omega
  · have hcountNat : m - 1 < BoundedGaps.primeShiftCount H n := by
      exact_mod_cast hcount
    omega

end MaynardTao
