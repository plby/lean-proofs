import ErdosProblems.Erdos964.PrimeSlicePNT
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The unconditional prime-counting asymptotic at real endpoints
-/

namespace Erdos964

open Asymptotics Filter
open scoped Asymptotics

theorem primeCounting_real_isEquivalent :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x => x / Real.log x) := by
  have hnat := BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have hfloor : (fun x : ℝ => (⌊x⌋₊ : ℝ)) ~[atTop] (fun x => x) := isEquivalent_nat_floor
  have hlog := hfloor.log tendsto_id
  have h := hnat.comp_tendsto (tendsto_nat_floor_atTop (α := ℝ))
  exact h.trans (hfloor.div hlog)

theorem exists_primeCounting_real_relative_error (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x| ≤ ε * (x / Real.log x) := by
  have h := primeCounting_real_isEquivalent
  rw [Asymptotics.IsEquivalent] at h
  obtain ⟨X, hX⟩ := eventually_atTop.mp (h.bound hε)
  refine ⟨max X 2, le_max_right _ _, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := (le_max_right X 2).trans hx
  have he := hX x ((le_max_left X 2).trans hx)
  have hn : 0 ≤ x / Real.log x := div_nonneg (by linarith) (Real.log_nonneg (by linarith))
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hn] using he

end Erdos964
