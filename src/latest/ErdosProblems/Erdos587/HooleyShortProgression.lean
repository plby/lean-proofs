import ErdosProblems.Erdos587.HooleyProgressionMean
import ErdosProblems.Erdos587.HooleyFourthRoot

/-!
# A fixed-power short-progression Delta bound

The auxiliary fourth-root cutoff is eliminated. The ambient integer
bound may be any fixed power of the progression length; neither signed
affine coefficient occurs in the implicit constant.
-/

open scoped BigOperators

namespace Erdos587

theorem exists_hooleyDelta_short_progression_totient_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ), B ≠ 0 → IsCoprime A B →
      ∀ N Y : ℕ, 2 ≤ N → 16 ≤ Y → N ≤ Y ^ r →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Y →
      (∀ n ∈ S, A + B * n ≠ 0) → (∀ n ∈ S, (A + B * n).natAbs ≤ N) →
      (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
        C * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_affine_fourth_root_mean (4 * r) (by omega)
  refine ⟨C, hC, ?_⟩
  intro A B hB hAB N Y hN hY hNY S hS hnonzero hvalues
  exact hmean A B hB hAB (deltaFourthRoot Y) N Y (deltaFourthRoot_two_le hY) hN
    (deltaFourthRoot_pow_le Y) (deltaFourthRoot_power_size hNY) S hS hnonzero hvalues

end Erdos587
