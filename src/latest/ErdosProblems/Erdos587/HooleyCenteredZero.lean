import ErdosProblems.Erdos587.HooleySmoothReduction

/-! # A square-root bound for the centered zero frequency -/

open scoped SchwartzMap

namespace Erdos587

theorem exists_delta_centered_zero_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ L : ℝ, 1 ≤ L →
      ‖deltaSmoothCenteredQuadratic f L q 0‖ ≤ C * Real.sqrt L := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_small_reduced_denominator_centered_sq_bound
    (Bornology.isVonNBounded_singleton (𝕜 := ℝ) f)
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro q hq L hL
  have hden : ((q / q.gcd 0 : ℕ) : ℝ) ≤ L := by
    simpa only [Nat.gcd_zero_right, Nat.div_self hq, Nat.cast_one] using hL
  have hsq : ‖deltaSmoothCenteredQuadratic f L q 0‖ ^ 2 ≤ C * L := by
    simpa only [Nat.cast_zero, mul_zero] using
      hbound f (Set.mem_singleton f) 1 q hq (Nat.coprime_one_right q) 0 L (by linarith) hden
  exact (Real.le_sqrt_of_sq_le hsq).trans_eq (Real.sqrt_mul hC.le L)

end Erdos587
