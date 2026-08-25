import ErdosProblems.Erdos67.Pretentious
import BoundedGaps.Maynard.PrimeMertensInterval

/-!
# Quantitative tails of pretentious distance

This file gives the moving-cutoff estimate used in the varying-scale Halasz
argument.  It is derived from the proved bounded-error Mertens theorem for
`sum (log p) / p`; no asymptotic input is left as an assumption.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRHalaszDistanceTail

noncomputable section

open Erdos67
open BoundedGaps.Maynard

theorem primesBetween_eq_primeLogIntervalSet (x y : ℕ) :
    primesBetween x y =
      Nat.primesLE y \ Nat.primesLE ((x + 1) - 1) := by
  have hsub : (x + 1) - 1 = x := by omega
  rw [hsub]
  ext p
  simp only [mem_primesBetween, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hxp, hpy⟩
    refine ⟨⟨hpy, hp⟩, ?_⟩
    intro hpx
    exact (not_lt_of_ge hpx.1) hxp
  · rintro ⟨⟨hpy, hp⟩, hpx⟩
    refine ⟨hp, ?_, hpy⟩
    by_contra hnot
    exact hpx ⟨Nat.le_of_not_gt hnot, hp⟩

/-- Reciprocal prime mass on `(x,y]` is controlled by the logarithmically
weighted prime mass, divided by the logarithm of the lower endpoint. -/
theorem sum_inv_primesBetween_le_primeLogInterval
    {x y : ℕ} (hx : 2 ≤ x) :
    (∑ p ∈ primesBetween x y, (p : ℝ)⁻¹) ≤
      primeLogIntervalSum (x + 1) y / Real.log (x + 1 : ℝ) := by
  rw [primesBetween_eq_primeLogIntervalSet,
    primeLogIntervalSum]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have hpMem := Finset.mem_sdiff.mp hp
  have hpPrime : p.Prime := (Nat.mem_primesLE.mp hpMem.1).2
  have hxp : x < p := by
    by_contra hnot
    exact hpMem.2 (Nat.mem_primesLE.mpr ⟨by omega, hpPrime⟩)
  have hlogPos : 0 < Real.log (x + 1 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x + 1 by omega)
  apply (le_div_iff₀ hlogPos).2
  rw [inv_mul_eq_div]
  apply div_le_div_of_nonneg_right
  · apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      positivity
    · simp only [Set.mem_Ioi]
      exact_mod_cast hpPrime.pos
    · exact_mod_cast (show x + 1 ≤ p by omega)
  · positivity

/-- An explicit bounded-error reciprocal-prime tail estimate. -/
theorem exists_uniform_sum_two_div_primesBetween_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x y : ℕ}, 2 ≤ x → x < y →
      (∑ p ∈ primesBetween x y, 2 / (p : ℝ)) ≤
        2 * (Real.log ((y : ℝ) / (x + 1 : ℝ)) + C) /
          Real.log (x + 1 : ℝ) := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_uniform_abs_primeLogIntervalSum_sub_log_div
  let C := |C₀|
  refine ⟨C, abs_nonneg _, ?_⟩
  intro x y hx hxy
  have hxy' : x + 1 ≤ y := by omega
  have hrecip := sum_inv_primesBetween_le_primeLogInterval
    (x := x) (y := y) hx
  have hM := hC₀ (w := x + 1) (z := y) (by omega) hxy'
  have hprimeLog :
      primeLogIntervalSum (x + 1) y ≤
        Real.log ((y : ℝ) / (x + 1 : ℝ)) + C := by
    have hdiff :
        primeLogIntervalSum (x + 1) y -
            Real.log ((y : ℝ) / (x + 1 : ℝ)) ≤ C := by
      calc
        _ ≤ |primeLogIntervalSum (x + 1) y -
            Real.log ((y : ℝ) / (x + 1 : ℝ))| := le_abs_self _
        _ ≤ C₀ := by
          simpa only [Nat.cast_add, Nat.cast_one] using hM
        _ ≤ C := le_abs_self C₀
    linarith
  have hlogPos : 0 < Real.log (x + 1 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < x + 1 by omega)
  have hsumEq :
      (∑ p ∈ primesBetween x y, 2 / (p : ℝ)) =
        2 * ∑ p ∈ primesBetween x y, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [div_eq_mul_inv]
  rw [hsumEq]
  calc
    2 * ∑ p ∈ primesBetween x y, (p : ℝ)⁻¹ ≤
        2 * (primeLogIntervalSum (x + 1) y /
          Real.log (x + 1 : ℝ)) := by gcongr
    _ ≤ 2 * ((Real.log ((y : ℝ) / (x + 1 : ℝ)) + C) /
          Real.log (x + 1 : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- Ready-to-use moving-cutoff loss for pretentious distance. -/
theorem exists_uniform_pretentiousDistSq_tail_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f g : ℕ → ℂ} {x y : ℕ},
        2 ≤ x → x < y →
        (∀ p, p.Prime → ‖f p‖ ≤ 1) →
        (∀ p, p.Prime → ‖g p‖ ≤ 1) →
        pretentiousDistSq f g y - pretentiousDistSq f g x ≤
          2 * (Real.log ((y : ℝ) / (x + 1 : ℝ)) + C) /
            Real.log (x + 1 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := exists_uniform_sum_two_div_primesBetween_le
  refine ⟨C, hC, ?_⟩
  intro f g x y hx hxy hf hg
  exact (pretentiousDistSq_tail_le_primeHarmonic hxy.le hf hg).trans
    (htail hx hxy)

/-- A form of the tail estimate arranged for the varying-scale Halasz
argument: a distance lower bound at the upper cutoff remains a lower bound
at every smaller cutoff, with only the explicit reciprocal-prime loss. -/
theorem exists_uniform_pretentiousDistSq_ge_at_lower_cutoff :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f g : ℕ → ℂ} {A : ℝ} {x y : ℕ},
        2 ≤ x → x < y →
        (∀ p, p.Prime → ‖f p‖ ≤ 1) →
        (∀ p, p.Prime → ‖g p‖ ≤ 1) →
        A ≤ pretentiousDistSq f g y →
        A - 2 * (Real.log ((y : ℝ) / (x + 1 : ℝ)) + C) /
              Real.log (x + 1 : ℝ) ≤
          pretentiousDistSq f g x := by
  obtain ⟨C, hC, htail⟩ := exists_uniform_pretentiousDistSq_tail_le
  refine ⟨C, hC, ?_⟩
  intro f g A x y hx hxy hf hg hA
  have h := htail hx hxy hf hg
  linarith

end

end Erdos67.MRHalaszDistanceTail
