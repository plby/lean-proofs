import ErdosProblems.Erdos4.TiltedResidueAssembly
import ErdosProblems.Erdos4.TiltedScale
import ErdosProblems.Erdos4.TiltedMaxima

/-!
# The tilted residue-covering and prime-gap bounds

This module formalizes the two main statements of
*A Tilted Residue-Class Construction for Long Prime-Free Intervals*
(25 August 2026), transcribed in `output/pdf/Erdos_4_GPT_5.6_Sol.tex`.

The finite construction uses the explicit tilt `4 log₃ x`, all fiber blocks,
exact inverse survival weights, and disjoint prime intervals. Both covering
layers are proved on the same finite sieve law, and their expected remainders
are combined before the sieve outcome is selected. Fresh primes finish the
cover. The CRT and scale comparisons give bounds at every sufficiently large
real endpoint.

`maximumCoverLength` and `maximumPrimeGap` are the finite maxima `Y` and `G`
from the manuscript. The final theorems have no analytic or covering hypotheses.
-/

namespace Erdos4.Tilted

open Filter FGKMT

theorem exists_covering_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c * coverScale X ≤ (maximumCoverLength X : ℝ) := by
  obtain ⟨c, hc, hcover⟩ := exists_tilted_interval_cover
  refine ⟨c / (128 * (256 : ℝ)), by positivity, ?_⟩
  have htendsto := scaledParameter_tendsto (by norm_num : 1 ≤ (256 : ℕ))
  filter_upwards [htendsto.eventually hcover,
    htendsto.eventually (eventually_gapTarget_bounds hc),
    eventually_scaledParameter_compare (by norm_num : 1 ≤ (256 : ℕ)),
    eventually_ge_atTop (0 : ℝ)] with X hcover hY hcompare hX
  let x := scaledParameter 256 X
  obtain ⟨cover, hsupport⟩ := hcover
  have hfront : 256 * x ≤ ⌊X⌋₊ := scaledParameter_frontier_le (by norm_num) hX
  have hbounded : BoundedCover ⌊X⌋₊ (gapTarget c x - x) := by
    refine ⟨cover, ?_⟩
    intro p hp
    have hh := Nat.mem_primesLE.mp (hsupport hp)
    exact Nat.mem_primesLE.mpr ⟨hh.1.trans hfront, hh.2⟩
  calc
    _ = (c / 4) * (coverScale X / (32 * (256 : ℝ))) := by ring
    _ ≤ (c / 4) * ((x : ℝ) * outerScale x) := mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = (c / 4) * (x : ℝ) * outerScale x := by ring
    _ ≤ ((gapTarget c x - x : ℕ) : ℝ) := hY.2.2.2.2.2.2.2.2
    _ ≤ _ := Nat.cast_le.mpr (le_maximumCoverLength hbounded)

/-- The covering theorem (1.2), with the maximum defined for every real frontier. -/
theorem covering_theorem :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X * Real.log X / Real.log (Real.log (Real.log X)) ≤ (maximumCoverLength X : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := exists_covering_lower_bound
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hbound
  refine ⟨c, X₀, hc, fun X hX => ?_⟩
  exact (hX₀ X hX).trans_eq' (by unfold coverScale; ring)

theorem exists_tilted_prime_gaps :
    ∃ (c : ℝ) (D : ℕ), 0 < c ∧ 1 ≤ D ∧ ∀ᶠ x : ℕ in atTop,
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ Real.exp ((D : ℝ) * x) ∧
        ((gapTarget c x - x : ℕ) : ℝ) <
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, hc, hcover⟩ := exists_tilted_interval_cover
  refine ⟨c, 4 * 256 + 10, hc, by norm_num, ?_⟩
  filter_upwards [hcover, eventually_ge_atTop 1] with x hcover hx
  obtain ⟨cover, hsupport⟩ := hcover
  obtain ⟨n, hn, hgap⟩ := residueCover_gap_endpoint cover
  have hmod : cover.modulus ≤ primorial (256 * x) := Erdos4.primeProduct_le_primorial hsupport
  refine ⟨n, ?_, hgap⟩
  have hh : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ ((6 * primorial (256 * x) : ℕ) : ℝ) := by
    exact_mod_cast hn.trans (Nat.mul_le_mul_left 6 hmod)
  exact hh.trans (six_primorial_le_exp 256 x hx)

theorem exists_all_endpoint_tilted_gaps :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ T ∧
        c * primeGapScale T ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, D, hc, hD, hgaps⟩ := exists_tilted_prime_gaps
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨c / (128 * (D : ℝ)), by positivity, ?_⟩
  have htendsto := endpointParameter_tendsto hD
  filter_upwards [htendsto.eventually hgaps,
    htendsto.eventually (eventually_gapTarget_bounds hc),
    eventually_endpoint_tilted_compare hD, eventually_ge_atTop (1 : ℝ)]
    with T hgap hlength hcompare hT
  let x := endpointParameter D T
  obtain ⟨n, hn, hgap⟩ := hgap
  refine ⟨n, hn.trans (endpointParameter_exp_le hD hT), ?_⟩
  calc
    _ = (c / 4) * (primeGapScale T / (32 * (D : ℝ))) := by ring
    _ ≤ (c / 4) * ((x : ℝ) * outerScale x) := mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = (c / 4) * (x : ℝ) * outerScale x := by ring
    _ ≤ ((gapTarget c x - x : ℕ) : ℝ) := hlength.2.2.2.2.2.2.2.2
    _ ≤ _ := hgap.le

/-- The prime-gap corollary (1.3), uniformly below every sufficiently large real endpoint. -/
theorem prime_gap_corollary :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T →
      c * Real.log T * Real.log (Real.log T) /
        Real.log (Real.log (Real.log (Real.log T))) ≤ (maximumPrimeGap T : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := exists_all_endpoint_tilted_gaps
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hbound
  refine ⟨c, T₀, hc, ?_⟩
  intro T hT
  obtain ⟨n, hn, hgap⟩ := hT₀ T hT
  have hh := hgap.trans (prime_gap_le_maximum T n hn)
  exact hh.trans_eq' (by unfold primeGapScale coverScale; ring)

/-- A witness form of the prime-gap bound that avoids referring to a maximum. -/
theorem all_endpoint_consecutive_prime_gaps :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ T ∧
      c * Real.log T * Real.log (Real.log T) /
        Real.log (Real.log (Real.log (Real.log T))) ≤
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, hc, hbound⟩ := exists_all_endpoint_tilted_gaps
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hbound
  refine ⟨c, T₀, hc, ?_⟩
  intro T hT
  obtain ⟨n, hn, hgap⟩ := hT₀ T hT
  exact ⟨n, hn, hgap.trans_eq' (by unfold primeGapScale coverScale; ring)⟩

end Erdos4.Tilted
