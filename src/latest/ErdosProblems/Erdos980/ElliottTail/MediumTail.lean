/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# Elliott's medium weighted tail

This file isolates the summation step in Elliott's medium-range argument.
The sieve input is deliberately expressed using one aggregate error over the
whole active range.  In particular, no pointwise uniform smallness of the
errors is assumed.
-/

namespace Erdos980.ElliottTail

open Filter Finset
open scoped BigOperators Topology
open Asymptotics

/-- The normalized weighted contribution of the active indices strictly past
the cutoff `M`. -/
noncomputable def mediumWeightedTail
    (weight : ℕ → ℝ) (normalizedCount : ℕ → ℕ → ℝ)
    (active : ℕ → Finset ℕ) (M x : ℕ) : ℝ :=
  ∑ j ∈ (active x).filter (M < ·), weight j * normalizedCount j x

/-- A pointwise main-term estimate with nonnegative errors sums using only the
aggregate error on the full active range.  This is the exact finite
bookkeeping needed after the large-sieve estimate. -/
theorem mediumWeightedTail_le_of_aggregateError
    (weight : ℕ → ℝ) (normalizedCount error : ℕ → ℕ → ℝ)
    (active : ℕ → Finset ℕ) (B ρ : ℝ) (M x : ℕ)
    (hweight : ∀ j, 0 ≤ weight j)
    (herror : ∀ j ∈ active x, 0 ≤ error j x)
    (hcount : ∀ j ∈ active x,
      normalizedCount j x ≤ B * ρ ^ j + error j x) :
    mediumWeightedTail weight normalizedCount active M x ≤
      B * (∑ j ∈ (active x).filter (M < ·), weight j * ρ ^ j) +
        ∑ j ∈ active x, weight j * error j x := by
  rw [mediumWeightedTail]
  calc
    ∑ j ∈ (active x).filter (M < ·), weight j * normalizedCount j x ≤
        ∑ j ∈ (active x).filter (M < ·),
          weight j * (B * ρ ^ j + error j x) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (hcount j (Finset.mem_filter.mp hj).1) (hweight j)
    _ = B * (∑ j ∈ (active x).filter (M < ·), weight j * ρ ^ j) +
        ∑ j ∈ (active x).filter (M < ·), weight j * error j x := by
      rw [Finset.mul_sum]
      simp only [mul_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ B * (∑ j ∈ (active x).filter (M < ·), weight j * ρ ^ j) +
        ∑ j ∈ active x, weight j * error j x := by
      have hsub : (active x).filter (M < ·) ⊆ active x := Finset.filter_subset _ _
      exact add_le_add_right
        (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun j hj _ ↦ mul_nonneg (hweight j) (herror j hj))) _

/-- A finite tail of a nonnegative summable majorant is bounded by the
corresponding shifted infinite tail. -/
theorem finite_strictTail_le_tsum_shift
    (f : ℕ → ℝ) (hf : Summable f) (hnonneg : ∀ j, 0 ≤ f j)
    (s : Finset ℕ) (M : ℕ) :
    ∑ j ∈ s.filter (M < ·), f j ≤ ∑' n : ℕ, f (n + (M + 1)) := by
  let tailSet : Set ℕ := {j | M < j}
  have htailSummable : Summable (tailSet.indicator f) := hf.indicator tailSet
  calc
    ∑ j ∈ s.filter (M < ·), f j =
        ∑ j ∈ s.filter (M < ·), tailSet.indicator f j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Set.indicator_of_mem]
      exact (Finset.mem_filter.mp hj).2
    _ ≤ ∑' j : ℕ, tailSet.indicator f j := by
      exact htailSummable.sum_le_tsum _ (fun j _ ↦ by
        exact Set.indicator_nonneg (fun _ _ ↦ hnonneg _) _)
    _ = ∑' n : ℕ, f (n + (M + 1)) := by
      rw [← _root_.tsum_subtype tailSet f]
      let e : ℕ ≃ tailSet :=
        { toFun := fun n ↦ ⟨n + (M + 1), by dsimp [tailSet]; omega⟩
          invFun := fun j ↦ j.1 - (M + 1)
          left_inv := fun n ↦ by simp
          right_inv := fun j ↦ by
            apply Subtype.ext
            dsimp
            have hjprop := j.2
            change M < j.1 at hjprop
            have hj : M + 1 ≤ j.1 := by omega
            exact Nat.sub_add_cancel hj }
      simpa [e] using (e.tsum_eq (fun j ↦ f j.1)).symm

/-- Infinite shifted tails of a real series tend to zero. -/
theorem tendsto_tsum_shift_zero (f : ℕ → ℝ) :
    Tendsto (fun M ↦ ∑' n : ℕ, f (n + (M + 1))) atTop (nhds 0) := by
  change Tendsto
    ((fun i ↦ ∑' n : ℕ, f (n + i)) ∘ (fun M ↦ M + 1)) atTop (nhds 0)
  exact (tendsto_sum_nat_add f).comp (tendsto_add_atTop_nat 1)

/-- The aggregate-error interface implies uniform smallness of the medium
tail.  Both sieve hypotheses are only required eventually in `x`; the error
itself is controlled solely after summing over the full active range. -/
theorem mediumWeightedTail_eventually_small_of_aggregateError
    (weight : ℕ → ℝ) (normalizedCount error : ℕ → ℕ → ℝ)
    (active : ℕ → Finset ℕ) (B ρ : ℝ)
    (hweight : ∀ j, 0 ≤ weight j) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hsum : Summable (fun j ↦ weight j * ρ ^ j))
    (herror : ∀ᶠ x : ℕ in atTop, ∀ j ∈ active x, 0 ≤ error j x)
    (hcount : ∀ᶠ x : ℕ in atTop, ∀ j ∈ active x,
      normalizedCount j x ≤ B * ρ ^ j + error j x)
    (haggregate : Tendsto
      (fun x ↦ ∑ j ∈ active x, weight j * error j x) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ M X : ℕ, ∀ x : ℕ, X ≤ x →
      mediumWeightedTail weight normalizedCount active M x ≤ ε := by
  intro ε hε
  let f : ℕ → ℝ := fun j ↦ weight j * ρ ^ j
  have hfnonneg : ∀ j, 0 ≤ f j := fun j ↦
    mul_nonneg (hweight j) (pow_nonneg hρ j)
  have hftail := tendsto_tsum_shift_zero f
  have hB1 : 0 < B + 1 := by linarith
  let δ : ℝ := ε / (2 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have htailEventually : ∀ᶠ M : ℕ in atTop,
      (∑' n : ℕ, f (n + (M + 1))) < δ :=
    hftail.eventually (Iio_mem_nhds hδ)
  obtain ⟨M, hM⟩ := htailEventually.exists
  have haggregateSmall : ∀ᶠ x : ℕ in atTop,
      (∑ j ∈ active x, weight j * error j x) < ε / 2 := by
    have hball := haggregate.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 2))
    filter_upwards [hball] with x hx
    have hx' : |∑ j ∈ active x, weight j * error j x| < ε / 2 := by
      simpa [Real.dist_eq] using hx
    exact (le_abs_self _).trans_lt hx'
  have hall := herror.and (hcount.and haggregateSmall)
  obtain ⟨X, hX⟩ := (eventually_atTop.1 hall)
  refine ⟨M, X, fun x hx ↦ ?_⟩
  obtain ⟨herr, hcnt, hagg⟩ := hX x hx
  have hfinite :
      ∑ j ∈ (active x).filter (M < ·), f j ≤
        ∑' n : ℕ, f (n + (M + 1)) :=
    finite_strictTail_le_tsum_shift f hsum hfnonneg (active x) M
  have htailNonneg : 0 ≤ ∑' n : ℕ, f (n + (M + 1)) :=
    tsum_nonneg fun _ ↦ hfnonneg _
  have hBtail : B * (∑' n : ℕ, f (n + (M + 1))) < ε / 2 := by
    calc
      B * (∑' n : ℕ, f (n + (M + 1))) ≤
          (B + 1) * (∑' n : ℕ, f (n + (M + 1))) := by
        exact mul_le_mul_of_nonneg_right (by linarith) htailNonneg
      _ < (B + 1) * δ := mul_lt_mul_of_pos_left hM hB1
      _ = ε / 2 := by
        dsimp [δ]
        field_simp
  calc
    mediumWeightedTail weight normalizedCount active M x ≤
        B * (∑ j ∈ (active x).filter (M < ·), weight j * ρ ^ j) +
          ∑ j ∈ active x, weight j * error j x :=
      mediumWeightedTail_le_of_aggregateError weight normalizedCount error active
        B ρ M x hweight herr hcnt
    _ ≤ B * (∑' n : ℕ, f (n + (M + 1))) +
          ∑ j ∈ active x, weight j * error j x := by
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left (by simpa [f] using hfinite) hB
    _ ≤ ε := by linarith

/-! ## Prime-indexed geometric majorants -/

/-- Eventually the prime-counting function is at least one half of its PNT
main term. -/
private theorem eventually_primeCounting_half_main :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / (2 * Real.log (x : ℝ)) ≤ (Nat.primeCounting x : ℝ) := by
  have hpnt :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 / 2 by norm_num)
  have hmainPos : ∀ᶠ x : ℕ in atTop,
      0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    positivity
  filter_upwards [herr, hmainPos] with x hx hpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hx
  have hlower :
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
        (Nat.primeCounting x : ℝ) := by
    linarith [neg_abs_le
      ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ))]
  calc
    (x : ℝ) / (2 * Real.log (x : ℝ)) =
        (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by ring
    _ ≤ (Nat.primeCounting x : ℝ) := hlower

/-- A deliberately coarse polynomial upper bound for the zero-indexed nth
prime.  The PNT is used only to obtain this eventual bound. -/
theorem eventually_nthPrime_le_square :
    ∀ᶠ n : ℕ in atTop, Nat.nth Nat.Prime n ≤ (n + 1) ^ 2 := by
  let X : ℕ → ℕ := fun n ↦ (n + 1) ^ 2
  have hXtop : Tendsto X atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun n hn ↦ hn.trans ?_⟩
    dsimp [X]
    nlinarith [Nat.zero_le n]
  have hpnt := hXtop.eventually eventually_primeCounting_half_main
  have hyTop : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlogSmall := hyTop.eventually
    (Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 8 by norm_num))
  filter_upwards [hpnt, hlogSmall, eventually_ge_atTop 2] with n hpi hsmall hn
  let y : ℝ := (n + 1 : ℕ)
  have hypos : 0 < y := by positivity
  have hyone : 1 < y := by
    dsimp [y]
    exact_mod_cast (show 1 < n + 1 by omega)
  have hlogypos : 0 < Real.log y := Real.log_pos hyone
  have hlogy : Real.log y ≤ y / 8 := by
    have habs : |Real.log y| ≤ (1 / 8 : ℝ) * |y| := by
      simpa only [y, id_eq, Real.norm_eq_abs] using hsmall
    rw [abs_of_pos hypos] at habs
    exact (le_abs_self _).trans (by linarith)
  have hlogX : Real.log (X n : ℝ) = 2 * Real.log y := by
    dsimp [X, y]
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow]
    norm_num
  have hlogXpos : 0 < Real.log (X n : ℝ) := by rw [hlogX]; positivity
  have hmain : (n : ℝ) < (X n : ℝ) / (2 * Real.log (X n : ℝ)) := by
    rw [lt_div_iff₀ (mul_pos (by norm_num) hlogXpos)]
    rw [hlogX]
    have hy : y = (n : ℝ) + 1 := by simp [y]
    have hX : (X n : ℝ) = y ^ 2 := by simp [X, y]
    rw [hX]
    nlinarith
  have hcountR : (n : ℝ) < (Nat.primeCounting (X n) : ℝ) := hmain.trans_le hpi
  have hcount : n < Nat.count Nat.Prime (X n + 1) := by
    exact_mod_cast hcountR
  have hnth : Nat.nth Nat.Prime n < X n + 1 := Nat.nth_lt_of_lt_count hcount
  dsimp [X] at hnth ⊢
  omega

/-- Prime-index weights multiplied by a geometric factor form a convergent
series for every ratio of absolute value less than one. -/
theorem summable_nthPrime_mul_geometric { ρ : ℝ } (hρ : |ρ| < 1) :
    Summable (fun j : ℕ ↦ (Nat.nth Nat.Prime j : ℝ) * ρ ^ j) := by
  have hmajorant : Summable
      (fun j : ℕ ↦ 4 * (j : ℝ) ^ 2 * |ρ| ^ j) := by
    simpa only [mul_assoc] using
      ((summable_pow_mul_geometric_of_norm_lt_one 2
        (show ‖|ρ|‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg] using hρ)).mul_left 4)
  apply hmajorant.of_norm_bounded_eventually_nat
  filter_upwards [eventually_nthPrime_le_square, eventually_ge_atTop 1] with j hj hjone
  have hnthnonneg : (0 : ℝ) ≤ (Nat.nth Nat.Prime j : ℕ) := by positivity
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hnthnonneg]
  have hjR : ((Nat.nth Nat.Prime j : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hj
  have hsquare : (((j + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * (j : ℝ) ^ 2 := by
    have hjRone : (1 : ℝ) ≤ j := by exact_mod_cast hjone
    have hjpow : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith [sq_nonneg ((j : ℝ) - 1)]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  exact mul_le_mul_of_nonneg_right (hjR.trans hsquare) (pow_nonneg (abs_nonneg ρ) j)

/-! ## The `x / log x` normalized prime-indexed tail -/

/-- Elliott's normalized medium contribution, indexed by the zero-based
sequence of rational primes.  `active x` is the finite range on which the
sieve estimate is valid (in the application, the indices with
`Nat.nth Nat.Prime j ≤ (log x)^A`). -/
noncomputable def primeIndexedMediumWeightedTail
    (count : ℕ → ℕ → ℝ) (active : ℕ → Finset ℕ)
    (M x : ℕ) : ℝ :=
  mediumWeightedTail (fun j ↦ (Nat.nth Nat.Prime j : ℝ))
    (fun j x ↦ (Real.log (x : ℝ) / (x : ℝ)) * count j x) active M x

theorem primeIndexedMediumWeightedTail_eq
    (count : ℕ → ℕ → ℝ) (active : ℕ → Finset ℕ)
    (M x : ℕ) :
    primeIndexedMediumWeightedTail count active M x =
      (Real.log (x : ℝ) / (x : ℝ)) *
        ∑ j ∈ (active x).filter (M < ·),
          (Nat.nth Nat.Prime j : ℝ) * count j x := by
  rw [primeIndexedMediumWeightedTail, mediumWeightedTail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A raw count bound at scale `x / log x` becomes the normalized main term
`B * ρ^j`; the only remaining error is its aggregate after multiplication
by `log x / x`. -/
theorem primeIndexedMediumWeightedTail_le_of_aggregateError
    (count error : ℕ → ℕ → ℝ) (active : ℕ → Finset ℕ)
    (B ρ : ℝ) (M x : ℕ) (hx : 1 < x)
    (herror : ∀ j ∈ active x, 0 ≤ error j x)
    (hcount : ∀ j ∈ active x,
      count j x ≤ B * ρ ^ j * ((x : ℝ) / Real.log (x : ℝ)) + error j x) :
    primeIndexedMediumWeightedTail count active M x ≤
      B * (∑ j ∈ (active x).filter (M < ·),
        (Nat.nth Nat.Prime j : ℝ) * ρ ^ j) +
      (Real.log (x : ℝ) / (x : ℝ)) *
        ∑ j ∈ active x, (Nat.nth Nat.Prime j : ℝ) * error j x := by
  have hxR : (0 : ℝ) < x := by positivity
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  let c : ℝ := Real.log (x : ℝ) / (x : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hnormalized : ∀ j ∈ active x,
      c * count j x ≤ B * ρ ^ j + c * error j x := by
    intro j hj
    calc
      c * count j x ≤
          c * (B * ρ ^ j * ((x : ℝ) / Real.log (x : ℝ)) + error j x) :=
        mul_le_mul_of_nonneg_left (hcount j hj) hc
      _ = B * ρ ^ j + c * error j x := by
        dsimp [c]
        field_simp
  have hcore := mediumWeightedTail_le_of_aggregateError
    (fun j ↦ (Nat.nth Nat.Prime j : ℝ))
    (fun j _ ↦ c * count j x) (fun j _ ↦ c * error j x)
    active B ρ M x (fun _ ↦ by positivity)
    (fun j hj ↦ mul_nonneg hc (herror j hj)) hnormalized
  have hlhs : primeIndexedMediumWeightedTail count active M x =
      mediumWeightedTail (fun j ↦ (Nat.nth Nat.Prime j : ℝ))
        (fun j _ ↦ c * count j x) active M x := by
    rw [primeIndexedMediumWeightedTail, mediumWeightedTail, mediumWeightedTail]
  rw [hlhs]
  calc
    mediumWeightedTail (fun j ↦ (Nat.nth Nat.Prime j : ℝ))
        (fun j _ ↦ c * count j x) active M x ≤
      B * (∑ j ∈ (active x).filter (M < ·),
        (Nat.nth Nat.Prime j : ℝ) * ρ ^ j) +
        ∑ j ∈ active x, (Nat.nth Nat.Prime j : ℝ) * (c * error j x) := hcore
    _ = B * (∑ j ∈ (active x).filter (M < ·),
        (Nat.nth Nat.Prime j : ℝ) * ρ ^ j) +
      (Real.log (x : ℝ) / (x : ℝ)) *
        ∑ j ∈ active x, (Nat.nth Nat.Prime j : ℝ) * error j x := by
      dsimp [c]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The exact aggregate-error-to-medium-tail theorem at the prime-counting
scale.  It uses the same active range throughout; no upper cutoff or limit is
enlarged in the proof. -/
theorem primeIndexedMediumWeightedTail_eventually_small_of_aggregateError
    (count error : ℕ → ℕ → ℝ) (active : ℕ → Finset ℕ)
    (B ρ : ℝ) (hB : 0 ≤ B) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (herror : ∀ᶠ x : ℕ in atTop, ∀ j ∈ active x, 0 ≤ error j x)
    (hcount : ∀ᶠ x : ℕ in atTop, ∀ j ∈ active x,
      count j x ≤ B * ρ ^ j * ((x : ℝ) / Real.log (x : ℝ)) + error j x)
    (haggregate : Tendsto
      (fun x : ℕ ↦ (Real.log (x : ℝ) / (x : ℝ)) *
        ∑ j ∈ active x, (Nat.nth Nat.Prime j : ℝ) * error j x)
      atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ M X : ℕ, ∀ x : ℕ, X ≤ x →
      primeIndexedMediumWeightedTail count active M x ≤ ε := by
  let c : ℕ → ℝ := fun x ↦ Real.log (x : ℝ) / (x : ℝ)
  let normalizedCount : ℕ → ℕ → ℝ := fun j x ↦ c x * count j x
  let normalizedError : ℕ → ℕ → ℝ := fun j x ↦ c x * error j x
  have hsum : Summable
      (fun j ↦ (Nat.nth Nat.Prime j : ℝ) * ρ ^ j) := by
    apply summable_nthPrime_mul_geometric
    rw [abs_of_nonneg hρ₀]
    exact hρ₁
  have hnerror : ∀ᶠ x : ℕ in atTop,
      ∀ j ∈ active x, 0 ≤ normalizedError j x := by
    filter_upwards [herror, eventually_ge_atTop 2] with x herr hx
    intro j hj
    exact mul_nonneg (by dsimp [c]; positivity) (herr j hj)
  have hncount : ∀ᶠ x : ℕ in atTop,
      ∀ j ∈ active x,
        normalizedCount j x ≤ B * ρ ^ j + normalizedError j x := by
    filter_upwards [hcount, eventually_ge_atTop 2] with x hcnt hx
    have hxR : (0 : ℝ) < x := by positivity
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    have hcx : 0 ≤ c x := by dsimp [c]; positivity
    intro j hj
    dsimp [normalizedCount, normalizedError]
    calc
      c x * count j x ≤
          c x * (B * ρ ^ j * ((x : ℝ) / Real.log (x : ℝ)) + error j x) :=
        mul_le_mul_of_nonneg_left (hcnt j hj) hcx
      _ = B * ρ ^ j + c x * error j x := by
        dsimp [c]
        field_simp
  have hnaggregate : Tendsto
      (fun x ↦ ∑ j ∈ active x,
        (Nat.nth Nat.Prime j : ℝ) * normalizedError j x) atTop (nhds 0) := by
    apply haggregate.congr'
    filter_upwards with x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [normalizedError, c]
    ring
  simpa only [primeIndexedMediumWeightedTail, normalizedCount, c] using
    mediumWeightedTail_eventually_small_of_aggregateError
      (fun j ↦ (Nat.nth Nat.Prime j : ℝ)) normalizedCount normalizedError
      active B ρ (fun _ ↦ by positivity) hB hρ₀ hsum hnerror hncount hnaggregate

end Erdos980.ElliottTail
