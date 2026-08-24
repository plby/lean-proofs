/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.StructuredCount

/-!
# Erdős 360: a sharp direct-prime count

The deliberately coarse constants in `StructuredCount` are enough to show
that the prime-only test set has the right order of magnitude, but not enough
for the unused-mass ledger in the CFP lower-bound argument.  This file keeps
the construction unchanged and sharpens only its finite cardinal estimate.

There are three quantitative inputs.  All have eventual proofs in the
intended diagonal range.

* the dyadic prime number theorem is used with relative constant `19/20`;
* every divisor fibre has scale at least twenty, controlling the integer
  floor in `y / u` with another factor `19/20`;
* the reciprocal-divisor tail and the deletion of prime factors of the
  target each consume one percent of the natural main scale.

The result retains one fifth of
`(n / φ(n)) y / log y`.  A final corollary records the exact additional
Mertens/logarithm comparison which turns this into the source constant
`initialMissingEulerProduct n h * y / 8`.
-/

namespace Erdos360

open Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

/-! ## A sharper dyadic PNT threshold -/

/-- One-percent relative-error bounds for the prime-counting function. -/
theorem eventually_primeCounting_hundredth_bounds :
    ∀ᶠ x : ℕ in atTop,
      (99 / 100 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
          (Nat.primeCounting x : ℝ) ∧
      (Nat.primeCounting x : ℝ) ≤
          (101 / 100 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hpnt :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 / 100 by norm_num)
  have hmainPos : ∀ᶠ x : ℕ in atTop,
      0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    positivity
  filter_upwards [herr, hmainPos] with x hx hpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hx
  constructor <;> linarith [le_abs_self
    ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ)),
    neg_abs_le
      ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ))]

/-- Eventually `log (2x)` is at most `101/100` times `log x`. -/
theorem eventually_log_two_mul_le_hundred_one_hundredths :
    ∀ᶠ x : ℕ in atTop,
      Real.log (2 * x : ℝ) ≤
        (101 / 100 : ℝ) * Real.log (x : ℝ) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ x : ℕ in atTop,
      100 * Real.log 2 ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop (100 * Real.log 2))
  filter_upwards [hevent, eventually_ge_atTop 1] with x hx hxone
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  rw [show (2 * x : ℝ) = 2 * (x : ℝ) by norm_num,
    Real.log_mul (by norm_num) hxpos.ne']
  linarith

/-- The PNT with one-percent errors gives a `19/20` dyadic lower bound. -/
theorem eventually_dyadicPrimes_card_nineteen_twentieth_lower :
    ∀ᶠ x : ℕ in atTop,
      (19 / 20 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
        ((Erdos446.dyadicPrimes x).card : ℝ) := by
  have hpnt := eventually_primeCounting_hundredth_bounds
  have htwoTop : Tendsto (fun x : ℕ ↦ 2 * x) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ Filter.tendsto_id
    filter_upwards with x
    simpa only [id_eq] using (show x ≤ 2 * x by omega)
  have hpntTwo := htwoTop.eventually eventually_primeCounting_hundredth_bounds
  have hlog := eventually_log_two_mul_le_hundred_one_hundredths
  have hlogPos : ∀ᶠ x : ℕ in atTop, 0 < Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  filter_upwards [hpnt, hpntTwo, hlog, hlogPos,
      eventually_ge_atTop 3] with x hx hxTwo hlog hlogPos hxthree
  norm_num [Nat.cast_mul] at hxTwo
  have hlogTwoPos : 0 < Real.log (2 * x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 2 * x by omega))
  have hmono : Nat.primesLE x ⊆ Nat.primesLE (2 * x) :=
    Nat.primesLE_mono (by omega)
  have hcard : (Erdos446.dyadicPrimes x).card =
      Nat.primeCounting (2 * x) - Nat.primeCounting x := by
    rw [Erdos446.dyadicPrimes, Finset.card_sdiff_of_subset hmono,
      Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting]
  have hpiMono : Nat.primeCounting x ≤ Nat.primeCounting (2 * x) := by
    simpa [← Nat.primesLE_card_eq_primeCounting] using
      Finset.card_le_card hmono
  have hcardR : ((Erdos446.dyadicPrimes x).card : ℝ) =
      (Nat.primeCounting (2 * x) : ℝ) -
        (Nat.primeCounting x : ℝ) := by
    rw [hcard, Nat.cast_sub hpiMono]
  rw [hcardR]
  have hratio :
      (x : ℝ) / Real.log (x : ℝ) ≤
        (101 / 100 : ℝ) *
          ((x : ℝ) / Real.log (2 * x : ℝ)) := by
    have hxnonneg : (0 : ℝ) ≤ x := by positivity
    have hmul :
        (x : ℝ) * Real.log (2 * x : ℝ) ≤
          ((101 / 100 : ℝ) * (x : ℝ)) * Real.log (x : ℝ) := by
      nlinarith [mul_nonneg hxnonneg (sub_nonneg.mpr hlog)]
    calc
      (x : ℝ) / Real.log (x : ℝ) ≤
          ((101 / 100 : ℝ) * (x : ℝ)) /
            Real.log (2 * x : ℝ) :=
        (div_le_div_iff₀ hlogPos hlogTwoPos).2 hmul
      _ = (101 / 100 : ℝ) *
          ((x : ℝ) / Real.log (2 * x : ℝ)) := by ring
  have hmainNonneg : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    positivity
  calc
    (19 / 20 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
        (9599 / 10100 : ℝ) *
          ((x : ℝ) / Real.log (x : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) hmainNonneg
    _ ≤ (99 / 100 : ℝ) *
          ((2 * x : ℝ) / Real.log (2 * x : ℝ)) -
        (101 / 100 : ℝ) *
          ((x : ℝ) / Real.log (x : ℝ)) := by
      have hscaled := mul_le_mul_of_nonneg_left hratio
        (show (0 : ℝ) ≤ 198 / 101 by norm_num)
      calc
        (9599 / 10100 : ℝ) *
              ((x : ℝ) / Real.log (x : ℝ)) =
            (198 / 101 : ℝ) *
                ((x : ℝ) / Real.log (x : ℝ)) -
              (101 / 100 : ℝ) *
                ((x : ℝ) / Real.log (x : ℝ)) := by ring
        _ ≤ (198 / 100 : ℝ) *
                ((x : ℝ) / Real.log (2 * x : ℝ)) -
              (101 / 100 : ℝ) *
                ((x : ℝ) / Real.log (x : ℝ)) := by
          exact sub_le_sub_right (by nlinarith) _
        _ = (99 / 100 : ℝ) *
              ((2 * x : ℝ) / Real.log (2 * x : ℝ)) -
            (101 / 100 : ℝ) *
              ((x : ℝ) / Real.log (x : ℝ)) := by
          norm_num [Nat.cast_mul]
          ring
    _ ≤ (Nat.primeCounting (2 * x) : ℝ) -
          (Nat.primeCounting x : ℝ) := sub_le_sub hxTwo.1 hx.2

/-- Threshold form of the preceding eventual dyadic PNT estimate. -/
theorem exists_dyadicPrimes_card_nineteen_twentieth_threshold :
    ∃ T : ℕ, ∀ X : ℕ, T ≤ X →
      (19 / 20 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ) := by
  exact Filter.eventually_atTop.mp
    eventually_dyadicPrimes_card_nineteen_twentieth_lower

/-! ## Floor and logarithm comparison in every divisor fibre -/

/-- If `y/u ≥ 20`, replacing the real quotient by `⌊y/u⌋` loses at
most a factor `19/20`; replacing its logarithm by `log y` only improves the
lower bound. -/
lemma nineteen_twentieth_y_log_inv_le_dyadic_ratio
    {y u : ℕ} (hu : 0 < u) (hsmall : 20 * u ≤ y) :
    (19 / 20 : ℝ) *
        (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹) ≤
      ((y / u : ℕ) : ℝ) / Real.log ((y / u : ℕ) : ℝ) := by
  have hXtwenty : 20 ≤ y / u := by
    apply (Nat.le_div_iff_mul_le hu).2
    simpa [Nat.mul_comm] using hsmall
  have hyTwenty : 20 ≤ y :=
    hsmall.trans' (Nat.le_mul_of_pos_right 20 hu)
  have hlogX : 0 < Real.log ((y / u : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y / u by omega))
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogle : Real.log ((y / u : ℕ) : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.div_le_self y u
  have hltNat : y < u * (y / u + 1) := Nat.lt_mul_div_succ y hu
  have hlt : (y : ℝ) < (u : ℝ) * ((y / u : ℕ) + 1) := by
    exact_mod_cast hltNat
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hfloor :
      (19 / 20 : ℝ) * ((y : ℝ) / (u : ℝ)) ≤ (y / u : ℕ) := by
    rw [← mul_div_assoc, div_le_iff₀ huR]
    have hXcast : (20 : ℝ) ≤ (y / u : ℕ) := by exact_mod_cast hXtwenty
    nlinarith
  have hratio :
      ((19 / 20 : ℝ) * ((y : ℝ) / (u : ℝ))) /
          Real.log (y : ℝ) ≤
        ((y / u : ℕ) : ℝ) / Real.log ((y / u : ℕ) : ℝ) := by
    exact div_le_div₀ (by positivity) hfloor hlogX hlogle
  calc
    (19 / 20 : ℝ) *
          (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹) =
        ((19 / 20 : ℝ) * ((y : ℝ) / (u : ℝ))) /
          Real.log (y : ℝ) := by
      field_simp [huR.ne', hlogY.ne']
      <;> ring
    _ ≤ ((y / u : ℕ) : ℝ) /
        Real.log ((y / u : ℕ) : ℝ) := hratio

/-! ## The sharp finite count -/

/-- With one-percent tail and deletion budgets, the prime-only test set
retains one fifth of the natural direct-prime main term. -/
theorem ratio_y_div_log_fifth_le_primeStructuredTestSet_card
    {n y U T : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hPNT : ∀ X : ℕ, T ≤ X →
      (19 / 20 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ))
    (hscale : ∀ u ∈ boundedTargetDivisors n U, T ≤ y / u)
    (hsmall : ∀ u ∈ boundedTargetDivisors n U, 20 * u ≤ y)
    (htail : (n.divisors.card : ℝ) / (U + 1) ≤
      (1 / 100 : ℝ) * ((n : ℝ) / Nat.totient n))
    (herror : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (100 * Real.log (y : ℝ))) :
    ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (5 * Real.log (y : ℝ)) ≤
      ((primeStructuredTestSet n y U).card : ℝ) := by
  have hone : 1 ∈ boundedTargetDivisors n U :=
    mem_boundedTargetDivisors.mpr ⟨one_dvd n, hn.ne', hU⟩
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < y by
        have := hsmall 1 hone
        omega))
  have hratio0 : 0 ≤ (n : ℝ) / Nat.totient n := by positivity
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hfull := totientRatio_quarter_le_sum_divisors_inv hn
  have hlarge := sum_large_divisors_inv_le n U
  rw [sum_divisors_inv_eq_bounded_add_large (U := U) hn.ne'] at hfull
  have hrecip :
      (6 / 25 : ℝ) * ((n : ℝ) / Nat.totient n) ≤
        ∑ u ∈ boundedTargetDivisors n U, (u : ℝ)⁻¹ := by
    nlinarith
  have hfibre : ∀ u ∈ boundedTargetDivisors n U,
      (361 / 400 : ℝ) *
          (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹) ≤
        ((Erdos446.dyadicPrimes (y / u)).card : ℝ) := by
    intro u hu
    have hcomp := nineteen_twentieth_y_log_inv_le_dyadic_ratio
      (boundedTargetDivisor_pos hu) (hsmall u hu)
    have hp := hPNT _ (hscale u hu)
    calc
      (361 / 400 : ℝ) *
            (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹) =
          (19 / 20 : ℝ) *
            ((19 / 20 : ℝ) *
              (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹)) := by ring
      _ ≤ (19 / 20 : ℝ) *
          (((y / u : ℕ) : ℝ) /
            Real.log ((y / u : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcomp (by norm_num)
      _ ≤ ((Erdos446.dyadicPrimes (y / u)).card : ℝ) := hp
  have hmain :
      (21 / 100 : ℝ) *
          (((n : ℝ) / Nat.totient n) * (y : ℝ) /
            Real.log (y : ℝ)) ≤
        ∑ u ∈ boundedTargetDivisors n U,
          ((Erdos446.dyadicPrimes (y / u)).card : ℝ) := by
    calc
      (21 / 100 : ℝ) *
            (((n : ℝ) / Nat.totient n) * (y : ℝ) /
              Real.log (y : ℝ)) ≤
          (361 / 400 : ℝ) *
            ((y : ℝ) / Real.log (y : ℝ)) *
              ((6 / 25 : ℝ) * ((n : ℝ) / Nat.totient n)) := by
        have hbase : 0 ≤
            ((n : ℝ) / Nat.totient n) * (y : ℝ) /
              Real.log (y : ℝ) := by positivity
        calc
          (21 / 100 : ℝ) *
                (((n : ℝ) / Nat.totient n) * (y : ℝ) /
                  Real.log (y : ℝ)) ≤
              ((361 / 400 : ℝ) * (6 / 25 : ℝ)) *
                (((n : ℝ) / Nat.totient n) * (y : ℝ) /
                  Real.log (y : ℝ)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hbase
          _ = (361 / 400 : ℝ) *
                ((y : ℝ) / Real.log (y : ℝ)) *
                  ((6 / 25 : ℝ) * ((n : ℝ) / Nat.totient n)) := by
            ring
      _ ≤ (361 / 400 : ℝ) *
            ((y : ℝ) / Real.log (y : ℝ)) *
              (∑ u ∈ boundedTargetDivisors n U, (u : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = ∑ u ∈ boundedTargetDivisors n U,
            (361 / 400 : ℝ) *
              (((y : ℝ) / Real.log (y : ℝ)) * (u : ℝ)⁻¹) := by
        simp [Finset.mul_sum]
        ring
      _ ≤ ∑ u ∈ boundedTargetDivisors n U,
          ((Erdos446.dyadicPrimes (y / u)).card : ℝ) := by
        exact Finset.sum_le_sum fun u hu ↦ hfibre u hu
  have hsum :
      (∑ u ∈ boundedTargetDivisors n U,
        (((Erdos446.dyadicPrimes (y / u)).card : ℝ) -
          n.primeFactors.card)) ≤
        ((primeStructuredTestSet n y U).card : ℝ) := by
    rw [card_primeStructuredTestSet]
    push_cast
    apply Finset.sum_le_sum
    intro u hu
    exact dyadicPrimes_card_cast_sub_primeFactors_le_primeStructured n _
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have htarget :
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (5 * Real.log (y : ℝ)) =
        (1 / 5 : ℝ) *
          (((n : ℝ) / Nat.totient n) * (y : ℝ) /
            Real.log (y : ℝ)) := by ring
  rw [htarget]
  have herr' : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      (1 / 100 : ℝ) *
        (((n : ℝ) / Nat.totient n) * (y : ℝ) /
          Real.log (y : ℝ)) := by
    convert herror using 1 <;> ring
  linarith

/-- The exact sharp count needed by the CFP unused-mass ledger.  The final
hypothesis is a transparent finite Mertens/log comparison; asymptotically it
has ample slack because the left side is equivalent to
`5 * exp(-γ) * (log y / log h) * n/φ(n)` and `log y / log h → 2`.
-/
theorem initialMissingEulerProduct_mul_y_div_eight_le_primeStructuredTestSet_card
    {n h y U T : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hPNT : ∀ X : ℕ, T ≤ X →
      (19 / 20 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ))
    (hscale : ∀ u ∈ boundedTargetDivisors n U, T ≤ y / u)
    (hsmall : ∀ u ∈ boundedTargetDivisors n U, 20 * u ≤ y)
    (htail : (n.divisors.card : ℝ) / (U + 1) ≤
      (1 / 100 : ℝ) * ((n : ℝ) / Nat.totient n))
    (herror : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (100 * Real.log (y : ℝ)))
    (hMertensLog :
      5 * initialMissingEulerProduct n h * Real.log (y : ℝ) ≤
        8 * ((n : ℝ) / Nat.totient n)) :
    initialMissingEulerProduct n h * (y : ℝ) / 8 ≤
      ((primeStructuredTestSet n y U).card : ℝ) := by
  have hcount := ratio_y_div_log_fifth_le_primeStructuredTestSet_card
    hn hU hPNT hscale hsmall htail herror
  have hone : 1 ∈ boundedTargetDivisors n U :=
    mem_boundedTargetDivisors.mpr ⟨one_dvd n, hn.ne', hU⟩
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < y by
        have := hsmall 1 hone
        omega))
  have hy0 : (0 : ℝ) ≤ y := by positivity
  calc
    initialMissingEulerProduct n h * (y : ℝ) / 8 ≤
        ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (5 * Real.log (y : ℝ)) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
        (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hMertensLog hy0]
    _ ≤ ((primeStructuredTestSet n y U).card : ℝ) := hcount

end Erdos360
