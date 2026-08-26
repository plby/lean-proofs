import ErdosProblems.Erdos796.BaselineIdentity
import ErdosProblems.Erdos796.MainReduction
import Mathlib.NumberTheory.Chebyshev

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The analytic baseline

This module isolates the analytic input in the proof of Erdős 796.  Mathlib
does not currently contain the prime number theorem or the second-order
semiprime theorem, so those statements are represented as propositions and
passed to the implication theorems below.  No analytic assertion is installed
as an axiom.
-/

namespace Erdos796

open Filter Topology
open scoped BigOperators Nat.Prime

/-- The sum of the reciprocals of the primes at most `n`. -/
noncomputable def primeHarmonic (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, (p : ℝ)⁻¹

/-- `M` is the Meissel--Mertens constant when the prime harmonic sum minus
`log log n` tends to `M`. -/
def IsMeisselMertensConstant (M : ℝ) : Prop :=
  Tendsto
    (fun n : ℕ => primeHarmonic n - Real.log (Real.log n))
    atTop (nhds M)

/-- The second-order semiprime asymptotic used in the manuscript. -/
def SemiprimeAsymptotic (M : ℝ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      ((semiprimeCount n : ℝ) - leadingTerm n) / secondOrderScale n)
    atTop (nhds M)

/-- A normalized formulation of the prime number theorem. -/
def PrimeNumberTheorem : Prop :=
  Tendsto
    (fun n : ℕ => (Nat.primeCounting n : ℝ) / secondOrderScale n)
    atTop (nhds 1)

/-- The triangular contribution from pairs of primes not exceeding `√n`. -/
def smallPrimeTriangle (n : ℕ) : ℕ :=
  Nat.primeCounting n.sqrt * (Nat.primeCounting n.sqrt + 1) / 2

/-- The prime-count and square-root boundary correction left after the
semiprime term is removed from the exact baseline identity. -/
noncomputable def baselineBoundaryCorrection (n : ℕ) : ℝ :=
  ((Nat.primeCounting n : ℝ) -
      (Nat.primeCounting n.sqrt : ℝ) -
      (smallPrimeTriangle n : ℝ)) /
    secondOrderScale n

/-- The contribution of the single small-prime boundary count is negligible
on the second-order scale. -/
def SqrtPrimeBoundaryNegligible : Prop :=
  Tendsto
    (fun n : ℕ =>
      (Nat.primeCounting n.sqrt : ℝ) / secondOrderScale n)
    atTop (nhds 0)

/-- The contribution of unordered pairs of primes below `√n` is negligible
on the second-order scale. -/
def SqrtPrimePairBoundaryNegligible : Prop :=
  Tendsto
    (fun n : ℕ => (smallPrimeTriangle n : ℝ) / secondOrderScale n)
    atTop (nhds 0)

theorem primeCounting_sqrt_le (n : ℕ) :
    Nat.primeCounting n.sqrt ≤ Nat.primeCounting n :=
  Nat.monotone_primeCounting (Nat.sqrt_le_self n)

theorem smallPrimeTriangle_le_semiprimeCount (n : ℕ) :
    smallPrimeTriangle n ≤ semiprimeCount n := by
  have hcard :
      semiprimeCount n =
        (smallSemiprimePairs n).card + (largeSemiprimePairs n).card := by
    rw [semiprimeCount, semiprimePairs_eq_small_union_large,
      Finset.card_union_of_disjoint (disjoint_small_largeSemiprimePairs n)]
  rw [card_smallSemiprimePairs] at hcard
  simpa [smallPrimeTriangle] using!
    (show Nat.primeCounting n.sqrt * (Nat.primeCounting n.sqrt + 1) / 2 ≤
        semiprimeCount n by omega)

/-- Exact normalized decomposition into the semiprime main term and the
boundary correction. -/
theorem normalized_baseline_eq_semiprime_add_boundary (n : ℕ) :
    ((baseline n : ℝ) - leadingTerm n) / secondOrderScale n =
      ((semiprimeCount n : ℝ) - leadingTerm n) / secondOrderScale n +
        baselineBoundaryCorrection n := by
  have hbase :
      baseline n =
        (Nat.primeCounting n - Nat.primeCounting n.sqrt) +
          (semiprimeCount n - smallPrimeTriangle n) := by
    simpa [smallPrimeTriangle] using! baseline_eq_prime_add_semiprime n
  rw [hbase, Nat.cast_add,
    Nat.cast_sub (primeCounting_sqrt_le n),
    Nat.cast_sub (smallPrimeTriangle_le_semiprimeCount n)]
  unfold baselineBoundaryCorrection
  ring

/-- Natural square root tends to infinity. -/
theorem tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

/-- The real cast of natural square root tends to infinity. -/
theorem tendsto_natSqrtCast_atTop :
    Tendsto (fun n : ℕ => (n.sqrt : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop

/-- Eventually `log n` is at most three times the logarithm of the natural
square root.  The harmless factor `3` avoids any floor-error calculation. -/
theorem eventually_log_le_three_log_sqrt :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ 3 * Real.log (n.sqrt : ℝ) := by
  filter_upwards [eventually_ge_atTop 9] with n hn
  have hsqrt : 3 ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hnlt : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
  have hcube : (n.sqrt + 1) * (n.sqrt + 1) ≤ n.sqrt ^ 3 := by
    nlinarith
  have hnle : (n : ℝ) ≤ (n.sqrt : ℝ) ^ 3 := by
    exact_mod_cast hnlt.le.trans hcube
  calc
    Real.log (n : ℝ) ≤ Real.log ((n.sqrt : ℝ) ^ 3) :=
      Real.log_le_log (by positivity) hnle
    _ = 3 * Real.log (n.sqrt : ℝ) := by
      rw [Real.log_pow]
      norm_num

/-- The scale at `√n` is negligible relative to the scale at `n`. -/
theorem sqrt_scale_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) /
          secondOrderScale n))
      atTop (nhds 0) := by
  have hupper : Tendsto (fun n : ℕ => (3 : ℝ) / (n.sqrt : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natSqrtCast_atTop
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 9] with n hn
    have hsqrt : 3 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by norm_num; omega)
    have hlogsqrt : 0 < Real.log (n.sqrt : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n.sqrt by omega))
    simp only [secondOrderScale]
    positivity
  · filter_upwards [eventually_ge_atTop 9,
      eventually_log_le_three_log_sqrt] with n hn hlog
    have hsqrt : 3 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hxpos : 0 < (n.sqrt : ℝ) := by positivity
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlogsqrt : 0 < Real.log (n.sqrt : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n.sqrt by omega))
    have hsquare : (n.sqrt : ℝ) * (n.sqrt : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sqrt_le n
    unfold secondOrderScale
    calc
      ((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) /
          ((n : ℝ) / Real.log n) =
          (n.sqrt : ℝ) * Real.log n /
            ((n : ℝ) * Real.log (n.sqrt : ℝ)) := by field
      _ ≤ (n.sqrt : ℝ) *
          (3 * Real.log (n.sqrt : ℝ)) /
            ((n : ℝ) * Real.log (n.sqrt : ℝ)) := by gcongr
      _ = 3 * (n.sqrt : ℝ) / (n : ℝ) := by field
      _ ≤ 3 / (n.sqrt : ℝ) := by
        rw [div_le_div_iff₀ hnpos hxpos]
        nlinarith
  · exact hupper

/-- The square of the scale at `√n` is still negligible on the scale at
`n`; this is the estimate needed for pairs of small primes. -/
theorem sqrt_scale_square_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) ^ 2 /
          secondOrderScale n))
      atTop (nhds 0) := by
  have hlogtop : Tendsto (fun n : ℕ => Real.log (n.sqrt : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp tendsto_natSqrtCast_atTop
  have hupper : Tendsto
      (fun n : ℕ => (3 : ℝ) / Real.log (n.sqrt : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogtop
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 9] with n hn
    have hsqrt : 3 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hlogsqrt : 0 < Real.log (n.sqrt : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n.sqrt by omega))
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by norm_num; omega)
    simp only [secondOrderScale]
    positivity
  · filter_upwards [eventually_ge_atTop 9,
      eventually_log_le_three_log_sqrt] with n hn hlog
    have hsqrt : 3 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hxpos : 0 < (n.sqrt : ℝ) := by positivity
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlogsqrt : 0 < Real.log (n.sqrt : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n.sqrt by omega))
    have hsquare : (n.sqrt : ℝ) ^ 2 ≤ (n : ℝ) := by
      simpa [pow_two] using! (show
        (n.sqrt : ℝ) * (n.sqrt : ℝ) ≤ (n : ℝ) by
          exact_mod_cast Nat.sqrt_le n)
    unfold secondOrderScale
    calc
      (((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) ^ 2) /
          ((n : ℝ) / Real.log n) =
          (n.sqrt : ℝ) ^ 2 * Real.log n /
            ((n : ℝ) * Real.log (n.sqrt : ℝ) ^ 2) := by field
      _ ≤ (n.sqrt : ℝ) ^ 2 *
          (3 * Real.log (n.sqrt : ℝ)) /
            ((n : ℝ) * Real.log (n.sqrt : ℝ) ^ 2) := by gcongr
      _ = 3 * (n.sqrt : ℝ) ^ 2 /
          ((n : ℝ) * Real.log (n.sqrt : ℝ)) := by field
      _ ≤ 3 / Real.log (n.sqrt : ℝ) := by
        rw [div_le_div_iff₀ (mul_pos hnpos hlogsqrt) hlogsqrt]
        nlinarith
  · exact hupper

/-- Chebyshev's theorem, pulled back along the natural square root. -/
theorem eventually_primeCounting_sqrt_le :
    ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n.sqrt : ℝ) ≤
        (Real.log 4 + 1) * (n.sqrt : ℝ) /
          Real.log (n.sqrt : ℝ) := by
  have h := tendsto_natSqrtCast_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [h] with n hn
  simpa using! hn

/-- The single-prime square-root boundary estimate follows from Chebyshev's
upper bound and the elementary scale comparison. -/
theorem sqrtPrimeBoundaryNegligible : SqrtPrimeBoundaryNegligible := by
  let C : ℝ := Real.log 4 + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hupper : Tendsto
      (fun n : ℕ => C *
        ((((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) /
          secondOrderScale n)))
      atTop (nhds 0) := by
    simpa using! sqrt_scale_ratio_tendsto_zero.const_mul C
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 9] with n hn
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hscale : 0 < secondOrderScale n := by
      simp only [secondOrderScale]
      positivity
    positivity
  · filter_upwards [eventually_ge_atTop 9,
      eventually_primeCounting_sqrt_le] with n hn hcheb
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hscale : 0 < secondOrderScale n := by
      simp only [secondOrderScale]
      positivity
    change (Nat.primeCounting n.sqrt : ℝ) / secondOrderScale n ≤
      C * (((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) /
        secondOrderScale n)
    calc
      (Nat.primeCounting n.sqrt : ℝ) / secondOrderScale n ≤
          (C * ((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ))) /
            secondOrderScale n := by
        apply div_le_div_of_nonneg_right
        · have hlogsqrt : Real.log (n.sqrt : ℝ) ≠ 0 := by
            have hsqrt : 3 ≤ n.sqrt := by
              rw [Nat.le_sqrt]
              omega
            have : 1 < (n.sqrt : ℝ) := by
              exact_mod_cast (show 1 < n.sqrt by omega)
            exact (Real.log_pos this).ne'
          simpa [C, div_eq_mul_inv, mul_assoc] using! hcheb
        · exact hscale.le
      _ = C * (((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) /
          secondOrderScale n) := by ring
  · exact hupper

/-- For a positive integer `r`, the unordered-pair count `r(r+1)/2` is at
most `r²`. -/
theorem triangle_le_square {r : ℕ} (hr : 0 < r) :
    r * (r + 1) / 2 ≤ r ^ 2 := by
  have hnum : r * (r + 1) ≤ (r ^ 2) * 2 := by
    nlinarith
  have hdiv := Nat.div_mul_le_self (r * (r + 1)) 2
  have htwice : (r * (r + 1) / 2) * 2 ≤ (r ^ 2) * 2 :=
    hdiv.trans hnum
  omega

/-- The small-prime-pair boundary estimate also follows from Chebyshev's
upper bound. -/
theorem sqrtPrimePairBoundaryNegligible :
    SqrtPrimePairBoundaryNegligible := by
  let C : ℝ := Real.log 4 + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hupper : Tendsto
      (fun n : ℕ => C ^ 2 *
        ((((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) ^ 2 /
          secondOrderScale n)))
      atTop (nhds 0) := by
    simpa using! sqrt_scale_square_ratio_tendsto_zero.const_mul (C ^ 2)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 9] with n hn
    have hscale : 0 < secondOrderScale n := by
      simp only [secondOrderScale]
      have hlogn : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    positivity
  · filter_upwards [eventually_ge_atTop 9,
      eventually_primeCounting_sqrt_le] with n hn hcheb
    have hsqrt : 3 ≤ n.sqrt := by
      rw [Nat.le_sqrt]
      omega
    have hscale : 0 < secondOrderScale n := by
      simp only [secondOrderScale]
      have hlogn : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    have hprimeTwo : (2 : ℕ).Prime := Nat.prime_two
    have htwoMem : 2 ∈ Nat.primesLE n.sqrt :=
      Nat.mem_primesLE.mpr ⟨by omega, hprimeTwo⟩
    have hrpos : 0 < Nat.primeCounting n.sqrt := by
      rw [← Nat.primesLE_card_eq_primeCounting]
      exact Finset.card_pos.mpr ⟨2, htwoMem⟩
    have htriangle :
        (smallPrimeTriangle n : ℝ) ≤
          (Nat.primeCounting n.sqrt : ℝ) ^ 2 := by
      exact_mod_cast triangle_le_square hrpos
    have hrootpos : 0 ≤
        (n.sqrt : ℝ) / Real.log (n.sqrt : ℝ) := by
      have hlogsqrt : 0 < Real.log (n.sqrt : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n.sqrt by omega))
      positivity
    have hprime_nonneg : 0 ≤ (Nat.primeCounting n.sqrt : ℝ) := by positivity
    have hcheb' : (Nat.primeCounting n.sqrt : ℝ) ≤
        C * ((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) := by
      simpa [C, div_eq_mul_inv, mul_assoc] using! hcheb
    have hsquare : (Nat.primeCounting n.sqrt : ℝ) ^ 2 ≤
        (C * ((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ))) ^ 2 := by
      nlinarith
    change (smallPrimeTriangle n : ℝ) / secondOrderScale n ≤
      C ^ 2 *
        ((((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) ^ 2 /
          secondOrderScale n))
    calc
      (smallPrimeTriangle n : ℝ) / secondOrderScale n ≤
          (Nat.primeCounting n.sqrt : ℝ) ^ 2 / secondOrderScale n := by
        exact div_le_div_of_nonneg_right htriangle hscale.le
      _ ≤ (C * ((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ))) ^ 2 /
          secondOrderScale n := by
        exact div_le_div_of_nonneg_right hsquare hscale.le
      _ = C ^ 2 *
          ((((n.sqrt : ℝ) / Real.log (n.sqrt : ℝ)) ^ 2 /
            secondOrderScale n)) := by ring
  · exact hupper

/-- The prime-number-theorem input gives the main prime contribution. -/
theorem primeCounting_div_scale_tendsto_one (hPNT : PrimeNumberTheorem) :
    Tendsto
      (fun n : ℕ => (Nat.primeCounting n : ℝ) / secondOrderScale n)
      atTop (nhds 1) :=
  hPNT

/-- The correction is exactly the prime-number-theorem term minus the two
square-root boundary terms. -/
theorem baselineBoundaryCorrection_eq (n : ℕ) :
    baselineBoundaryCorrection n =
      (Nat.primeCounting n : ℝ) / secondOrderScale n -
      (Nat.primeCounting n.sqrt : ℝ) / secondOrderScale n -
      (smallPrimeTriangle n : ℝ) / secondOrderScale n := by
  unfold baselineBoundaryCorrection
  ring

/-- PNT together with the two explicit square-root estimates makes the
boundary correction tend to `1`. -/
theorem baselineBoundaryCorrection_tendsto_one
    (hPNT : PrimeNumberTheorem)
    (hRootPrime : SqrtPrimeBoundaryNegligible)
    (hRootPairs : SqrtPrimePairBoundaryNegligible) :
    Tendsto baselineBoundaryCorrection atTop (nhds 1) := by
  have h := hPNT.sub hRootPrime |>.sub hRootPairs
  simpa only [sub_zero] using!
    h.congr' (Eventually.of_forall fun n =>
      (baselineBoundaryCorrection_eq n).symm)

/-- The complete exact analytic reduction for the baseline: the semiprime
asymptotic, PNT, and the two explicit square-root error estimates imply the
manuscript's baseline asymptotic. -/
theorem baselineAsymptotic_of_analytic_inputs (M : ℝ)
    (hSemiprime : SemiprimeAsymptotic M)
    (hPNT : PrimeNumberTheorem)
    (hRootPrime : SqrtPrimeBoundaryNegligible)
    (hRootPairs : SqrtPrimePairBoundaryNegligible) :
    BaselineAsymptotic M := by
  have hsum := hSemiprime.add
    (baselineBoundaryCorrection_tendsto_one hPNT hRootPrime hRootPairs)
  have hsum' : Tendsto
      (fun n : ℕ =>
        ((semiprimeCount n : ℝ) - leadingTerm n) / secondOrderScale n +
          baselineBoundaryCorrection n)
      atTop (nhds (1 + M)) := by
    simpa [add_comm] using! hsum
  exact hsum'.congr' <| Eventually.of_forall fun n =>
    (normalized_baseline_eq_semiprime_add_boundary n).symm

/-- Version recording that the constant in the semiprime theorem is the
Meissel--Mertens constant. -/
theorem baselineAsymptotic_of_meisselMertens_semiprime (M : ℝ)
    (_hM : IsMeisselMertensConstant M)
    (hSemiprime : SemiprimeAsymptotic M)
    (hPNT : PrimeNumberTheorem)
    (hRootPrime : SqrtPrimeBoundaryNegligible)
    (hRootPairs : SqrtPrimePairBoundaryNegligible) :
    BaselineAsymptotic M :=
  baselineAsymptotic_of_analytic_inputs M hSemiprime hPNT hRootPrime hRootPairs

/-- All square-root boundary terms have been discharged internally, so only
the two genuine analytic inputs remain. -/
theorem baselineAsymptotic_of_semiprime_and_pnt (M : ℝ)
    (hSemiprime : SemiprimeAsymptotic M)
    (hPNT : PrimeNumberTheorem) :
    BaselineAsymptotic M :=
  baselineAsymptotic_of_analytic_inputs M hSemiprime hPNT
    sqrtPrimeBoundaryNegligible sqrtPrimePairBoundaryNegligible

end Erdos796
