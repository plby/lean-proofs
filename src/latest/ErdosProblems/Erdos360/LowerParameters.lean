/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.Core
import ErdosProblems.Erdos387.BinomialEulerProductSharp

/-!
# Erdős 360: diagonal lower-bound parameters

This file isolates the part of the lower-bound argument which is
independent of the finite subset-sum theorem.  There are two separate prime
parameters in the CFP paper:

* `r` in `W(r)` is a **number of initial primes**;
* the second argument of `missingEulerProduct` is a **prime-value cutoff**.

The latter is what is already available in `Erdos360.Core`.  We prove its
sharp elementary two-sided bounds, the floor facts for the color parameter,
and an integer selector for the auxiliary length `y`.  The selector is stated
abstractly enough that it can also be reused after the initial-prime Euler
product is introduced.
-/

namespace Erdos360

open Filter
open scoped BigOperators

/-! ## The integral number of colors -/

/-- The canonical rounded color parameter for the diagonal lower bound. -/
noncomputable def lowerColorCount (c : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (c * resolutionScale n)

lemma lowerColorCount_bounds {c : ℝ} {n : ℕ}
    (hc : 0 ≤ c) (hscale : 0 ≤ resolutionScale n) :
    (lowerColorCount c n : ℝ) ≤ c * resolutionScale n ∧
      c * resolutionScale n < lowerColorCount c n + 1 := by
  constructor
  · simpa [lowerColorCount] using
      Nat.floor_le (mul_nonneg hc hscale)
  · simpa [lowerColorCount] using
      Nat.lt_floor_add_one (c * resolutionScale n)

lemma lowerColorCount_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (lowerColorCount c) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (resolutionScale_tendsto_atTop.const_mul_atTop hc)

lemma eventually_three_le_lowerColorCount {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ lowerColorCount c n :=
  (lowerColorCount_tendsto_atTop hc).eventually (eventually_ge_atTop 3)

/-- The diagonal color parameter is eventually well beyond the threshold
`10 log n / log log n` used in CFP's initial-prime Euler-product estimate.
Only the already proved coarse polynomial lower bound for
`resolutionScale` is needed here. -/
lemma eventually_ten_log_div_loglog_le_lowerColorCount
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      10 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤
        (lowerColorCount c n : ℝ) := by
  have hlarge :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1800 / c))
  filter_upwards [eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_resolutionScale_pos, hlarge] with
      n hn hnlog hnloglog hnscale hnlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let P := Real.rpow (n : ℝ) (1 / 5 : ℝ)
  let Q := Real.rpow (n : ℝ) (1 / 10 : ℝ)
  have hP : 1 ≤ P := by
    dsimp [P]
    exact Real.one_le_rpow hnOne (by norm_num)
  have hPQ : Real.rpow (n : ℝ) (3 / 10 : ℝ) = P * Q := by
    have h := Real.rpow_add hnR (1 / 5 : ℝ) (1 / 10 : ℝ)
    dsimp [P, Q]
    convert h using 1 <;> norm_num
  have hlogP : Real.log (n : ℝ) ≤ 5 * P := by
    have h := Real.log_le_rpow_div hnR.le
      (show (0 : ℝ) < 1 / 5 by norm_num)
    simpa [P, div_eq_mul_inv, mul_comm] using h
  have hQ : 1800 / c ≤ Q := by simpa [Q] using hnlarge
  have hcQ : 1800 ≤ c * Q := by
    have := (div_le_iff₀ hc).mp hQ
    nlinarith
  have hscaleLower :=
    resolutionScale_ge_rpow_three_tenths hn hnlog hnloglog
  have hfloorUpper := (lowerColorCount_bounds hc.le hnscale.le).2
  have hcolor : 10 * Real.log (n : ℝ) + 1 ≤
      c * resolutionScale n := by
    calc
      10 * Real.log (n : ℝ) + 1 ≤ 51 * P := by nlinarith
      _ ≤ c * ((1 / 30 : ℝ) * Real.rpow (n : ℝ) (3 / 10 : ℝ)) := by
        rw [hPQ]
        have hP0 : 0 ≤ P := zero_le_one.trans hP
        nlinarith
      _ ≤ c * resolutionScale n :=
        mul_le_mul_of_nonneg_left hscaleLower hc.le
  have hten : 10 * Real.log (n : ℝ) ≤
      (lowerColorCount c n : ℝ) := by
    nlinarith
  have hnum : 0 ≤ 10 * Real.log (n : ℝ) := by positivity
  exact (div_le_self hnum hnloglog).trans hten

/-! ## The Euler product with a prime-value cutoff -/

/-- The missing-prime product with the parameter interpreted, as in CFP, as
a **number of initial primes**.  Indexing is zero-based in Lean, hence the
cutoff `primeAt (h - 1)`.  The convention at `h = 0` is irrelevant to the
eventual argument. -/
noncomputable def initialMissingEulerProduct (n h : ℕ) : ℝ :=
  missingEulerProduct n (primeAt (h - 1))

lemma oddFirstMissingPrimes_eq_missingPrimesUpTo_primeAt_pred
    {n h : ℕ} (hh : 0 < h) :
    oddFirstMissingPrimes n h = missingPrimesUpTo n (primeAt (h - 1)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨i, hi, rfl⟩, hp2, hpn⟩ := mem_oddFirstMissingPrimes.mp hp
    apply mem_missingPrimesUpTo.mpr
    refine ⟨hp2, ?_, Nat.prime_nth_prime i, hpn⟩
    apply (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
    omega
  · intro hp
    obtain ⟨hp2, hple, hpprime, hpn⟩ := mem_missingPrimesUpTo.mp hp
    let i := Nat.count Nat.Prime p
    have hip : primeAt i = p := Nat.nth_count hpprime
    have hih : i < h := by
      by_contra hnot
      have hle : h ≤ i := Nat.le_of_not_gt hnot
      have hpredlt : h - 1 < i := by omega
      have hstrict : primeAt (h - 1) < primeAt i :=
        (Nat.nth_strictMono Nat.infinite_setOfPred_prime) hpredlt
      rw [hip] at hstrict
      omega
    exact mem_oddFirstMissingPrimes.mpr ⟨⟨i, hih, hip⟩, hp2, hpn⟩

lemma initialMissingEulerProduct_eq_prod_oddFirstMissingPrimes
    {n h : ℕ} (hh : 0 < h) :
    initialMissingEulerProduct n h =
      ∏ p ∈ oddFirstMissingPrimes n h,
        (1 - Erdos851.oneShiftDensity p) := by
  unfold initialMissingEulerProduct missingEulerProduct
  rw [oddFirstMissingPrimes_eq_missingPrimesUpTo_primeAt_pred hh]

lemma one_le_residualCofactorOrdinaryInverseProduct (n r : ℕ) :
    1 ≤ Erdos4.residualCofactorOrdinaryInverseProduct r n := by
  unfold Erdos4.residualCofactorOrdinaryInverseProduct
  apply Finset.one_le_prod
  intro p hp
  exact Erdos4.one_le_oneShift_inverseFactor
    ((Erdos851.mem_sievePrimes.mp
      (Finset.mem_filter.mp hp).1).2.2)

lemma oneShiftLocalEulerProduct_pos (z y : ℕ) :
    0 < Erdos851.localEulerProduct Erdos851.oneShiftDensity z y := by
  unfold Erdos851.localEulerProduct
  apply Finset.prod_pos
  intro p hp
  exact Erdos851.oneShift_localFactor_pos
    (Erdos851.mem_sievePrimes.mp hp).2.2

/-- Removing the prime factors of the target can only increase the ordinary
Mertens product.  The explicit constant comes from the proved Mertens bound
`partialEulerProduct_le_three_mul_log`. -/
lemma missingEulerProduct_cutoff_lower {n r : ℕ} (hr : 3 ≤ r) :
    2 / (3 * Real.log (r : ℝ)) ≤ missingEulerProduct n r := by
  have hlog : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hpartial : partial_euler_product r ≤ 3 * Real.log (r : ℝ) :=
    Erdos387.BinomialEulerProductSharp.partialEulerProduct_le_three_mul_log hr
  have hpartialPos : 0 < partial_euler_product r :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hall : 2 / (3 * Real.log (r : ℝ)) ≤
      Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 r := by
    rw [Erdos4.oneShift_localEulerProduct_two_eq r (by omega)]
    exact div_le_div_of_nonneg_left (by norm_num) hpartialPos hpartial
  rw [missingEulerProduct_eq_all_mul_targetInverse]
  exact hall.trans (le_mul_of_one_le_right
    (oneShiftLocalEulerProduct_pos 2 r).le
    (one_le_residualCofactorOrdinaryInverseProduct n r))

/-- The matching upper estimate, retaining the exact target correction
`n / φ(n)`.  Unlike the existential Mertens bound used by the upper-bound
construction, this version has the explicit harmless constant `2`. -/
lemma missingEulerProduct_cutoff_upper {n r : ℕ}
    (hn : 0 < n) (hr : 3 ≤ r) :
    missingEulerProduct n r ≤
      2 * ((n : ℝ) / Nat.totient n) / Real.log (r : ℝ) := by
  have hlog : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hpartial : Real.log (r : ℝ) ≤ partial_euler_product r :=
    Erdos387.BinomialEulerProductSharp.log_le_partialEulerProduct r
  have hpartialPos : 0 < partial_euler_product r :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hall : Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 r ≤
      2 / Real.log (r : ℝ) := by
    rw [Erdos4.oneShift_localEulerProduct_two_eq r (by omega)]
    exact div_le_div_of_nonneg_left (by norm_num) hlog hpartial
  have hcorr := Erdos4.residualCofactorOrdinaryInverseProduct_le_ratio
    (y := r) hn
  have hcorrNonneg : 0 ≤
      Erdos4.residualCofactorOrdinaryInverseProduct r n := by
    exact (one_le_residualCofactorOrdinaryInverseProduct n r).trans' zero_le_one
  rw [missingEulerProduct_eq_all_mul_targetInverse]
  calc
    Erdos851.localEulerProduct Erdos851.oneShiftDensity 2 r *
          Erdos4.residualCofactorOrdinaryInverseProduct r n ≤
        (2 / Real.log (r : ℝ)) * ((n : ℝ) / Nat.totient n) := by
      exact mul_le_mul hall hcorr hcorrNonneg
        (by positivity)
    _ = 2 * ((n : ℝ) / Nat.totient n) /
          Real.log (r : ℝ) := by ring

lemma missingEulerProduct_cutoff_inv_upper {n r : ℕ} (hr : 3 ≤ r) :
    (missingEulerProduct n r)⁻¹ ≤
      (3 / 2 : ℝ) * Real.log (r : ℝ) := by
  have hlog : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hV := missingEulerProduct_cutoff_lower (n := n) hr
  have hVpos := missingEulerProduct_pos n r
  have hbase : 0 < 2 / (3 * Real.log (r : ℝ)) := by positivity
  have hinv := (inv_le_inv₀ hVpos hbase).2 hV
  calc
    (missingEulerProduct n r)⁻¹ ≤
        (2 / (3 * Real.log (r : ℝ)))⁻¹ := hinv
    _ = (3 / 2 : ℝ) * Real.log (r : ℝ) := by
      field_simp [hlog.ne']

lemma initialMissingEulerProduct_lower {n h : ℕ} (hh : 2 ≤ h) :
    2 / (3 * Real.log (primeAt (h - 1) : ℝ)) ≤
      initialMissingEulerProduct n h := by
  apply missingEulerProduct_cutoff_lower
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
    (by omega : 1 ≤ h - 1) |>.trans' (by norm_num)

lemma initialMissingEulerProduct_upper {n h : ℕ}
    (hn : 0 < n) (hh : 2 ≤ h) :
    initialMissingEulerProduct n h ≤
      2 * ((n : ℝ) / Nat.totient n) /
        Real.log (primeAt (h - 1) : ℝ) := by
  apply missingEulerProduct_cutoff_upper hn
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
    (by omega : 1 ≤ h - 1) |>.trans' (by norm_num)

/-! ## Exact integral selection of the length parameter -/

/-- The real quantity `r * n / V`, where
`V = (n / φ(n)) * τ`, which occurs under the square root in CFP Claim B.4
after specializing `m = n`.  The product `missingEulerProduct` is `V` (up to
the harmless convention of omitting the prime `2`), not `τ` itself. -/
noncomputable def lowerParameterMass (n r : ℕ) : ℝ :=
  (r : ℝ) * n / missingEulerProduct n r

/-- Choosing `ceil (4 sqrt A)` gives the entire CFP window
`15 A ≤ y² < 25 A` as soon as `A ≥ 1`.  This avoids any appeal to an
unspecified "integer between two close real numbers". -/
noncomputable def integerSqrtWindow (A : ℝ) : ℕ :=
  Nat.ceil (4 * Real.sqrt A)

lemma integerSqrtWindow_bounds {A : ℝ} (hA : 1 ≤ A) :
    15 * A ≤ (integerSqrtWindow A : ℝ) ^ 2 ∧
      (integerSqrtWindow A : ℝ) ^ 2 < 25 * A := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hsqrt : 1 ≤ Real.sqrt A := by
    rw [Real.le_sqrt (by norm_num) hA0]
    nlinarith
  have hlo : 4 * Real.sqrt A ≤ (integerSqrtWindow A : ℝ) := by
    simpa [integerSqrtWindow] using Nat.le_ceil (4 * Real.sqrt A)
  have hhi : (integerSqrtWindow A : ℝ) < 4 * Real.sqrt A + 1 := by
    simpa [integerSqrtWindow] using
      Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (Real.sqrt_nonneg A))
  have hsqrtSq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA0
  constructor
  · have hy0 : 0 ≤ (integerSqrtWindow A : ℝ) := by positivity
    nlinarith
  · nlinarith

lemma le_integerSqrtWindow_of_sq_le {A x : ℝ}
    (hA : 1 ≤ A) (hx : 0 ≤ x) (hxsq : x ^ 2 ≤ 15 * A) :
    x ≤ (integerSqrtWindow A : ℝ) := by
  have hwindow := (integerSqrtWindow_bounds hA).1
  have hy : 0 ≤ (integerSqrtWindow A : ℝ) := by positivity
  nlinarith

lemma integerSqrtWindow_lt_of_sq_lt {A B : ℝ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hmass : 25 * A ≤ B ^ 2) :
    (integerSqrtWindow A : ℝ) < B := by
  have hwindow := (integerSqrtWindow_bounds hA).2
  have hy : 0 ≤ (integerSqrtWindow A : ℝ) := by positivity
  nlinarith

/-- Canonical auxiliary integer for the diagonal lower-bound parameter
window, using the cutoff Euler product currently defined in `Core`. -/
noncomputable def lowerY (n r : ℕ) : ℕ :=
  integerSqrtWindow (lowerParameterMass n r)

/-- The actual CFP diagonal mass, where the color parameter counts initial
primes rather than serving as a prime-value cutoff. -/
noncomputable def initialLowerParameterMass (n r : ℕ) : ℝ :=
  (r : ℝ) * n / initialMissingEulerProduct n r

/-- The canonical `y` for the actual initial-prime version of CFP. -/
noncomputable def initialLowerY (n r : ℕ) : ℕ :=
  integerSqrtWindow (initialLowerParameterMass n r)

lemma initialMissingEulerProduct_pos (n r : ℕ) :
    0 < initialMissingEulerProduct n r := by
  exact missingEulerProduct_pos n (primeAt (r - 1))

lemma initialMissingEulerProduct_le_one (n r : ℕ) :
    initialMissingEulerProduct n r ≤ 1 := by
  unfold initialMissingEulerProduct missingEulerProduct
  apply Finset.prod_le_one
  · intro p hp
    exact (Erdos851.oneShift_localFactor_pos
      (mem_missingPrimesUpTo.mp hp).2.2.1).le
  · intro p hp
    have hdensity : 0 ≤ Erdos851.oneShiftDensity p := by
      unfold Erdos851.oneShiftDensity
      positivity
    linarith

lemma one_le_initialLowerParameterMass {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) :
    1 ≤ initialLowerParameterMass n r := by
  have hVpos := initialMissingEulerProduct_pos n r
  unfold initialLowerParameterMass
  rw [le_div_iff₀ hVpos]
  have hrone : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [initialMissingEulerProduct_le_one n r]

lemma initialLowerY_parameter_window {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) :
    15 * initialLowerParameterMass n r ≤ (initialLowerY n r : ℝ) ^ 2 ∧
      (initialLowerY n r : ℝ) ^ 2 <
        25 * initialLowerParameterMass n r := by
  simpa [initialLowerY] using
    integerSqrtWindow_bounds (one_le_initialLowerParameterMass hn hr)

/-- Exact interface supplied by CFP equation (34), adjusted for Core's
convention of omitting the prime `2`.  This is the only genuinely new
number-theoretic estimate still needed by the diagonal parameter selector.
The parameter `r` counts initial primes. -/
def InitialMissingMertensBounds (n r : ℕ) : Prop :=
  0 < Real.log (r : ℝ) ∧
    ((n : ℝ) / Nat.totient n) /
          (4 * Real.log (r : ℝ)) ≤ initialMissingEulerProduct n r ∧
    initialMissingEulerProduct n r ≤
      2 * ((n : ℝ) / Nat.totient n) / Real.log (r : ℝ)

lemma initialLowerParameterMass_bounds {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r)
    (hMertens : InitialMissingMertensBounds n r) :
    (r : ℝ) * Nat.totient n * Real.log (r : ℝ) / 2 ≤
        initialLowerParameterMass n r ∧
      initialLowerParameterMass n r ≤
        4 * r * Nat.totient n * Real.log (r : ℝ) := by
  rcases hMertens with ⟨hlog, hVlower, hVupper⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphiR : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hVpos := initialMissingEulerProduct_pos n r
  have hUpperPos : 0 <
      2 * ((n : ℝ) / Nat.totient n) / Real.log (r : ℝ) := by
    positivity
  have hLowerPos : 0 <
      ((n : ℝ) / Nat.totient n) /
        (4 * Real.log (r : ℝ)) := by
    positivity
  have hinvLower :
      (2 * ((n : ℝ) / Nat.totient n) /
          Real.log (r : ℝ))⁻¹ ≤
        (initialMissingEulerProduct n r)⁻¹ :=
    (inv_le_inv₀ hUpperPos hVpos).2 hVupper
  have hinvUpper :
      (initialMissingEulerProduct n r)⁻¹ ≤
        (((n : ℝ) / Nat.totient n) /
          (4 * Real.log (r : ℝ)))⁻¹ :=
    (inv_le_inv₀ hVpos hLowerPos).2 hVlower
  unfold initialLowerParameterMass
  rw [div_eq_mul_inv]
  constructor
  · calc
      (r : ℝ) * Nat.totient n * Real.log (r : ℝ) / 2 =
          ((r : ℝ) * n) *
            (2 * ((n : ℝ) / Nat.totient n) /
              Real.log (r : ℝ))⁻¹ := by
        field_simp [hnR.ne', hphiR.ne', hlog.ne']
      _ ≤ ((r : ℝ) * n) * (initialMissingEulerProduct n r)⁻¹ :=
        mul_le_mul_of_nonneg_left hinvLower (by positivity)
  · calc
      ((r : ℝ) * n) * (initialMissingEulerProduct n r)⁻¹ ≤
          ((r : ℝ) * n) *
            (((n : ℝ) / Nat.totient n) /
              (4 * Real.log (r : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hinvUpper (by positivity)
      _ = 4 * r * Nat.totient n * Real.log (r : ℝ) := by
        field_simp [hnR.ne', hphiR.ne', hlog.ne']

lemma initialLowerY_coarse_bounds {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r)
    (hMertens : InitialMissingMertensBounds n r) :
    (15 / 2 : ℝ) * r * Nat.totient n * Real.log (r : ℝ) ≤
        (initialLowerY n r : ℝ) ^ 2 ∧
      (initialLowerY n r : ℝ) ^ 2 <
        100 * r * Nat.totient n * Real.log (r : ℝ) := by
  have hwindow := initialLowerY_parameter_window hn hr
  have hmass := initialLowerParameterMass_bounds hn hr hMertens
  constructor <;> nlinarith

/-- All three geometric range requirements in CFP Claim B.4 follow from
three transparent real inequalities.  This leaves the asymptotic
number-theory estimates completely separate from rounding `y`. -/
lemma initialLowerY_range_of_numeric_bounds {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r)
    (hMertens : InitialMissingMertensBounds n r)
    (hrange : ((r : ℝ) ^ 2) ^ 2 ≤
      (15 / 2 : ℝ) * r * Nat.totient n * Real.log (r : ℝ))
    (hpower : Real.rpow (n : ℝ) (6 / 5 : ℝ) ≤
      (15 / 2 : ℝ) * r * Nat.totient n * Real.log (r : ℝ))
    (hhalf : 100 * r * Nat.totient n * Real.log (r : ℝ) ≤
      ((n : ℝ) / 2) ^ 2) :
    (r : ℝ) ^ 2 ≤ (initialLowerY n r : ℝ) ∧
      Real.rpow (n : ℝ) (3 / 5 : ℝ) ≤
        (initialLowerY n r : ℝ) ∧
      (initialLowerY n r : ℝ) < (n : ℝ) / 2 := by
  have hcoarse := initialLowerY_coarse_bounds hn hr hMertens
  have hy0 : 0 ≤ (initialLowerY n r : ℝ) := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowSq : (Real.rpow (n : ℝ) (3 / 5 : ℝ)) ^ 2 =
      Real.rpow (n : ℝ) (6 / 5 : ℝ) := by
    calc
      (Real.rpow (n : ℝ) (3 / 5 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow (n : ℝ) (3 / 5 : ℝ)) (2 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 2
      _ = Real.rpow (n : ℝ) ((3 / 5 : ℝ) * 2) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = Real.rpow (n : ℝ) (6 / 5 : ℝ) := by norm_num
  have hp0 : 0 ≤ Real.rpow (n : ℝ) (3 / 5 : ℝ) :=
    Real.rpow_nonneg hnR.le _
  constructor
  · nlinarith [sq_nonneg ((r : ℝ) ^ 2)]
  constructor
  · nlinarith
  · have hnHalf : 0 ≤ (n : ℝ) / 2 := by positivity
    nlinarith

lemma lowerParameterMass_pos {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    0 < lowerParameterMass n r := by
  unfold lowerParameterMass
  exact div_pos (mul_pos (by exact_mod_cast hr) (by exact_mod_cast hn))
    (missingEulerProduct_pos n r)

lemma lowerY_parameter_window {n r : ℕ}
    (hA : 1 ≤ lowerParameterMass n r) :
    15 * lowerParameterMass n r ≤ (lowerY n r : ℝ) ^ 2 ∧
      (lowerY n r : ℝ) ^ 2 < 25 * lowerParameterMass n r := by
  simpa [lowerY] using integerSqrtWindow_bounds hA

/-- A convenient sufficient condition for the mass to be at least one. -/
lemma one_le_lowerParameterMass {n r : ℕ}
    (hn : 0 < n) (hr : 3 ≤ r) :
    1 ≤ lowerParameterMass n r := by
  have hVle : missingEulerProduct n r ≤ 1 := by
    unfold missingEulerProduct
    apply Finset.prod_le_one
    · intro p hp
      exact (Erdos851.oneShift_localFactor_pos
        (mem_missingPrimesUpTo.mp hp).2.2.1).le
    · intro p hp
      have hdensity : 0 ≤ Erdos851.oneShiftDensity p := by
        unfold Erdos851.oneShiftDensity
        positivity
      linarith
  have hVpos := missingEulerProduct_pos n r
  unfold lowerParameterMass
  rw [le_div_iff₀ hVpos]
  have hrone : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

lemma lowerY_parameter_window_of_three_le {n r : ℕ}
    (hn : 0 < n) (hr : 3 ≤ r) :
    15 * lowerParameterMass n r ≤ (lowerY n r : ℝ) ^ 2 ∧
      (lowerY n r : ℝ) ^ 2 < 25 * lowerParameterMass n r :=
  lowerY_parameter_window (one_le_lowerParameterMass hn hr)

lemma lowerY_ge_colorSquare {n r : ℕ}
    (hn : 0 < n) (hr : 3 ≤ r)
    (hmass : ((r : ℝ) ^ 2) ^ 2 ≤ 15 * lowerParameterMass n r) :
    (r : ℝ) ^ 2 ≤ (lowerY n r : ℝ) := by
  simpa [lowerY] using le_integerSqrtWindow_of_sq_le
    (one_le_lowerParameterMass hn hr)
    (sq_nonneg (r : ℝ)) hmass

lemma lowerY_ge_threeFifthsPower {n r : ℕ}
    (hn : 0 < n) (hr : 3 ≤ r)
    (hmass : Real.rpow (n : ℝ) (6 / 5 : ℝ) ≤
      15 * lowerParameterMass n r) :
    Real.rpow (n : ℝ) (3 / 5 : ℝ) ≤ (lowerY n r : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply le_integerSqrtWindow_of_sq_le
    (one_le_lowerParameterMass hn hr) (Real.rpow_nonneg hnR.le _)
  change (Real.rpow (n : ℝ) (3 / 5 : ℝ)) ^ 2 ≤
    15 * lowerParameterMass n r
  rw [show (Real.rpow (n : ℝ) (3 / 5 : ℝ)) ^ 2 =
      Real.rpow (n : ℝ) (6 / 5 : ℝ) by
    calc
      (Real.rpow (n : ℝ) (3 / 5 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow (n : ℝ) (3 / 5 : ℝ)) (2 : ℝ) := by
        symm
        exact Real.rpow_natCast _ 2
      _ = Real.rpow (n : ℝ) ((3 / 5 : ℝ) * 2) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = Real.rpow (n : ℝ) (6 / 5 : ℝ) := by norm_num]
  exact hmass

lemma lowerY_lt_half {n r : ℕ}
    (hn : 0 < n) (hr : 3 ≤ r)
    (hmass : 25 * lowerParameterMass n r ≤ ((n : ℝ) / 2) ^ 2) :
    (lowerY n r : ℝ) < (n : ℝ) / 2 := by
  exact integerSqrtWindow_lt_of_sq_lt
    (one_le_lowerParameterMass hn hr) (by positivity) hmass

/-- The upper Mertens estimate gives a lower bound for the real mass under
the square root.  This is the direction used to prove `y ≥ r²` and
`y ≥ n^(3/5)` once the scale and totient-ratio estimates are inserted. -/
lemma lowerParameterMass_lower {n r : ℕ}
    (hn : 0 < n) (hr : 3 ≤ r) :
    (r : ℝ) * Nat.totient n * Real.log (r : ℝ) / 2 ≤
      lowerParameterMass n r := by
  have hVpos := missingEulerProduct_pos n r
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphiR : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hlog : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hV := missingEulerProduct_cutoff_upper hn hr
  have hupperPos : 0 <
      2 * ((n : ℝ) / Nat.totient n) / Real.log (r : ℝ) := by
    positivity
  have hinv :
      (2 * ((n : ℝ) / Nat.totient n) / Real.log (r : ℝ))⁻¹ ≤
        (missingEulerProduct n r)⁻¹ :=
    (inv_le_inv₀ hupperPos hVpos).2 hV
  unfold lowerParameterMass
  rw [div_eq_mul_inv]
  calc
    (r : ℝ) * Nat.totient n * Real.log (r : ℝ) / 2 =
        ((r : ℝ) * n) *
          (2 * ((n : ℝ) / Nat.totient n) /
            Real.log (r : ℝ))⁻¹ := by
      field_simp [hnR.ne', hphiR.ne', hlog.ne']
    _ ≤ ((r : ℝ) * n) *
          (missingEulerProduct n r)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)

/-- The lower Mertens estimate gives the complementary upper bound for the
mass.  It is the direction used to show `y < n/2`. -/
lemma lowerParameterMass_upper {n r : ℕ} (hr : 3 ≤ r) :
    lowerParameterMass n r ≤
      (3 / 2 : ℝ) * r * n * Real.log (r : ℝ) := by
  have hVpos := missingEulerProduct_pos n r
  have hinv := missingEulerProduct_cutoff_inv_upper (n := n) hr
  unfold lowerParameterMass
  rw [div_eq_mul_inv]
  calc
    (r : ℝ) * n * (missingEulerProduct n r)⁻¹ ≤
        (r : ℝ) * n *
          ((3 / 2 : ℝ) * Real.log (r : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (3 / 2 : ℝ) * r * n * Real.log (r : ℝ) := by ring

end Erdos360
