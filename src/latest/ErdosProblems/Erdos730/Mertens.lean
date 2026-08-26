/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.AnalyticInputs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-!
# Erdős 730: reciprocal-prime estimates available in pinned Mathlib

This file isolates the reciprocal-prime input used by the density proof.  It
contains no axiom and does not assume a Mertens theorem.  The main exact
identity is Abel summation:

`sum_{p ≤ x} 1 / p = π(x) / x + ∫₂ˣ π(t) / t² dt`.

Consequently an ordinary prime-number theorem is enough to recover all fixed
prime-band limits.  Pinned Mathlib currently supplies only Chebyshev's upper
bound, not the coefficient-one asymptotic; the unconditional lemmas below
bank the exact Abel bridge and the crude harmonic majorant needed by the
uniform geometric tail.
-/

open Filter Finset MeasureTheory Real
open scoped ArithmeticFunction BigOperators Nat.Prime Topology

namespace Erdos730.FullDensity

/-- The reciprocal-prime sum is nonnegative. -/
theorem reciprocalPrimeSum_nonneg (N : ℕ) :
    0 ≤ reciprocalPrimeSum N := by
  exact sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Dropping the primality restriction embeds the reciprocal-prime sum in the
ordinary harmonic sum.  The endpoint convention agrees exactly: the extra
term at `0` is zero. -/
theorem reciprocalPrimeSum_le_harmonic (N : ℕ) :
    reciprocalPrimeSum N ≤ (harmonic N : ℝ) := by
  rw [reciprocalPrimeSum]
  calc
    (∑ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℝ)⁻¹)
        ≤ ∑ p ∈ range (N + 1), (p : ℝ)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro p _ _
          positivity
    _ = (harmonic N : ℝ) := by
      induction N with
      | zero => simp
      | succ N ih =>
          rw [sum_range_succ, harmonic_succ, Rat.cast_add, Rat.cast_inv,
            Rat.cast_natCast, ih]

/-- A completely unconditional logarithmic majorant.  This is much weaker
than Mertens, but is already sufficient after multiplication by the geometric
depth factor in the uniform tail. -/
theorem reciprocalPrimeSum_le_one_add_log (N : ℕ) :
    reciprocalPrimeSum N ≤ 1 + Real.log N :=
  (reciprocalPrimeSum_le_harmonic N).trans (harmonic_le_one_add_log N)

/-- The elementary linear majorant used to discharge geometric-depth tails.
It is intentionally proved without any prime-counting estimate. -/
theorem reciprocalPrimeSum_le_natCast (N : ℕ) :
    reciprocalPrimeSum N ≤ (N : ℝ) := by
  refine (reciprocalPrimeSum_le_harmonic N).trans ?_
  induction N with
  | zero => simp
  | succ N ih =>
      rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
        Nat.cast_add, Nat.cast_one]
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hone : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      exact add_le_add ih ((inv_le_one₀ hpos).2 hone)

/-- Any fixed geometric depth factor kills the reciprocal-prime partial sum.
This unconditional lemma is the analytic content needed for the deepest-band
tail after the depth cutoff has been converted to a natural parameter. -/
theorem tendsto_geom_mul_reciprocalPrimeSum_atTop
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun N : ℕ => q ^ N * reciprocalPrimeSum N) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro N
    exact mul_nonneg (pow_nonneg hq0 N) (reciprocalPrimeSum_nonneg N)
  · intro N
    calc
      q ^ N * reciprocalPrimeSum N ≤ q ^ N * (N : ℝ) :=
        mul_le_mul_of_nonneg_left (reciprocalPrimeSum_le_natCast N) (pow_nonneg hq0 N)
      _ = (N : ℝ) * q ^ N := mul_comm _ _
  · exact tendsto_self_mul_const_pow_of_lt_one hq0 hq1

/-- Abel summation for reciprocal primes.  This is the exact bridge from the
ordinary prime-counting function to the Mertens-type band estimates needed by
the density proof. -/
theorem reciprocalPrimeSum_eq_primeCounting_div_add_integral
    {N : ℕ} (hN : 2 ≤ N) :
    reciprocalPrimeSum N =
      (Nat.primeCounting N : ℝ) / N +
        ∫ t in (2 : ℝ)..N, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) N,
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (zero_lt_two.trans_le ht.1))
  have hint : IntegrableOn (deriv fun x : ℝ => x⁻¹) (Set.Icc (2 : ℝ) N) := by
    rw [deriv_inv']
    refine ContinuousOn.integrableOn_Icc ?_
    exact ((continuous_id.pow 2).continuousOn.inv₀ fun t ht hzero =>
      (zero_lt_two.trans_le ht.1).ne' (eq_zero_of_pow_eq_zero hzero)).neg
  rw [reciprocalPrimeSum, Nat.range_succ_eq_Icc_zero, sum_filter]
  let a : ℕ → ℝ := Set.indicator {p | p.Prime} (fun _ => 1)
  trans ∑ k ∈ Icc 0 N, (k : ℝ)⁻¹ * a k
  · refine sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · simp [a, hk]
    · simp [a, hk]
  have hab :
      ∑ k ∈ Icc 0 N, (k : ℝ)⁻¹ * a k =
        (N : ℝ)⁻¹ * ∑ k ∈ Icc 0 N, a k -
          ∫ t in Set.Ioc (2 : ℝ) N,
            deriv (fun x : ℝ => x⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, a k := by
    simpa using sum_mul_eq_sub_integral_mul₁ a (f := fun x : ℝ => x⁻¹)
      (by simp [a, Nat.not_prime_zero]) (by simp [a, Nat.not_prime_one]) N hdiff hint
  rw [hab, ← intervalIntegral.integral_of_le (mod_cast hN)]
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have int_deriv (f : ℝ → ℝ) :
      ∫ u in (2 : ℝ)..N,
          deriv (fun x : ℝ => x⁻¹) u * f u =
        ∫ u in (2 : ℝ)..N, f u * -(u ^ 2)⁻¹ :=
    intervalIntegral.integral_congr fun u _ => by rw [deriv_inv']; ring
  rw [int_deriv]
  simp [a, Set.indicator_apply, Nat.range_succ_eq_Icc_zero, div_eq_mul_inv]
  ring

/-!
## The unconditional weighted Mertens estimate

The following factorial argument is adapted from
`math-inc/Erdos1196`, commit
`02fba13be7487cc51315f68d8fa7ef277633d3c8`, file
`PrimitiveSetsAboveX/PreliminariesMertens.lean` (Apache-2.0).  The source
targets Lean `v4.30.0-rc1`; the proof below has been ported and checked against
this repository's pinned Lean `v4.33.0` and Mathlib `db584cd6`.

This is the classical first Mertens theorem for the von Mangoldt weight.  It
is strictly weaker than the reciprocal-prime asymptotic, but it is the
standard unconditional input from which that asymptotic follows after (i)
bounding the contribution of proper prime powers and (ii) a second Abel
summation with weight `1 / log`.
-/

/-- Partial sums of `Λ(m) / m`. -/
noncomputable def vonMangoldtReciprocalSum (t : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 t, Λ m / (m : ℝ)

/-- The fractional-part correction in the factorial proof. -/
private noncomputable def vonMangoldtFractionalError (t : ℕ) : ℝ :=
  (1 / t) * ∑ m ∈ Icc 1 t, Λ m * ((t : ℝ) / m - ((t / m : ℕ) : ℝ))

private lemma one_div_mul_mul_natCast_div {a : ℝ} {t m : ℕ} (ht : t ≠ 0) :
    (1 / (t : ℝ)) * (a * ((t : ℝ) / m)) = a / (m : ℝ) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  grind only

private lemma truncation_eq_mod_div {t m : ℕ} :
    ((t : ℝ) / m - ↑(t / m)) = ↑(t % m) / m := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    apply (eq_div_iff hmR).2
    have hdecomp : (↑(t % m) : ℝ) + ↑(t / m) * m = t := by
      have h : (↑(t % m + m * (t / m)) : ℝ) = t := by
        exact_mod_cast (Nat.mod_add_div t m)
      simpa [Nat.cast_add, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h
    grind only

private lemma truncation_eq_fract {t m : ℕ} :
    ((t : ℝ) / m - ↑(t / m)) = Int.fract ((t : ℝ) / m) := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  exact truncation_eq_mod_div

private lemma sum_vonMangoldt_mul_div_eq_log_factorial (N : ℕ) :
    (Icc 1 N).sum (fun m => Λ m * ((N / m : ℕ) : ℝ)) =
      Real.log (Nat.factorial N) := by
  have hI : Icc 1 N = Ioc 0 N := by
    ext n
    simp [mem_Icc, mem_Ioc, Nat.succ_le_iff]
  have hlogsum :
      (Icc 1 N).sum (fun n => Real.log (n : ℝ)) =
        Real.log (∏ n ∈ Icc 1 N, (n : ℝ)) := by
    symm
    refine Real.log_prod ?_
    intro n hn
    exact Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (Nat.succ_le_iff.mp (mem_Icc.mp hn).1))
  have hprodRange :
      (∏ i ∈ range N, ((i + 1 : ℕ) : ℝ)) = Nat.factorial N := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial N
  have hprod : (∏ n ∈ Icc 1 N, (n : ℝ)) = Nat.factorial N := by
    rw [← Ico_add_one_right_eq_Icc 1 N, prod_Ico_eq_prod_range]
    simpa [Nat.succ_eq_add_one, add_comm] using hprodRange
  calc
    (Icc 1 N).sum (fun m => Λ m * ((N / m : ℕ) : ℝ)) =
        ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by rw [hI]
    _ = ∑ n ∈ Ioc 0 N,
        (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) n := by
          simpa using
            (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
              ArithmeticFunction.vonMangoldt N).symm
    _ = ∑ n ∈ Ioc 0 N, Real.log (n : ℝ) := by
          simp [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log]
    _ = ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by rw [← hI]
    _ = Real.log (Nat.factorial N) := by rw [hlogsum, hprod]

private lemma log_factorial_eq_sum_range (N : ℕ) :
    Real.log (Nat.factorial N) =
      ∑ i ∈ range N, Real.log ((i + 1 : ℕ) : ℝ) := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, Real.log_prod]
  grind only

private lemma integral_log_le_log_factorial {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x ≤ Real.log (Nat.factorial N) := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have hx1 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) hx.1
    exact Real.log_le_log hx1 hxy
  calc
    ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x
      ≤ ∑ i ∈ Ico 1 N, Real.log ((i + 1 : ℕ) : ℝ) :=
        MonotoneOn.integral_le_sum_Ico (f := Real.log) hN hmono
    _ = ∑ i ∈ range N, Real.log ((i + 1 : ℕ) : ℝ) := by
        have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
        rw [sum_Ico_eq_sum_range]
        rw [← hpred, sum_range_succ']
        simp [Nat.cast_add, add_left_comm, add_comm]
    _ = Real.log (Nat.factorial N) := (log_factorial_eq_sum_range N).symm

private lemma log_factorial_le_log_add_integral_log {N : ℕ} (hN : 1 ≤ N) :
    Real.log (Nat.factorial N) ≤
      Real.log N + ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have hx1 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)) hx.1
    exact Real.log_le_log hx1 hxy
  have hsum :
      ∑ i ∈ Ico 1 N, Real.log (i : ℝ) ≤
        ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x :=
    MonotoneOn.sum_le_integral_Ico (f := Real.log) hN hmono
  have hsum' :
      ∑ i ∈ Ico 1 N, Real.log (i : ℝ) =
        Real.log (Nat.factorial (N - 1)) := by
    rw [sum_Ico_eq_sum_range]
    simpa [Nat.cast_add, add_comm] using
      (log_factorial_eq_sum_range (N - 1)).symm
  have hfacNat : Nat.factorial N = N * Nat.factorial (N - 1) := by
    have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
    simpa [Nat.succ_eq_add_one, hpred] using Nat.factorial_succ (N - 1)
  have hfac :
      Real.log (Nat.factorial N) =
        Real.log N + Real.log (Nat.factorial (N - 1)) := by
    rw [hfacNat, Nat.cast_mul, Real.log_mul]
    · exact_mod_cast Nat.ne_of_gt hN
    · exact_mod_cast Nat.factorial_ne_zero (N - 1)
  grind only

private lemma abs_log_factorial_div_sub_log_le_one {N : ℕ} (hN : 1 ≤ N) :
    |Real.log (Nat.factorial N) / N - Real.log N| ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hint :
      ∫ x in ((1 : ℕ) : ℝ)..N, Real.log x =
        (N : ℝ) * Real.log N - N + 1 := by
    simp [integral_log]
  have hlower : Real.log N - 1 ≤ Real.log (Nat.factorial N) / N := by
    apply (le_div_iff₀ hNpos).2
    have hcomp :
        (N : ℝ) * Real.log N - N + 1 ≤ Real.log (Nat.factorial N) := by
      simpa [hint] using integral_log_le_log_factorial hN
    linarith
  have hupper : Real.log (Nat.factorial N) / N ≤ Real.log N := by
    apply (div_le_iff₀ hNpos).2
    have hcomp :
        Real.log (Nat.factorial N) ≤
          Real.log N + ((N : ℝ) * Real.log N - N + 1) := by
      simpa [hint] using log_factorial_le_log_add_integral_log hN
    have hlog : Real.log N ≤ N - 1 := by
      simpa using Real.log_le_sub_one_of_pos hNpos
    linarith
  grind only [= abs.eq_1, = max_def]

private lemma vonMangoldtReciprocalSum_eq_log_factorial_div_add_fractional
    (t : ℕ) :
    vonMangoldtReciprocalSum t =
      Real.log (Nat.factorial t) / t + vonMangoldtFractionalError t := by
  by_cases ht : t = 0
  · subst ht
    simp [vonMangoldtReciprocalSum, vonMangoldtFractionalError]
  · rw [vonMangoldtReciprocalSum, vonMangoldtFractionalError]
    calc
      ∑ m ∈ Icc 1 t, Λ m / (m : ℝ) =
          ∑ m ∈ Icc 1 t,
            ((1 / (t : ℝ)) * (Λ m * (((t / m : ℕ) : ℝ))) +
              (1 / (t : ℝ)) *
                (Λ m * ((t : ℝ) / m - ↑(t / m)))) := by
            refine sum_congr rfl ?_
            intro m _
            calc
              Λ m / (m : ℝ) =
                  (1 / (t : ℝ)) * (Λ m * ((t : ℝ) / m)) := by
                symm
                exact one_div_mul_mul_natCast_div (a := Λ m) ht
              _ = (1 / (t : ℝ)) * (Λ m * (((t / m : ℕ) : ℝ))) +
                    (1 / (t : ℝ)) *
                      (Λ m * ((t : ℝ) / m - ↑(t / m))) := by ring
      _ = (1 / (t : ℝ)) *
              ∑ m ∈ Icc 1 t, Λ m * (((t / m : ℕ) : ℝ)) +
            (1 / (t : ℝ)) *
              ∑ m ∈ Icc 1 t,
                Λ m * ((t : ℝ) / m - ↑(t / m)) := by
            rw [sum_add_distrib, mul_sum, mul_sum]
      _ = Real.log (Nat.factorial t) / t + vonMangoldtFractionalError t := by
            rw [sum_vonMangoldt_mul_div_eq_log_factorial]
            rw [vonMangoldtFractionalError]
            ring_nf

private lemma vonMangoldtFractionalError_nonneg {t : ℕ} (ht : 1 ≤ t) :
    0 ≤ vonMangoldtFractionalError t := by
  rw [vonMangoldtFractionalError]
  refine mul_nonneg ?_ (sum_nonneg ?_)
  · exact one_div_nonneg.mpr (show (0 : ℝ) ≤ t by positivity)
  · intro m _
    rw [truncation_eq_fract]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Int.fract_nonneg _)

private lemma vonMangoldtFractionalError_le {t : ℕ} (ht : 2 ≤ t) :
    vonMangoldtFractionalError t ≤ Real.log 4 + 4 := by
  rw [vonMangoldtFractionalError]
  have hsum :
      ∑ m ∈ Icc 1 t, Λ m * ((t : ℝ) / m - ↑(t / m)) ≤
        ∑ m ∈ Icc 1 t, Λ m := by
    refine sum_le_sum ?_
    intro m _
    rw [truncation_eq_fract]
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := m),
      (Int.fract_lt_one ((t : ℝ) / m)).le]
  have hcheb : Chebyshev.psi t ≤ (Real.log 4 + 4) * t := by
    simpa using Chebyshev.psi_le_const_mul_self (x := (t : ℝ))
      (show 0 ≤ (t : ℝ) by positivity)
  have hI : Icc 1 t = Ioc 0 t := by
    ext n
    simp [mem_Icc, mem_Ioc, Nat.succ_le_iff]
  calc
    (1 / t : ℝ) *
        ∑ m ∈ Icc 1 t, Λ m * ((t : ℝ) / m - ↑(t / m))
      ≤ (1 / t : ℝ) * ∑ m ∈ Icc 1 t, Λ m :=
        mul_le_mul_of_nonneg_left hsum
          (one_div_nonneg.mpr (show (0 : ℝ) ≤ t by positivity))
    _ = Chebyshev.psi t / t := by
        simp [hI, Chebyshev.psi, Nat.floor_natCast, div_eq_mul_inv, mul_comm]
    _ ≤ Real.log 4 + 4 := by
        have htR : 0 < (t : ℝ) := by positivity
        exact (div_le_iff₀ htR).mpr hcheb

/-- Unconditional bounded-error first Mertens theorem:
`∑_{m ≤ t} Λ(m) / m = log t + O(1)` with an explicit bound. -/
theorem vonMangoldtReciprocalSum_bounded_error :
    ∀ ⦃t : ℕ⦄, 2 ≤ t →
      |vonMangoldtReciprocalSum t - Real.log (t : ℝ)| ≤ Real.log 4 + 5 := by
  intro t ht
  have ht1 : 1 ≤ t := by omega
  rw [vonMangoldtReciprocalSum_eq_log_factorial_div_add_fractional t]
  calc
    |Real.log (Nat.factorial t) / t + vonMangoldtFractionalError t -
        Real.log (t : ℝ)| =
      |(Real.log (Nat.factorial t) / t - Real.log (t : ℝ)) +
        vonMangoldtFractionalError t| := by
          congr
          ring
    _ ≤ |Real.log (Nat.factorial t) / t - Real.log (t : ℝ)| +
          |vonMangoldtFractionalError t| := abs_add_le _ _
    _ = |Real.log (Nat.factorial t) / t - Real.log (t : ℝ)| +
          vonMangoldtFractionalError t := by
        rw [abs_of_nonneg (vonMangoldtFractionalError_nonneg ht1)]
    _ ≤ 1 + (Real.log 4 + 4) := by
        gcongr
        · exact abs_log_factorial_div_sub_log_le_one ht1
        · exact vonMangoldtFractionalError_le ht
    _ = Real.log 4 + 5 := by ring

/-- Proper prime powers make an absolutely summable contribution to the
von-Mangoldt reciprocal series.  This specializes Mathlib's residue-class
lemma to the unique class modulo `1`; unlike the prime-number theorem in
progressions, this summability theorem is already present in pinned Mathlib. -/
theorem summable_nonprime_vonMangoldt_div :
    Summable fun n : ℕ => (if n.Prime then 0 else Λ n) / n := by
  have h :=
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
      (a := (0 : ZMod 1))
  refine h.congr fun n => ?_
  have hn : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [ArithmeticFunction.vonMangoldt.residueClass, hn]

/-- The logarithmically weighted reciprocal-prime partial sum. -/
noncomputable def logWeightedPrimeSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / p

/-- The summable proper-prime-power contribution. -/
noncomputable def nonprimeVonMangoldtConstant : ℝ :=
  ∑' n : ℕ, (if n.Prime then 0 else Λ n) / n

theorem nonprimeVonMangoldtConstant_nonneg : 0 ≤ nonprimeVonMangoldtConstant := by
  exact tsum_nonneg fun n => by
    split_ifs
    · simp
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

/-- Exact separation of prime and proper-prime-power terms. -/
theorem vonMangoldtReciprocalSum_eq_logWeightedPrimeSum_add (N : ℕ) :
    vonMangoldtReciprocalSum N =
      logWeightedPrimeSum N +
        ∑ n ∈ Icc 1 N, (if n.Prime then 0 else Λ n) / n := by
  rw [vonMangoldtReciprocalSum, logWeightedPrimeSum, sum_filter,
    ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · simp [hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
  · simp [hn]

/-- Every finite proper-prime-power contribution is bounded by its convergent
total mass. -/
theorem sum_nonprime_vonMangoldt_div_le_constant (N : ℕ) :
    ∑ n ∈ Icc 1 N, (if n.Prime then 0 else Λ n) / n ≤
      nonprimeVonMangoldtConstant := by
  exact summable_nonprime_vonMangoldt_div.sum_le_tsum (Icc 1 N)
    (fun n _ => by
      split_ifs
      · simp
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))

/-- The floor/log discrepancy on a unit interval is at most `log 2`. -/
private lemma abs_log_floor_sub_log_le_log_two {t : ℝ} (ht : 2 ≤ t) :
    |Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t| ≤ Real.log 2 := by
  have hfloor_pos : 0 < ((⌊t⌋₊ : ℕ) : ℝ) := by
    have hfloor_one : (1 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le one_lt_two (Nat.le_floor ht)
    linarith
  have ht_pos : 0 < t := by linarith
  have hfloor_le : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht_pos.le
  have htwo : t ≤ ((⌊t⌋₊ : ℕ) : ℝ) * 2 := by
    have hlt : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    grind only
  have habs : Real.log ((⌊t⌋₊ : ℕ) : ℝ) - Real.log t ≤ 0 := by
    exact sub_nonpos.mpr (Real.log_le_log hfloor_pos hfloor_le)
  rw [abs_of_nonpos habs, neg_sub, ← Real.log_div
    (show t ≠ 0 by linarith)
    (show (((⌊t⌋₊ : ℕ) : ℝ) ≠ 0) by positivity)]
  have hratio_pos : 0 < t / (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
  refine Real.log_le_log hratio_pos ?_
  exact (div_le_iff₀' hfloor_pos).mpr htwo

/-- Continuous-endpoint bounded error for the von-Mangoldt sum. -/
theorem vonMangoldtReciprocalSum_floor_bounded_error {x : ℝ} (hx : 2 ≤ x) :
    |vonMangoldtReciprocalSum ⌊x⌋₊ - Real.log x| ≤
      Real.log 4 + 5 + Real.log 2 := by
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  calc
    |vonMangoldtReciprocalSum ⌊x⌋₊ - Real.log x|
      ≤ |vonMangoldtReciprocalSum ⌊x⌋₊ - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| +
          |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              abs_sub_le (vonMangoldtReciprocalSum ⌊x⌋₊)
                (Real.log ((⌊x⌋₊ : ℕ) : ℝ)) (Real.log x)
    _ ≤ (Real.log 4 + 5) + Real.log 2 :=
      add_le_add (vonMangoldtReciprocalSum_bounded_error hfloor)
        (abs_log_floor_sub_log_le_log_two hx)

/-- Real-endpoint error for the weighted prime sum. -/
noncomputable def logWeightedPrimeError (x : ℝ) : ℝ :=
  logWeightedPrimeSum ⌊x⌋₊ - Real.log x

/-- The prime-weighted first Mertens error is bounded unconditionally.  The
constant is deliberately not optimized; finiteness, rather than its numerical
value, is what the second Abel summation requires. -/
theorem logWeightedPrimeError_abs_le {x : ℝ} (hx : 2 ≤ x) :
    |logWeightedPrimeError x| ≤
      Real.log 4 + 5 + Real.log 2 + nonprimeVonMangoldtConstant := by
  let R : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (if n.Prime then 0 else Λ n) / n
  have hR0 : 0 ≤ R := by
    exact sum_nonneg fun n _ => by
      split_ifs
      · simp
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hRC : R ≤ nonprimeVonMangoldtConstant :=
    sum_nonprime_vonMangoldt_div_le_constant ⌊x⌋₊
  have hA := vonMangoldtReciprocalSum_floor_bounded_error hx
  have hdecomp := vonMangoldtReciprocalSum_eq_logWeightedPrimeSum_add ⌊x⌋₊
  rw [abs_le] at hA ⊢
  constructor
  · dsimp [logWeightedPrimeError]
    rw [hdecomp] at hA
    dsimp [R] at hR0 hRC ⊢
    linarith
  · dsimp [logWeightedPrimeError]
    rw [hdecomp] at hA
    dsimp [R] at hR0 hRC ⊢
    linarith

private lemma sum_Ioc_one_eq_sum_Ioc_zero_aux {f : ℕ → ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hf1 : f 1 = 0) :
    ∑ n ∈ Ioc 1 N, f n = ∑ n ∈ Ioc 0 N, f n := by
  calc
    ∑ n ∈ Ioc 1 N, f n = f 1 + ∑ n ∈ Ioc 1 N, f n := by rw [hf1, zero_add]
    _ = ∑ n ∈ Icc 1 N, f n := add_sum_Ioc_eq_sum_Icc hN
    _ = ∑ n ∈ Ioc 0 N, f n := by congr 1

private lemma sum_Ioc_one_eq_sum_Icc_zero_aux {f : ℕ → ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 N, f n = ∑ n ∈ Icc 0 N, f n := by
  calc
    ∑ n ∈ Ioc 1 N, f n = f 1 + ∑ n ∈ Ioc 1 N, f n := by rw [hf1, zero_add]
    _ = ∑ n ∈ Icc 1 N, f n := add_sum_Ioc_eq_sum_Icc hN
    _ = ∑ n ∈ Ioc 0 N, f n := by
      congr 1
    _ = ∑ n ∈ Icc 0 N, f n := by
      rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le N), hf0, zero_add]

/-- Abel summation with inverse-log weight. -/
private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊x⌋₊, f n / Real.log n =
      (∑ n ∈ Ioc 1 ⌊x⌋₊, f n) / Real.log x +
        ∫ t in 2..x,
          (∑ n ∈ Ioc 1 ⌊t⌋₊, f n) / (t * Real.log t ^ 2) := by
  let g : ℕ → ℝ := fun n => if n < 2 then 0 else f n
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
      (by simp) (by simp)]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : ¬n ≤ 1 := by simp_all
    simp [g, hn1]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := fun n => (Real.log n)⁻¹)
    (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv,
      ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
        (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn => ?_
      simp only [mem_Ioc] at hn
      have hn1 : ¬n ≤ 1 := by linarith
      simp [g, hn1]
    · rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht => ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
        (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn => ?_
      simp only [mem_Ioc] at hn
      have hn1 : ¬n ≤ 1 := by linarith
      simp [g, hn1]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : Real.log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext y; rw [deriv_inv_log]
    have : Real.log t ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    IntegrableOn (fun t => c / (t * Real.log t ^ 2)) (Set.Ioi x) volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply Integrable.const_mul
  refine integrableOn_Ioi_deriv_of_nonneg' ?_ ?_
    Real.tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have hlog : Real.log t ≠ 0 := by simp; grind
    have hdiff : DifferentiableAt ℝ (fun y => -(Real.log y)⁻¹) t := by
      fun_prop (disch := grind)
    refine hdiff.hasDerivAt.congr_deriv ?_
    simp [deriv_inv_log_apply]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private theorem integrable_logWeightedPrimeError_div_mul_log_sq
    {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn
      (fun t => logWeightedPrimeError t / (t * Real.log t ^ 2))
      (Set.Ioi x) volume := by
  let C := Real.log 4 + 5 + Real.log 2 + nonprimeVonMangoldtConstant
  have hC : 0 < C := by
    dsimp [C]
    positivity [nonprimeVonMangoldtConstant_nonneg]
  apply Integrable.mono (integrable_const_div_mul_log_sq C hx)
  · exact Measurable.aestronglyMeasurable (by
      unfold logWeightedPrimeError logWeightedPrimeSum
      fun_prop)
  · filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, Real.norm_eq_abs, norm_mul, norm_pow, sq_abs,
      abs_of_pos hC]
    gcongr
    exact logWeightedPrimeError_abs_le (by linarith)

private lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t => Real.log (Real.log t)) x = 1 / (x * Real.log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

private lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * Real.log t) =
      Real.log (Real.log x) - Real.log (Real.log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub
    (f := fun t => Real.log (Real.log t))]
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : Real.log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := fun t => 1 / (t * Real.log t))
    · refine fun t ht => ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : Real.log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

private lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => 1 / (t * Real.log t)) volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht =>
    ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : Real.log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

private theorem integral_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * Real.log t ^ 2) = c / Real.log x := by
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0)
    (f := fun y => -c / Real.log y) ?_
    (integrable_const_div_mul_log_sq c hx) ?_ using 1
  · grind
  · intro t ht
    simp at ht
    refine (HasDerivAt.fun_div (hasDerivAt_const _ (-c))
      (hasDerivAt_log (by linarith)) ?_).congr_deriv ?_
    · simp
      grind
    · grind
  · have h := Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c)
    simpa [div_eq_mul_inv] using! h

/-- Reciprocal-prime partial sums with a real cutoff. -/
noncomputable def reciprocalPrimeSumReal (x : ℝ) : ℝ :=
  ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, (p : ℝ)⁻¹

private lemma sum_Ioc_logWeighted_eq (x : ℝ) :
    ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p / p =
      logWeightedPrimeSum ⌊x⌋₊ := by
  rw [logWeightedPrimeSum]
  congr 2

private lemma sum_Icc_logWeighted_eq (x : ℝ) :
    ∑ p ∈ (Icc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p / p =
      logWeightedPrimeSum ⌊x⌋₊ := by
  rw [logWeightedPrimeSum]
  congr 1

/-- The Meissel-Mertens constant produced by the bounded first-error
integral. -/
noncomputable def reciprocalPrimeMertensConstant : ℝ :=
  (∫ t in Set.Ioi 2,
      logWeightedPrimeError t / (t * Real.log t ^ 2)) +
    1 - Real.log (Real.log 2)

/-- The continuous second Mertens error. -/
noncomputable def reciprocalPrimeMertensError (x : ℝ) : ℝ :=
  reciprocalPrimeSumReal x - Real.log (Real.log x) -
    reciprocalPrimeMertensConstant

/-- Exact tail-integral representation of the reciprocal-prime Mertens
error. -/
theorem reciprocalPrimeMertensError_eq {x : ℝ} (hx : 2 ≤ x) :
    reciprocalPrimeMertensError x =
      logWeightedPrimeError x / Real.log x -
        ∫ t in Set.Ioi x,
          logWeightedPrimeError t / (t * Real.log t ^ 2) := by
  unfold reciprocalPrimeMertensError reciprocalPrimeSumReal
  rw [sum_filter,
    ← sum_Ioc_one_eq_sum_Ioc_zero_aux (Nat.le_floor (by grind))
      (by simp [Nat.not_prime_one])]
  have hterm (n : ℕ) :
      (if n.Prime then (n : ℝ)⁻¹ else 0) =
        (if n.Prime then Real.log n / n else 0) / Real.log n := by
    split_ifs with hn
    · have hlog : Real.log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · simp
  simp_rw [hterm]
  rw [sum_div_log_eq hx,
    sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
      (by simp) (by simp), ← sum_filter, sum_Icc_logWeighted_eq]
  have hmain :
      ∫ t in 2..x,
          (∑ n ∈ Ioc 1 ⌊t⌋₊,
            if n.Prime then Real.log n / n else 0) /
              (t * Real.log t ^ 2) =
        ∫ t in 2..x,
          (1 / (t * Real.log t) +
            logWeightedPrimeError t / (t * Real.log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Icc_zero_aux (Nat.le_floor (by grind))
      (by simp) (by simp), ← sum_filter, sum_Icc_logWeighted_eq]
    unfold logWeightedPrimeError
    field
  rw [hmain, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx,
      show logWeightedPrimeSum ⌊x⌋₊ =
        Real.log x + logWeightedPrimeError x by
          unfold logWeightedPrimeError
          ring,
      add_div,
      div_self (by simp; grind)]
    unfold reciprocalPrimeMertensConstant
    calc
      _ = logWeightedPrimeError x / Real.log x +
          (∫ t in 2..x,
            logWeightedPrimeError t / (t * Real.log t ^ 2)) -
          (∫ t in Set.Ioi 2,
            logWeightedPrimeError t / (t * Real.log t ^ 2)) := by ring
      _ = _ := by
        rw [← intervalIntegral.integral_interval_add_Ioi
          (integrable_logWeightedPrimeError_div_mul_log_sq (by rfl))
          (integrable_logWeightedPrimeError_div_mul_log_sq hx)]
        ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact (integrable_logWeightedPrimeError_div_mul_log_sq
      (x := 2) (by rfl)).mono (by grind) (by rfl)

/-- A concrete (not optimized) coefficient for the reciprocal-prime Mertens
error. -/
noncomputable def reciprocalPrimeMertensErrorConstant : ℝ :=
  2 * (Real.log 4 + 5 + Real.log 2 + nonprimeVonMangoldtConstant)

theorem reciprocalPrimeMertensErrorConstant_pos :
    0 < reciprocalPrimeMertensErrorConstant := by
  unfold reciprocalPrimeMertensErrorConstant
  positivity [nonprimeVonMangoldtConstant_nonneg]

/-- Unconditional reciprocal-prime Mertens estimate with an explicit formal
coefficient.  No prime number theorem is used. -/
theorem reciprocalPrimeMertensError_abs_le {x : ℝ} (hx : 2 ≤ x) :
    |reciprocalPrimeMertensError x| ≤
      reciprocalPrimeMertensErrorConstant / Real.log x := by
  let C := Real.log 4 + 5 + Real.log 2 + nonprimeVonMangoldtConstant
  have hC : 0 < C := by
    dsimp [C]
    positivity [nonprimeVonMangoldtConstant_nonneg]
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [reciprocalPrimeMertensError_eq hx, abs_le']
  constructor
  · have hE : logWeightedPrimeError x ≤ C := by
      simpa [C] using (abs_le.mp (logWeightedPrimeError_abs_le hx)).2
    have htail :
        ∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2) ≥
          (-C) / Real.log x := calc
      _ ≥ ∫ t in Set.Ioi x, (-C) / (t * Real.log t ^ 2) := by
        apply setIntegral_mono_on
          (integrable_const_div_mul_log_sq (-C) hx)
          (integrable_logWeightedPrimeError_div_mul_log_sq hx)
          (by measurability)
        intro y hy
        simp only [Set.mem_Ioi] at hy
        have hden : 0 ≤ y * Real.log y ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        apply div_le_div_of_nonneg_right _ hden
        simpa [C] using (abs_le.mp
          (logWeightedPrimeError_abs_le (x := y) (by linarith))).1
      _ = _ := integral_const_div_mul_log_sq (-C) hx
    have hEdiv := div_le_div_of_nonneg_right hE hlog.le
    calc
      logWeightedPrimeError x / Real.log x -
          ∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2) ≤
          C / Real.log x - (-C / Real.log x) :=
        sub_le_sub hEdiv htail
      _ = reciprocalPrimeMertensErrorConstant / Real.log x := by
        simp only [reciprocalPrimeMertensErrorConstant, C]
        ring
  · have hE : -C ≤ logWeightedPrimeError x := by
      simpa [C] using (abs_le.mp (logWeightedPrimeError_abs_le hx)).1
    have htail :
        ∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2) ≤
          C / Real.log x := calc
      _ ≤ ∫ t in Set.Ioi x, C / (t * Real.log t ^ 2) := by
        apply setIntegral_mono_on
          (integrable_logWeightedPrimeError_div_mul_log_sq hx)
          (integrable_const_div_mul_log_sq C hx)
          (by measurability)
        intro y hy
        simp only [Set.mem_Ioi] at hy
        have hden : 0 ≤ y * Real.log y ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        apply div_le_div_of_nonneg_right _ hden
        simpa [C] using (abs_le.mp
          (logWeightedPrimeError_abs_le (x := y) (by linarith))).2
      _ = _ := integral_const_div_mul_log_sq C hx
    have hEdiv := div_le_div_of_nonneg_right hE hlog.le
    calc
      -(logWeightedPrimeError x / Real.log x -
          ∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2)) =
          (∫ t in Set.Ioi x,
            logWeightedPrimeError t / (t * Real.log t ^ 2)) -
              logWeightedPrimeError x / Real.log x := by ring
      _ ≤ C / Real.log x - (-C / Real.log x) :=
        sub_le_sub htail hEdiv
      _ = reciprocalPrimeMertensErrorConstant / Real.log x := by
        simp only [reciprocalPrimeMertensErrorConstant, C]
        ring

theorem reciprocalPrimeSumReal_natCast (N : ℕ) :
    reciprocalPrimeSumReal (N : ℝ) = reciprocalPrimeSum N := by
  rw [reciprocalPrimeSumReal, reciprocalPrimeSum, Nat.floor_natCast,
    Nat.range_succ_eq_Icc_zero]
  congr 1

/-- Full unconditional closure of the reciprocal-prime analytic input, with a
non-optimized coefficient. -/
theorem mertensReciprocalPrimeInput : MertensReciprocalPrimeInput := by
  refine ⟨reciprocalPrimeMertensConstant,
    reciprocalPrimeMertensErrorConstant,
    reciprocalPrimeMertensErrorConstant_pos, ?_⟩
  intro N hN
  have h := reciprocalPrimeMertensError_abs_le
    (x := (N : ℝ)) (by exact_mod_cast (show 2 ≤ N by omega))
  unfold reciprocalPrimeMertensError at h
  rw [reciprocalPrimeSumReal_natCast] at h
  exact h

end Erdos730.FullDensity
