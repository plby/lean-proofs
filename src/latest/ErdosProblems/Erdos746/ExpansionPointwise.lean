import ErdosProblems.Erdos746.ExpansionRangeSmall
import ErdosProblems.Erdos746.ExpansionRangeMedium
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Pointwise expansion estimates for Erdős 746

This file bounds the exact fixed-cardinality union-bound summand supplied by
the graph adapter.  Its lower-tail cutoff is `2*s`, corresponding to the bad
event `|N(S)| < 2|S|`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos746

noncomputable section

/-- The exact contribution from all candidate sets of cardinality `s`. -/
def expansionBinomialUnionTerm (c : ℝ) (n s : ℕ) : ℝ :=
  (n.choose s : ℝ) *
    binomialLowerTail (n - s) (2 * s) (rangeOneSuccess c n s)

theorem expansionBinomialUnionTerm_nonneg {c : ℝ} {n s : ℕ}
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    0 ≤ expansionBinomialUnionTerm c n s := by
  have hq0 := rangeOneSuccess_nonneg hp0 hp1 (s := s)
  have hq1 : rangeOneSuccess c n s ≤ 1 := by
    unfold rangeOneSuccess
    have hbase0 : 0 ≤ 1 - rangeOneProbability c n := sub_nonneg.mpr hp1
    linarith [pow_nonneg hbase0 s]
  unfold expansionBinomialUnionTerm binomialLowerTail
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun i _ ↦ binomialTerm_nonneg hq0 hq1)

/-- Increasing the strict cutoff of a finite binomial lower tail can only
increase its mass. -/
theorem binomialLowerTail_mono_cutoff (a : ℕ) {K L : ℕ} {q : ℝ}
    (hKL : K ≤ L) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    binomialLowerTail a K q ≤ binomialLowerTail a L q := by
  unfold binomialLowerTail
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKL)
    (fun i _ _ ↦ binomialTerm_nonneg hq0 hq1)

/-- The usual entropy estimate `choose n s ≤ (e*n/s)^s`, proved from
Mathlib's exact factorial bound and the lower half of Stirling's inequality. -/
theorem choose_cast_le_exp_mul_div_pow (n : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    (n.choose s : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (s : ℝ)) ^ s := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (s : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hpi := Real.pi_gt_three
    have hsR' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  have hpow0 : 0 ≤ ((s : ℝ) / Real.exp 1) ^ s := by positivity
  have hfac : ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by
    calc
      ((s : ℝ) / Real.exp 1) ^ s ≤
          Real.sqrt (2 * Real.pi * (s : ℝ)) *
            ((s : ℝ) / Real.exp 1) ^ s :=
        le_mul_of_one_le_left hpow0 hsqrt
      _ ≤ (s.factorial : ℝ) := Stirling.le_factorial_stirling s
  have hchoose : (n.choose s : ℝ) ≤ (n : ℝ) ^ s / (s.factorial : ℝ) :=
    Nat.choose_le_pow_div s n
  have hnum0 : 0 ≤ (n : ℝ) ^ s := by positivity
  calc
    (n.choose s : ℝ) ≤ (n : ℝ) ^ s / (s.factorial : ℝ) := hchoose
    _ ≤ (n : ℝ) ^ s / (((s : ℝ) / Real.exp 1) ^ s) := by
      exact div_le_div_of_nonneg_left hnum0 (by positivity) hfac
    _ = (Real.exp 1 * (n : ℝ) / (s : ℝ)) ^ s := by
      rw [← div_pow]
      congr 1
      field_simp [ne_of_gt hsR, Real.exp_ne_zero]

/-- The range-success probability lies in `[0,1]` whenever the underlying
edge probability does. -/
theorem rangeOneSuccess_mem_Icc {c : ℝ} {n s : ℕ}
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    rangeOneSuccess c n s ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨rangeOneSuccess_nonneg hp0 hp1, ?_⟩
  unfold rangeOneSuccess
  have hbase0 : 0 ≤ 1 - rangeOneProbability c n := sub_nonneg.mpr hp1
  linarith [pow_nonneg hbase0 s]

/-- Uniform upper half of equation (4): the binomial mean is at most
`c*s*log n`. -/
theorem rangeOneMean_le_mul_log {c : ℝ} {n s : ℕ}
    (hn : 1 ≤ n) (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    rangeOneMean c n s ≤ c * (s : ℝ) * Real.log (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hq := rangeOneSuccess_le hp0 hp1 (s := s)
  have hns : ((n - s : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n s
  have hq0 := rangeOneSuccess_nonneg hp0 hp1 (s := s)
  calc
    rangeOneMean c n s = ((n - s : ℕ) : ℝ) * rangeOneSuccess c n s := rfl
    _ ≤ (n : ℝ) * rangeOneSuccess c n s :=
      mul_le_mul_of_nonneg_right hns hq0
    _ ≤ (n : ℝ) * ((s : ℝ) * rangeOneProbability c n) :=
      mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hq) (Nat.cast_nonneg n)
    _ = c * (s : ℝ) * Real.log (n : ℝ) := by
      unfold rangeOneProbability
      field_simp

/-- Uniform lower half of equation (4), under explicit smallness conditions
on `s/n` and `p*s`.  The later range adapter obtains both conditions from
`s ≤ n/(log n)^2`. -/
theorem rangeOneMean_ge_small {c δ : ℝ} {n s : ℕ}
    (hcδ : 1 + δ ≤ c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 1 ≤ n) (hsn : s ≤ n)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1)
    (hsSmall : (s : ℝ) ≤ (δ / 16) * (n : ℝ))
    (hpsSmall : rangeOneProbability c n * (s : ℝ) ≤ δ / 16) :
    (1 + δ / 2) * (s : ℝ) * Real.log (n : ℝ) ≤
      rangeOneMean c n s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hcpos : 0 < c := by linarith
  let x := rangeOneProbability c n * (s : ℝ)
  let a := δ / 16
  have hx0 : 0 ≤ x := mul_nonneg hp0 (Nat.cast_nonneg s)
  have hxa : x ≤ a := hpsSmall
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hden : 0 < 1 + x := by positivity
  have hq : x / (1 + x) ≤ rangeOneSuccess c n s := by
    simpa [x, mul_comm] using mul_div_one_add_le_rangeOneSuccess hp0 hp1 (s := s)
  have hnsCast : ((n - s : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) := by
    rw [Nat.cast_sub hsn]
  have hnsLower : (n : ℝ) * (1 - a) ≤ ((n - s : ℕ) : ℝ) := by
    rw [hnsCast]
    dsimp [a]
    nlinarith [hsSmall]
  have hcoef : (1 + δ / 2) * (1 + a) ≤ c * (1 - a) := by
    have ha1 : 0 ≤ 1 - a := by dsimp [a]; nlinarith
    have hcMul := mul_le_mul_of_nonneg_right hcδ ha1
    apply le_trans _ hcMul
    dsimp [a]
    nlinarith
  let T := (1 + δ / 2) * (s : ℝ) * Real.log (n : ℝ)
  have hT0 : 0 ≤ T := by
    dsimp [T]
    positivity
  have hxidentity : (n : ℝ) * x = c * (s : ℝ) * Real.log (n : ℝ) := by
    dsimp [x]
    unfold rangeOneProbability
    field_simp
  have hnumerator : T * (1 + x) ≤ ((n - s : ℕ) : ℝ) * x := by
    calc
      T * (1 + x) ≤ T * (1 + a) := by gcongr
      _ = ((1 + δ / 2) * (1 + a)) *
          ((s : ℝ) * Real.log (n : ℝ)) := by
        dsimp [T]
        ring
      _ ≤ (c * (1 - a)) * ((s : ℝ) * Real.log (n : ℝ)) := by
        gcongr
      _ = ((n : ℝ) * (1 - a)) * x := by
        calc
          (c * (1 - a)) * ((s : ℝ) * Real.log (n : ℝ)) =
              (1 - a) * (c * (s : ℝ) * Real.log (n : ℝ)) := by ring
          _ = (1 - a) * ((n : ℝ) * x) := by rw [hxidentity]
          _ = ((n : ℝ) * (1 - a)) * x := by ring
      _ ≤ ((n - s : ℕ) : ℝ) * x := by
        exact mul_le_mul_of_nonneg_right hnsLower hx0
  have hfrac : T ≤ ((n - s : ℕ) : ℝ) * (x / (1 + x)) := by
    rw [show ((n - s : ℕ) : ℝ) * (x / (1 + x)) =
        (((n - s : ℕ) : ℝ) * x) / (1 + x) by ring,
      le_div_iff₀ hden]
    simpa [mul_assoc] using hnumerator
  calc
    (1 + δ / 2) * (s : ℝ) * Real.log (n : ℝ) = T := rfl
    _ ≤ ((n - s : ℕ) : ℝ) * (x / (1 + x)) := hfrac
    _ ≤ ((n - s : ℕ) : ℝ) * rangeOneSuccess c n s := by
      exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    _ = rangeOneMean c n s := rfl

/-- Range-II lower mean estimate under the elementary conditions
`s ≤ n/2` and `p*s ≤ 1`. -/
theorem rangeOneMean_ge_medium {c : ℝ} {n s : ℕ}
    (hn : 1 ≤ n) (hsHalf : 2 * s ≤ n)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1)
    (hps : rangeOneProbability c n * (s : ℝ) ≤ 1) :
    c / 4 * (s : ℝ) * Real.log (n : ℝ) ≤ rangeOneMean c n s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf := half_mul_le_one_sub_one_sub_pow
    (p := rangeOneProbability c n) s hp0 hp1 hps
  have hsn : s ≤ n := by omega
  have hnsCast : ((n - s : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) := by
    rw [Nat.cast_sub hsn]
  have hsHalfR : 2 * (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsHalf
  have hns : (n : ℝ) / 2 ≤ ((n - s : ℕ) : ℝ) := by
    rw [hnsCast]
    linarith
  have hpMul0 : 0 ≤ rangeOneProbability c n * (s : ℝ) / 2 := by positivity
  calc
    c / 4 * (s : ℝ) * Real.log (n : ℝ) =
        ((n : ℝ) / 2) * (rangeOneProbability c n * (s : ℝ) / 2) := by
      unfold rangeOneProbability
      field_simp
      ring
    _ ≤ ((n - s : ℕ) : ℝ) *
          (rangeOneProbability c n * (s : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hns hpMul0
    _ ≤ ((n - s : ℕ) : ℝ) * rangeOneSuccess c n s := by
      exact mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg _)
    _ = rangeOneMean c n s := rfl

/-- Chernoff's finite lower-tail inequality applied to the exact bad-event
cutoff `2*s`. -/
theorem expansionBinomialUnionTerm_le_chernoff
    {c : ℝ} {n s : ℕ}
    (hs : 1 ≤ s)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1)
    (hmean : (2 * s : ℕ) ≤
      ((n - s : ℕ) : ℝ) * rangeOneSuccess c n s) :
    expansionBinomialUnionTerm c n s ≤
      (n.choose s : ℝ) *
        (Real.exp (-rangeOneMean c n s) *
          (Real.exp 1 * rangeOneMean c n s / (2 * s : ℕ)) ^ (2 * s)) := by
  have hq := rangeOneSuccess_mem_Icc hp0 hp1 (s := s)
  have hmono : binomialLowerTail (n - s) (2 * s) (rangeOneSuccess c n s) ≤
      binomialLowerTail (n - s) (2 * s + 1) (rangeOneSuccess c n s) :=
    binomialLowerTail_mono_cutoff _ (by omega) hq.1 hq.2
  have hclassic := binomialLowerTail_chernoff_classic (n - s) (2 * s)
    hq.1 hq.2 (by omega) hmean
  unfold expansionBinomialUnionTerm
  exact mul_le_mul_of_nonneg_left (hmono.trans hclassic) (Nat.cast_nonneg _)

/-- Pointwise Range-I estimate.  The hypotheses are exactly the two uniform
mean estimates in equation (4), plus the condition needed to invoke the
finite Chernoff bound. -/
theorem expansionBinomialUnionTerm_le_small_envelope
    {c δ : ℝ} {n s : ℕ}
    (hδ : 0 < δ) (hc0 : 0 ≤ c) (hn : 1 ≤ n) (hs : 1 ≤ s)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1)
    (hmeanLower : (1 + δ / 2) * (s : ℝ) * Real.log (n : ℝ) ≤
      rangeOneMean c n s)
    (hmeanUpper : rangeOneMean c n s ≤
      c * (s : ℝ) * Real.log (n : ℝ))
    (hmeanTwo : (2 * s : ℕ) ≤ rangeOneMean c n s) :
    expansionBinomialUnionTerm c n s ≤
      (baseRatio (Real.exp 3 * c ^ 2 / 4) δ n) ^ s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hraw := expansionBinomialUnionTerm_le_chernoff hs hp0 hp1 hmeanTwo
  have hchoose : (n.choose s : ℝ) ≤ (n : ℝ) ^ s := by
    exact_mod_cast Nat.choose_le_pow n s
  have hmu0 : 0 ≤ rangeOneMean c n s := by
    unfold rangeOneMean
    exact mul_nonneg (Nat.cast_nonneg _) (rangeOneSuccess_nonneg hp0 hp1)
  have htailbase :
      Real.exp 1 * rangeOneMean c n s / (2 * s : ℕ) ≤
        Real.exp 1 * c * Real.log (n : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_left hmeanUpper (Real.exp_nonneg 1)
    rw [div_le_iff₀ (show (0 : ℝ) < (2 * s : ℕ) by positivity)]
    calc
      Real.exp 1 * rangeOneMean c n s ≤
          Real.exp 1 * (c * (s : ℝ) * Real.log (n : ℝ)) := hm
      _ = Real.exp 1 * c * Real.log (n : ℝ) / 2 * (2 * s : ℕ) := by
        push_cast
        ring
  have htailbase0 : 0 ≤ Real.exp 1 * rangeOneMean c n s / (2 * s : ℕ) := by
    positivity
  have htailbaseTarget0 : 0 ≤ Real.exp 1 * c * Real.log (n : ℝ) / 2 := by
    positivity
  have hexpmean : Real.exp (-rangeOneMean c n s) ≤
      Real.exp (-((1 + δ / 2) * (s : ℝ) * Real.log (n : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfactor :
      (n : ℝ) * Real.exp (-((1 + δ / 2) * Real.log (n : ℝ))) =
        Real.exp (-(δ / 2) * Real.log (n : ℝ)) := by
    calc
      (n : ℝ) * Real.exp (-((1 + δ / 2) * Real.log (n : ℝ))) =
          Real.exp (Real.log (n : ℝ)) *
            Real.exp (-((1 + δ / 2) * Real.log (n : ℝ))) := by
              rw [Real.exp_log hnR]
      _ = Real.exp (Real.log (n : ℝ) +
          -((1 + δ / 2) * Real.log (n : ℝ))) := by rw [Real.exp_add]
      _ = Real.exp (- (δ / 2) * Real.log (n : ℝ)) := by congr 1 <;> ring
  have hconst :
      Real.exp 1 ^ 2 * c ^ 2 / 4 ≤ Real.exp 3 * c ^ 2 / 4 := by
    have he : Real.exp 1 ^ 2 ≤ Real.exp 3 := by
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by norm_num)
    gcongr
  calc
    expansionBinomialUnionTerm c n s ≤
        (n.choose s : ℝ) *
          (Real.exp (-rangeOneMean c n s) *
            (Real.exp 1 * rangeOneMean c n s / (2 * s : ℕ)) ^ (2 * s)) := hraw
    _ ≤ (n : ℝ) ^ s *
          (Real.exp (-((1 + δ / 2) * (s : ℝ) * Real.log (n : ℝ))) *
            (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ (2 * s)) := by
      gcongr
    _ = (Real.exp (-(δ / 2) * Real.log (n : ℝ)) *
          (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2) ^ s := by
      rw [show -((1 + δ / 2) * (s : ℝ) * Real.log (n : ℝ)) =
          (s : ℝ) * (-((1 + δ / 2) * Real.log (n : ℝ))) by ring,
        Real.exp_nat_mul, pow_mul, ← mul_pow, ← mul_pow, ← mul_assoc,
        hfactor]
    _ ≤ (Real.exp (-(δ / 2) * Real.log (n : ℝ)) *
          (Real.exp 3 * c ^ 2 / 4 * Real.log (n : ℝ) ^ 2)) ^ s := by
      apply pow_le_pow_left₀ (by positivity)
      gcongr
      calc
        (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2 =
            (Real.exp 1 ^ 2 * c ^ 2 / 4) * Real.log (n : ℝ) ^ 2 := by ring
        _ ≤ (Real.exp 3 * c ^ 2 / 4) * Real.log (n : ℝ) ^ 2 := by
          gcongr
    _ = (baseRatio (Real.exp 3 * c ^ 2 / 4) δ n) ^ s := by
      congr 1
      unfold baseRatio
      rw [Real.rpow_def_of_pos hnR]
      rw [show Real.exp (-(δ / 2) * Real.log (n : ℝ)) =
          (Real.exp ((δ / 2) * Real.log (n : ℝ)))⁻¹ by
        rw [← Real.exp_neg]
        congr 1
        ring]
      field_simp

/-- Pointwise Range-II estimate.  The endpoint/absorption hypothesis is the
uniform analytic inequality already proved in `ExpansionRangeMedium`. -/
theorem expansionBinomialUnionTerm_le_medium_envelope
    {c : ℝ} {n s : ℕ}
    (hc : 0 < c) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1)
    (hmeanLower : c / 4 * (s : ℝ) * Real.log (n : ℝ) ≤
      rangeOneMean c n s)
    (hmeanUpper : rangeOneMean c n s ≤
      c * (s : ℝ) * Real.log (n : ℝ))
    (hmeanTwo : (2 * s : ℕ) ≤ rangeOneMean c n s)
    (hsLower : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (s : ℝ))
    (habsorb : 4 * Real.log (n : ℝ) ^ 2 *
        (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2 ≤
      Real.exp ((c / 8) * Real.log (n : ℝ))) :
    expansionBinomialUnionTerm c n s ≤
      Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := hlog.le
  have hraw := expansionBinomialUnionTerm_le_chernoff hs hp0 hp1 hmeanTwo
  have hchoose := choose_cast_le_exp_mul_div_pow n hs
  have hmu0 : 0 ≤ rangeOneMean c n s := by
    unfold rangeOneMean
    exact mul_nonneg (Nat.cast_nonneg _) (rangeOneSuccess_nonneg hp0 hp1)
  have htailbase :
      Real.exp 1 * rangeOneMean c n s / (2 * s : ℕ) ≤
        Real.exp 1 * c * Real.log (n : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_left hmeanUpper (Real.exp_nonneg 1)
    rw [div_le_iff₀ (show (0 : ℝ) < (2 * s : ℕ) by positivity)]
    calc
      Real.exp 1 * rangeOneMean c n s ≤
          Real.exp 1 * (c * (s : ℝ) * Real.log (n : ℝ)) := hm
      _ = Real.exp 1 * c * Real.log (n : ℝ) / 2 * (2 * s : ℕ) := by
        push_cast
        ring
  have htailbase0 : 0 ≤ Real.exp 1 * rangeOneMean c n s / (2 * s : ℕ) := by
    positivity
  have hexpmean : Real.exp (-rangeOneMean c n s) ≤
      Real.exp (-(c / 4 * (s : ℝ) * Real.log (n : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hn_div_s : (n : ℝ) / (s : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ hsR]
    simpa [mul_comm] using (div_le_iff₀ (sq_pos_of_pos hlog)).1 hsLower
  have hexp_four : Real.exp 1 ≤ 4 := by
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  have hbaseAbsorb :
      (Real.exp 1 * (n : ℝ) / (s : ℝ)) *
          (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2 ≤
        Real.exp ((c / 8) * Real.log (n : ℝ)) := by
    calc
      (Real.exp 1 * (n : ℝ) / (s : ℝ)) *
          (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2 ≤
          (4 * Real.log (n : ℝ) ^ 2) *
            (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2 := by
        gcongr
        calc
          Real.exp 1 * (n : ℝ) / (s : ℝ) =
              Real.exp 1 * ((n : ℝ) / (s : ℝ)) := by ring
          _ ≤ 4 * Real.log (n : ℝ) ^ 2 := by gcongr
      _ ≤ Real.exp ((c / 8) * Real.log (n : ℝ)) := by simpa [mul_assoc] using habsorb
  calc
    expansionBinomialUnionTerm c n s ≤
        (n.choose s : ℝ) *
          (Real.exp (-rangeOneMean c n s) *
            (Real.exp 1 * rangeOneMean c n s / (2 * s : ℕ)) ^ (2 * s)) := hraw
    _ ≤ (Real.exp 1 * (n : ℝ) / (s : ℝ)) ^ s *
          (Real.exp (-(c / 4 * (s : ℝ) * Real.log (n : ℝ))) *
            (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ (2 * s)) := by
      gcongr
    _ = (Real.exp (-(c / 4) * Real.log (n : ℝ)) *
          ((Real.exp 1 * (n : ℝ) / (s : ℝ)) *
            (Real.exp 1 * c * Real.log (n : ℝ) / 2) ^ 2)) ^ s := by
      rw [show -(c / 4 * (s : ℝ) * Real.log (n : ℝ)) =
          (s : ℝ) * (-(c / 4) * Real.log (n : ℝ)) by ring,
        Real.exp_nat_mul, pow_mul, ← mul_pow, ← mul_pow]
      congr 1
      ring
    _ ≤ (Real.exp (-(c / 4) * Real.log (n : ℝ)) *
          Real.exp ((c / 8) * Real.log (n : ℝ))) ^ s := by
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left hbaseAbsorb (Real.exp_nonneg _)) s
    _ = Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring

/-! ## The large-set pointwise estimate -/

/-- The binomial lower tail can also be bounded by choosing fewer than
`2s` occupied outside-vertex bundles and forcing every remaining bundle to
be empty.  This is the finite binomial version of equation (7). -/
theorem binomialLowerTail_rangeOneSuccess_le_large
    {c : ℝ} {n s : ℕ}
    (hs : 1 ≤ s) (hthree : 3 * s ≤ n)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    binomialLowerTail (n - s) (2 * s) (rangeOneSuccess c n s) ≤
      (2 : ℝ) ^ n * Real.exp
        (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ)) := by
  let a := n - s
  let r := 2 * s - 1
  have hcut : r + 1 = 2 * s := by dsimp [r]; omega
  have hq := rangeOneSuccess_mem_Icc hp0 hp1 (s := s)
  have htail := binomialLowerTail_le_choose_sum_mul a r hq.1 hq.2
  rw [hcut] at htail
  have hra : r + 1 ≤ a + 1 := by
    dsimp [a, r]
    omega
  have hchooseSum :
      (∑ i ∈ Finset.range (r + 1), (a.choose i : ℝ)) ≤ (2 : ℝ) ^ a := by
    calc
      (∑ i ∈ Finset.range (r + 1), (a.choose i : ℝ)) ≤
          ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hra)
          (fun _ _ _ ↦ Nat.cast_nonneg _)
      _ = (2 : ℝ) ^ a := by exact_mod_cast Nat.sum_range_choose a
  have hfail0 : 0 ≤ 1 - rangeOneProbability c n := sub_nonneg.mpr hp1
  have hfail1 : 1 - rangeOneProbability c n ≤ 1 := by linarith
  have hexpNat : s * (n - 3 * s) ≤ s * (a - r) := by
    apply Nat.mul_le_mul_left
    dsimp [a, r]
    omega
  have hpow :
      (1 - rangeOneSuccess c n s) ^ (a - r) ≤
        Real.exp (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ)) := by
    calc
      (1 - rangeOneSuccess c n s) ^ (a - r) =
          (1 - rangeOneProbability c n) ^ (s * (a - r)) := by
        unfold rangeOneSuccess
        rw [show 1 - (1 - (1 - rangeOneProbability c n) ^ s) =
          (1 - rangeOneProbability c n) ^ s by ring]
        rw [pow_mul]
      _ ≤ (1 - rangeOneProbability c n) ^ (s * (n - 3 * s)) :=
        pow_le_pow_of_le_one hfail0 hfail1 hexpNat
      _ ≤ Real.exp
          (-rangeOneProbability c n * (s * (n - 3 * s) : ℕ)) := by
        have hbase := Real.one_sub_le_exp_neg (rangeOneProbability c n)
        calc
          (1 - rangeOneProbability c n) ^ (s * (n - 3 * s)) ≤
              Real.exp (-rangeOneProbability c n) ^ (s * (n - 3 * s)) :=
            pow_le_pow_left₀ hfail0 hbase _
          _ = Real.exp
              (-rangeOneProbability c n * (s * (n - 3 * s) : ℕ)) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
      _ = Real.exp
          (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ)) := by
        congr 1
        push_cast
        ring
  have hpow0 : 0 ≤ (1 - rangeOneSuccess c n s) ^ (a - r) := by
    have : 0 ≤ 1 - rangeOneSuccess c n s := sub_nonneg.mpr hq.2
    positivity
  calc
    binomialLowerTail (n - s) (2 * s) (rangeOneSuccess c n s) ≤
        (∑ i ∈ Finset.range (r + 1), (a.choose i : ℝ)) *
          (1 - rangeOneSuccess c n s) ^ (a - r) := by
            simpa [a, hcut] using htail
    _ ≤ (2 : ℝ) ^ a * (1 - rangeOneSuccess c n s) ^ (a - r) :=
      mul_le_mul_of_nonneg_right hchooseSum hpow0
    _ ≤ (2 : ℝ) ^ n * Real.exp
        (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ)) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n s)
      · exact hpow
      · positivity
      · positivity

/-- Equation (7), after choosing the candidate set `S`.  The binomial tail
keeps the first factor `choose n s` explicit so that the first subrange can
use its sharper entropy estimate. -/
theorem expansionBinomialUnionTerm_le_large_raw
    {c : ℝ} {n s : ℕ}
    (hs : 1 ≤ s) (hthree : 3 * s ≤ n)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    expansionBinomialUnionTerm c n s ≤
      (n.choose s : ℝ) * ((2 : ℝ) ^ n * Real.exp
        (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ))) := by
  unfold expansionBinomialUnionTerm
  exact mul_le_mul_of_nonneg_left
    (binomialLowerTail_rangeOneSuccess_le_large hs hthree hp0 hp1)
    (Nat.cast_nonneg _)

/-- First half of Range III: if `n/(c log n) ≤ s ≤ n/12` and the
eventual logarithmic absorption inequality holds, the complete `s`-layer is
at most `exp(-((7/10)-log 2)n)`. -/
theorem expansionBinomialUnionTerm_le_large_linear
    {c : ℝ} {n s : ℕ}
    (hc : 0 < c) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (hthree : 3 * s ≤ n) (htwelve : 12 * s ≤ n)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1)
    (hsLower : (n : ℝ) / (c * Real.log (n : ℝ)) ≤ (s : ℝ))
    (hlogAbsorb : Real.log (Real.exp 1 * c * Real.log (n : ℝ)) ≤
      c * Real.log (n : ℝ) / 20) :
    expansionBinomialUnionTerm c n s ≤
      Real.exp (-(((7 / 10 : ℝ) - Real.log 2) * (n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hclog : 0 < c * Real.log (n : ℝ) := mul_pos hc hlog
  have hraw := expansionBinomialUnionTerm_le_large_raw hs hthree hp0 hp1
  have hchoose := choose_cast_le_exp_mul_div_pow n hs
  have hn_div_s : (n : ℝ) / (s : ℝ) ≤ c * Real.log (n : ℝ) := by
    rw [div_le_iff₀ hsR]
    have := (div_le_iff₀ hclog).1 hsLower
    nlinarith
  have hbase : Real.exp 1 * (n : ℝ) / (s : ℝ) ≤
      Real.exp 1 * c * Real.log (n : ℝ) := by
    calc
      Real.exp 1 * (n : ℝ) / (s : ℝ) =
          Real.exp 1 * ((n : ℝ) / (s : ℝ)) := by ring
      _ ≤ Real.exp 1 * (c * Real.log (n : ℝ)) := by gcongr
      _ = Real.exp 1 * c * Real.log (n : ℝ) := by ring
  have hBpos : 0 < Real.exp 1 * c * Real.log (n : ℝ) := by positivity
  have hchooseExp : (n.choose s : ℝ) ≤
      Real.exp ((s : ℝ) * Real.log (Real.exp 1 * c * Real.log (n : ℝ))) := by
    calc
      (n.choose s : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (s : ℝ)) ^ s := hchoose
      _ ≤ (Real.exp 1 * c * Real.log (n : ℝ)) ^ s :=
        pow_le_pow_left₀ (by positivity) hbase s
      _ = Real.exp ((s : ℝ) * Real.log
          (Real.exp 1 * c * Real.log (n : ℝ))) := by
        calc
          (Real.exp 1 * c * Real.log (n : ℝ)) ^ s =
              Real.exp (Real.log (Real.exp 1 * c * Real.log (n : ℝ))) ^ s := by
                rw [Real.exp_log hBpos]
          _ = Real.exp ((s : ℝ) * Real.log
              (Real.exp 1 * c * Real.log (n : ℝ))) := by
                rw [← Real.exp_nat_mul]
  have htwelveR : 12 * (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast htwelve
  have hquarter : (3 : ℝ) / 4 * (n : ℝ) ≤ (n - 3 * s : ℕ) := by
    have hsn : 3 * s ≤ n := hthree
    rw [Nat.cast_sub hsn]
    push_cast
    linarith
  have hpsn : (n : ℝ) ≤ c * Real.log (n : ℝ) * (s : ℝ) := by
    have := (div_le_iff₀ hclog).1 hsLower
    nlinarith
  have hloss : (7 / 10 : ℝ) * (n : ℝ) ≤
      rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ) -
        (s : ℝ) * Real.log (Real.exp 1 * c * Real.log (n : ℝ)) := by
    have habs : (s : ℝ) * Real.log (Real.exp 1 * c * Real.log (n : ℝ)) ≤
        (1 / 20 : ℝ) * (c * Real.log (n : ℝ) * (s : ℝ)) := by
      calc
        (s : ℝ) * Real.log (Real.exp 1 * c * Real.log (n : ℝ)) ≤
            (s : ℝ) * (c * Real.log (n : ℝ) / 20) := by gcongr
        _ = (1 / 20 : ℝ) * (c * Real.log (n : ℝ) * (s : ℝ)) := by ring
    have hlossMain : (3 / 4 : ℝ) * (c * Real.log (n : ℝ) * (s : ℝ)) ≤
        rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ) := by
      have hpS0 : 0 ≤ rangeOneProbability c n * (s : ℝ) :=
        mul_nonneg hp0 (Nat.cast_nonneg s)
      have hm := mul_le_mul_of_nonneg_left hquarter hpS0
      calc
        (3 / 4 : ℝ) * (c * Real.log (n : ℝ) * (s : ℝ)) =
            (rangeOneProbability c n * (s : ℝ)) * ((3 / 4 : ℝ) * n) := by
          unfold rangeOneProbability
          field_simp
        _ ≤ (rangeOneProbability c n * (s : ℝ)) * (n - 3 * s : ℕ) := hm
        _ = rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ) := by ring
    nlinarith
  have hpowTwo : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ n = Real.exp (Real.log 2) ^ n := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((n : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
  calc
    expansionBinomialUnionTerm c n s ≤
        (n.choose s : ℝ) * ((2 : ℝ) ^ n * Real.exp
          (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ))) := hraw
    _ ≤ Real.exp ((s : ℝ) * Real.log
          (Real.exp 1 * c * Real.log (n : ℝ))) *
        (Real.exp ((n : ℝ) * Real.log 2) * Real.exp
          (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ))) := by
      rw [hpowTwo]
      gcongr
    _ = Real.exp ((s : ℝ) * Real.log
          (Real.exp 1 * c * Real.log (n : ℝ)) +
        (n : ℝ) * Real.log 2 -
          rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(((7 / 10 : ℝ) - Real.log 2) * (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Second half of Range III: on `n/12 ≤ s ≤ n/4`, concavity gives
`s(n-3s) ≥ n²/16`, yielding equation (9)'s pointwise envelope. -/
theorem expansionBinomialUnionTerm_le_large_log
    {c : ℝ} {n s : ℕ}
    (hc : 0 < c) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (hthree : 3 * s ≤ n)
    (htwelve : (n : ℝ) / 12 ≤ (s : ℝ))
    (hquarter : (s : ℝ) ≤ (n : ℝ) / 4)
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    expansionBinomialUnionTerm c n s ≤ Real.exp
      (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hraw := expansionBinomialUnionTerm_le_large_raw hs hthree hp0 hp1
  have hchoose : (n.choose s : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n s
  have hconcave : (n : ℝ) ^ 2 / 16 ≤
      (s : ℝ) * ((n : ℝ) - 3 * (s : ℝ)) := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (s : ℝ) - (n : ℝ) / 12 by linarith)
      (show (s : ℝ) - (n : ℝ) / 4 ≤ 0 by linarith)]
  have hsubCast : ((n - 3 * s : ℕ) : ℝ) = (n : ℝ) - 3 * (s : ℝ) := by
    rw [Nat.cast_sub hthree]
    norm_num
  have hloss : c * (n : ℝ) * Real.log (n : ℝ) / 16 ≤
      rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ) := by
    have hp0' : 0 ≤ rangeOneProbability c n := hp0
    have hm := mul_le_mul_of_nonneg_left hconcave hp0'
    calc
      c * (n : ℝ) * Real.log (n : ℝ) / 16 =
          rangeOneProbability c n * ((n : ℝ) ^ 2 / 16) := by
        unfold rangeOneProbability
        field_simp
      _ ≤ rangeOneProbability c n *
          ((s : ℝ) * ((n : ℝ) - 3 * (s : ℝ))) := hm
      _ = rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ) := by
        rw [hsubCast]
        ring
  have hpowTwo : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ n = Real.exp (Real.log 2) ^ n := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((n : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
  calc
    expansionBinomialUnionTerm c n s ≤
        (n.choose s : ℝ) * ((2 : ℝ) ^ n * Real.exp
          (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ))) := hraw
    _ ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n * Real.exp
          (-rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ))) := by
      gcongr
    _ = Real.exp (2 * (n : ℝ) * Real.log 2 -
          rangeOneProbability c n * (s : ℝ) * (n - 3 * s : ℕ)) := by
      rw [hpowTwo, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp
        (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16) := by
      exact Real.exp_le_exp.mpr (by linarith)

end

end Erdos746
