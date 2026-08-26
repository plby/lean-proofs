import ErdosProblems.Erdos1002.DiscreteAbel
import ErdosProblems.Erdos1002.RamanujanIdentities
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Incomplete orthogonality for Ramanujan sums

This file proves the uniform interval bound used in the reconstruction
argument, including intervals with negative integer endpoints.  The proof
uses the divisor--Möbius formula and retains the two endpoint discrepancies
in the count of multiples.
-/

open Finset
open scoped ArithmeticFunction.sigma BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

/-- Number of multiples of `m` in the half-open integer interval `[A,B)`. -/
def integerMultipleCount (A B : ℤ) (m : ℕ) : ℕ :=
  #{n ∈ Ico A B | (m : ℤ) ∣ n}

private theorem rat_abs_ceil_sub_le_one (x : ℚ) :
    |((⌈x⌉ : ℤ) : ℚ) - x| ≤ 1 := by
  rw [abs_le]
  constructor
  · have hx := Int.le_ceil x
    linarith
  · have hx := Int.ceil_lt_add_one x
    linarith

/-- A multiple count differs from interval length divided by the modulus by
at most the two endpoint errors.  The sharper constant one is true, but two
is the form used by the manuscript and avoids any endpoint convention being
hidden. -/
theorem integerMultipleCount_discrepancy (A B : ℤ) (hAB : A ≤ B)
    {m : ℕ} (hm : m ≠ 0) :
    |((integerMultipleCount A B m : ℕ) : ℚ) -
        ((B - A : ℤ) : ℚ) / (m : ℚ)| ≤ 2 := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hdiv : (A : ℚ) / (m : ℚ) ≤ (B : ℚ) / (m : ℚ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hAB) hmQ.le
  have hceil : ⌈(A : ℚ) / (m : ℚ)⌉ ≤ ⌈(B : ℚ) / (m : ℚ)⌉ :=
    Int.ceil_mono hdiv
  have hcardInt :
      (integerMultipleCount A B m : ℤ) =
        ⌈(B : ℚ) / (m : ℚ)⌉ - ⌈(A : ℚ) / (m : ℚ)⌉ := by
    rw [integerMultipleCount, Int.Ico_filter_dvd_card A B hmZ]
    exact max_eq_left (sub_nonneg.mpr hceil)
  have hcardRat :
      ((integerMultipleCount A B m : ℕ) : ℚ) =
        (⌈(B : ℚ) / (m : ℚ)⌉ : ℤ) -
          (⌈(A : ℚ) / (m : ℚ)⌉ : ℤ) := by
    exact_mod_cast hcardInt
  rw [hcardRat]
  let x : ℚ := (A : ℚ) / (m : ℚ)
  let y : ℚ := (B : ℚ) / (m : ℚ)
  have hA := rat_abs_ceil_sub_le_one x
  have hB := rat_abs_ceil_sub_le_one y
  calc
    |((⌈(B : ℚ) / (m : ℚ)⌉ : ℤ) : ℚ) -
        ((⌈(A : ℚ) / (m : ℚ)⌉ : ℤ) : ℚ) -
        ((B - A : ℤ) : ℚ) / (m : ℚ)| =
      |(((⌈y⌉ : ℤ) : ℚ) - y) - (((⌈x⌉ : ℤ) : ℚ) - x)| := by
          congr 1
          dsimp [x, y]
          push_cast
          ring
    _ ≤ |((⌈y⌉ : ℤ) : ℚ) - y| + |((⌈x⌉ : ℤ) : ℚ) - x| := by
      simpa only [sub_zero, zero_sub, abs_neg] using!
        (abs_sub_le ((((⌈y⌉ : ℤ) : ℚ) - y)) 0 ((((⌈x⌉ : ℤ) : ℚ) - x)))
    _ ≤ 2 := by linarith

/-- Divisor formula rewritten as a sum over all divisors of the modulus with
an explicit integer divisibility indicator. -/
theorem ramanujanSum_eq_divisor_indicator {q : ℕ} (n : ℤ) (hq : q ≠ 0) :
    ramanujanSum q n =
      ∑ d ∈ q.divisors,
        if (d : ℤ) ∣ n then
          (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℂ)
        else 0 := by
  rw [ramanujanSum_divisor_moebius n hq]
  have hgcd : Nat.gcd q n.natAbs ≠ 0 :=
    (Nat.gcd_pos_of_pos_left n.natAbs (Nat.pos_of_ne_zero hq)).ne'
  have hfin :
      (Nat.gcd q n.natAbs).divisors =
        Finset.filter (fun d : ℕ ↦ (d : ℤ) ∣ n) q.divisors := by
    ext d
    simp [Nat.mem_divisors, hq, hgcd, Nat.dvd_gcd_iff, Int.natCast_dvd, and_comm]
  rw [hfin, Finset.sum_filter]

/-- Coefficient attached to a pair of divisors in the product of two
divisor--Möbius formulas. -/
def ramanujanPairWeight (p p' d e : ℕ) : ℂ :=
  ((d : ℂ) * (ArithmeticFunction.moebius (p / d) : ℂ)) *
    ((e : ℂ) * (ArithmeticFunction.moebius (p' / e) : ℂ))

private theorem divisor_indicator_product {p p' d e : ℕ} (n : ℤ) :
    (if (d : ℤ) ∣ n then
        (d : ℂ) * (ArithmeticFunction.moebius (p / d) : ℂ) else 0) *
      (if (e : ℤ) ∣ n then
        (e : ℂ) * (ArithmeticFunction.moebius (p' / e) : ℂ) else 0) =
      if (Nat.lcm d e : ℤ) ∣ n then ramanujanPairWeight p p' d e else 0 := by
  have hiff : (Nat.lcm d e : ℤ) ∣ n ↔ (d : ℤ) ∣ n ∧ (e : ℤ) ∣ n := by
    simp only [Int.natCast_dvd, Nat.lcm_dvd_iff]
  by_cases hd : (d : ℤ) ∣ n
  · by_cases he : (e : ℤ) ∣ n
    · rw [if_pos hd, if_pos he, if_pos (hiff.2 ⟨hd, he⟩)]
      rfl
    · have hl : ¬(Nat.lcm d e : ℤ) ∣ n := fun h ↦ he (hiff.1 h).2
      rw [if_pos hd, if_neg he, if_neg hl, mul_zero]
  · have hl : ¬(Nat.lcm d e : ℤ) ∣ n := fun h ↦ hd (hiff.1 h).1
    rw [if_neg hd, if_neg hl, zero_mul]

private theorem sum_indicator_eq_weight_mul_count
    (A B : ℤ) (p p' d e : ℕ) :
    (∑ n ∈ Ico A B,
      if (Nat.lcm d e : ℤ) ∣ n then ramanujanPairWeight p p' d e else 0) =
      ramanujanPairWeight p p' d e * (integerMultipleCount A B (Nat.lcm d e) : ℂ) := by
  rw [← Finset.sum_filter]
  simp [integerMultipleCount, nsmul_eq_mul, mul_comm]

/-- Exact expansion of an incomplete product sum into counts of common
multiples. -/
theorem sum_ramanujan_product_eq_multipleCounts
    (A B : ℤ) {p p' : ℕ} (hp : p ≠ 0) (hp' : p' ≠ 0) :
    (∑ n ∈ Ico A B, ramanujanSum p n * ramanujanSum p' n) =
      ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          (integerMultipleCount A B (Nat.lcm d e) : ℂ) := by
  calc
    (∑ n ∈ Ico A B, ramanujanSum p n * ramanujanSum p' n) =
      ∑ n ∈ Ico A B, ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        (if (d : ℤ) ∣ n then
            (d : ℂ) * (ArithmeticFunction.moebius (p / d) : ℂ) else 0) *
          (if (e : ℤ) ∣ n then
            (e : ℂ) * (ArithmeticFunction.moebius (p' / e) : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [ramanujanSum_eq_divisor_indicator n hp,
        ramanujanSum_eq_divisor_indicator n hp', Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
    _ = ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors, ∑ n ∈ Ico A B,
        (if (d : ℤ) ∣ n then
            (d : ℂ) * (ArithmeticFunction.moebius (p / d) : ℂ) else 0) *
          (if (e : ℤ) ∣ n then
            (e : ℂ) * (ArithmeticFunction.moebius (p' / e) : ℂ) else 0) := by
      rw [Finset.sum_comm (s := Ico A B) (t := p.divisors)]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm (s := Ico A B) (t := p'.divisors)]
    _ = ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors, ∑ n ∈ Ico A B,
        if (Nat.lcm d e : ℤ) ∣ n then ramanujanPairWeight p p' d e else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro n _
      exact divisor_indicator_product n
    _ = ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          (integerMultipleCount A B (Nat.lcm d e) : ℂ) := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      exact sum_indicator_eq_weight_mul_count A B p p' d e

private theorem sum_Ico_zero_int_eq_sum_range (L : ℕ) (f : ℤ → ℂ) :
    (∑ z ∈ Ico (0 : ℤ) (L : ℤ), f z) = ∑ n ∈ Finset.range L, f (n : ℤ) := by
  refine Finset.sum_bij (fun z _ ↦ z.toNat) ?_ ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_range]
    have hz' := Finset.mem_Ico.mp hz
    have hzNonneg : 0 ≤ z := hz'.1
    have hzLt : z < (L : ℤ) := hz'.2
    change z.toNat < L
    rw [← Int.toNat_of_nonneg hzNonneg] at hzLt
    exact_mod_cast hzLt
  · intro z₁ hz₁ z₂ hz₂ heq
    have hz₁nonneg : 0 ≤ z₁ := (Finset.mem_Ico.mp hz₁).1
    have hz₂nonneg : 0 ≤ z₂ := (Finset.mem_Ico.mp hz₂).1
    rw [← Int.toNat_of_nonneg hz₁nonneg, ← Int.toNat_of_nonneg hz₂nonneg]
    exact congrArg (fun n : ℕ ↦ (n : ℤ)) heq
  · intro n hn
    refine ⟨(n : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Ico]
      exact ⟨by positivity, by exact_mod_cast Finset.mem_range.mp hn⟩
    · simp
  · intro z hz
    rw [Int.toNat_of_nonneg (Finset.mem_Ico.mp hz).1]

private theorem integerMultipleCount_zero_period {L m : ℕ}
    (hm : m ≠ 0) (hmL : m ∣ L) :
    integerMultipleCount 0 (L : ℤ) m = L / m := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hratio : (L : ℚ) / (m : ℚ) = ((L / m : ℕ) : ℚ) := by
    rw [div_eq_iff (by exact_mod_cast hm)]
    exact_mod_cast (Nat.div_mul_cancel hmL).symm
  have hcardZ : (integerMultipleCount 0 (L : ℤ) m : ℤ) = (L / m : ℕ) := by
    have hcard := Int.Ico_filter_dvd_card (0 : ℤ) (L : ℤ) hmZ
    have hratio' : ((L : ℤ) : ℚ) / ((m : ℤ) : ℚ) =
        (((L / m : ℕ) : ℤ) : ℚ) := by simpa using! hratio
    simp only [Int.cast_zero, zero_div, Int.ceil_zero, sub_zero, hratio',
      Int.ceil_intCast] at hcard
    rw [max_eq_left (by positivity : (0 : ℤ) ≤ (L / m : ℕ))] at hcard
    simpa [integerMultipleCount] using! hcard
  exact_mod_cast hcardZ

private theorem divisorPair_lcm_dvd {p p' d e : ℕ}
    (hd : d ∈ p.divisors) (he : e ∈ p'.divisors) :
    Nat.lcm d e ∣ Nat.lcm p p' := by
  exact Nat.lcm_dvd
    ((Nat.dvd_of_mem_divisors hd).trans (Nat.dvd_lcm_left p p'))
    ((Nat.dvd_of_mem_divisors he).trans (Nat.dvd_lcm_right p p'))

private theorem divisorPair_lcm_ne_zero {p p' d e : ℕ}
    (hd : d ∈ p.divisors) (he : e ∈ p'.divisors) :
    Nat.lcm d e ≠ 0 := by
  exact Nat.lcm_ne_zero (Nat.pos_of_mem_divisors hd).ne'
    (Nat.pos_of_mem_divisors he).ne'

/-- The divisor-pair expansion has zero average off the diagonal.  This is
the exact algebraic cancellation which removes the interval-length term
from every incomplete sum. -/
theorem ramanujanPairWeight_mean_zero {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
      ramanujanPairWeight p p' d e /
        (Nat.lcm d e : ℂ)) = 0 := by
  let L := Nat.lcm p p'
  have hL : L ≠ 0 := Nat.lcm_ne_zero hp hp'
  have hperiod :
      (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          ((L / Nat.lcm d e : ℕ) : ℂ)) = 0 := by
    calc
      (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          ((L / Nat.lcm d e : ℕ) : ℂ)) =
        ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
          ramanujanPairWeight p p' d e *
            (integerMultipleCount 0 (L : ℤ) (Nat.lcm d e) : ℂ) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          rw [integerMultipleCount_zero_period
            (divisorPair_lcm_ne_zero hd he) (divisorPair_lcm_dvd hd he)]
      _ = ∑ z ∈ Ico (0 : ℤ) (L : ℤ),
          ramanujanSum p z * ramanujanSum p' z := by
          symm
          exact sum_ramanujan_product_eq_multipleCounts 0 (L : ℤ) hp hp'
      _ = ∑ n ∈ Finset.range L,
          ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ) :=
            sum_Ico_zero_int_eq_sum_range L _
      _ = 0 := ramanujan_complete_period_orthogonality hp hp' hpp'
  have hscaled :
      (L : ℂ) *
          (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
            ramanujanPairWeight p p' d e /
              (Nat.lcm d e : ℂ)) = 0 := by
    calc
      (L : ℂ) *
          (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
            ramanujanPairWeight p p' d e /
              (Nat.lcm d e : ℂ)) =
        ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
          ramanujanPairWeight p p' d e *
            ((L / Nat.lcm d e : ℕ) : ℂ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          have hm : Nat.lcm d e ≠ 0 := divisorPair_lcm_ne_zero hd he
          have hmL : Nat.lcm d e ∣ L := divisorPair_lcm_dvd hd he
          have hmC : (Nat.lcm d e : ℂ) ≠ 0 := by exact_mod_cast hm
          rw [Nat.cast_div hmL hmC]
          field_simp [hmC]
      _ = 0 := hperiod
  exact (mul_eq_zero.mp hscaled).resolve_left (by exact_mod_cast hL)

/-- The complex-valued endpoint error in a count of multiples. -/
def integerMultipleError (A B : ℤ) (m : ℕ) : ℂ :=
  (integerMultipleCount A B m : ℂ) -
    ((B - A : ℤ) : ℂ) / (m : ℂ)

private theorem norm_integerMultipleError_le_two
    (A B : ℤ) (hAB : A ≤ B) {m : ℕ} (hm : m ≠ 0) :
    ‖integerMultipleError A B m‖ ≤ 2 := by
  have hrat := integerMultipleCount_discrepancy A B hAB hm
  have hcast : integerMultipleError A B m =
      (((integerMultipleCount A B m : ℕ) : ℚ) -
        ((B - A : ℤ) : ℚ) / (m : ℚ) : ℚ) := by
    unfold integerMultipleError
    push_cast
    rfl
  rw [hcast, Complex.norm_ratCast]
  exact_mod_cast hrat

private theorem norm_ramanujanPairWeight_le (p p' d e : ℕ) :
    ‖ramanujanPairWeight p p' d e‖ ≤ (d : ℝ) * (e : ℝ) := by
  rcases ArithmeticFunction.moebius_eq_or (p / d) with hd | hd | hd <;>
    rcases ArithmeticFunction.moebius_eq_or (p' / e) with he | he | he <;>
    simp [ramanujanPairWeight, hd, he] <;> positivity

private theorem sum_norm_ramanujanPairWeight_le (p p' : ℕ) :
    (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
      ‖ramanujanPairWeight p p' d e‖) ≤
      (ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ) := by
  calc
    (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
      ‖ramanujanPairWeight p p' d e‖) ≤
      ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors, (d : ℝ) * (e : ℝ) := by
        gcongr with d hd e he
        exact norm_ramanujanPairWeight_le p p' d e
    _ = (ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ) := by
      rw [ArithmeticFunction.sigma_one_apply,
        ArithmeticFunction.sigma_one_apply]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]

/-- Exact form of incomplete orthogonality: after the complete-period mean
has cancelled, only the two endpoint errors in each divisor-pair count
remain. -/
theorem sum_ramanujan_product_eq_endpointErrors
    (A B : ℤ) {p p' : ℕ} (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    (∑ n ∈ Ico A B, ramanujanSum p n * ramanujanSum p' n) =
      ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          integerMultipleError A B (Nat.lcm d e) := by
  let ℓ : ℂ := ((B - A : ℤ) : ℂ)
  have hmean := ramanujanPairWeight_mean_zero hp hp' hpp'
  have hmain :
      (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          (ℓ / (Nat.lcm d e : ℂ))) = 0 := by
    calc
      (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          (ℓ / (Nat.lcm d e : ℂ))) =
        ℓ * (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
          ramanujanPairWeight p p' d e /
            (Nat.lcm d e : ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
      _ = 0 := by rw [hmean, mul_zero]
  rw [sum_ramanujan_product_eq_multipleCounts A B hp hp']
  calc
    (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
      ramanujanPairWeight p p' d e *
        (integerMultipleCount A B (Nat.lcm d e) : ℂ)) =
      (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          (ℓ / (Nat.lcm d e : ℂ))) +
      ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          integerMultipleError A B (Nat.lcm d e) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e _
        simp only [integerMultipleError]
        dsimp [ℓ]
        ring
    _ = ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          integerMultipleError A B (Nat.lcm d e) := by rw [hmain, zero_add]

/-- Uniform incomplete orthogonality on every nonempty half-open integer
interval.  The constant is independent of both endpoints. -/
theorem ramanujan_incomplete_orthogonality_Ico
    (A B : ℤ) (hAB : A ≤ B) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Ico A B, ramanujanSum p n * ramanujanSum p' n‖ ≤
      2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) := by
  rw [sum_ramanujan_product_eq_endpointErrors A B hp hp' hpp']
  calc
    ‖∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
      ramanujanPairWeight p p' d e *
        integerMultipleError A B (Nat.lcm d e)‖ ≤
      ∑ d ∈ p.divisors, ‖∑ e ∈ p'.divisors,
        ramanujanPairWeight p p' d e *
          integerMultipleError A B (Nat.lcm d e)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ‖ramanujanPairWeight p p' d e *
          integerMultipleError A B (Nat.lcm d e)‖ := by
      gcongr with d hd
      exact norm_sum_le _ _
    _ ≤ ∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        2 * ‖ramanujanPairWeight p p' d e‖ := by
      gcongr with d hd e he
      rw [norm_mul]
      have hm := divisorPair_lcm_ne_zero hd he
      have herr := norm_integerMultipleError_le_two A B hAB hm
      nlinarith [norm_nonneg (ramanujanPairWeight p p' d e)]
    _ = 2 * (∑ d ∈ p.divisors, ∑ e ∈ p'.divisors,
        ‖ramanujanPairWeight p p' d e‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
    _ ≤ 2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_norm_ramanujanPairWeight_le p p') (by norm_num)

/-- Uniform incomplete orthogonality for arbitrary ordered endpoints; a
reversed half-open interval is empty. -/
theorem ramanujan_incomplete_orthogonality_Ico_all
    (A B : ℤ) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Ico A B, ramanujanSum p n * ramanujanSum p' n‖ ≤
      2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) := by
  by_cases hAB : A ≤ B
  · exact ramanujan_incomplete_orthogonality_Ico A B hAB hp hp' hpp'
  · rw [Finset.Ico_eq_empty (not_lt_of_ge (le_of_not_ge hAB))]
    simp only [Finset.sum_empty, norm_zero]
    positivity

/-- Closed-interval form of uniform incomplete orthogonality. -/
theorem ramanujan_incomplete_orthogonality_Icc
    (A B : ℤ) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Icc A B, ramanujanSum p n * ramanujanSum p' n‖ ≤
      2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) := by
  have hsets : Icc A B = Ico A (B + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsets]
  exact ramanujan_incomplete_orthogonality_Ico_all A (B + 1) hp hp' hpp'

/-- Hermitian half-open form.  Ramanujan sums are real, so conjugation does
not change the estimate. -/
theorem ramanujan_incomplete_orthogonality_Ico_conj
    (A B : ℤ) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Ico A B,
      ramanujanSum p n * conj (ramanujanSum p' n)‖ ≤
      2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) := by
  simpa only [conj_ramanujanSum] using!
    ramanujan_incomplete_orthogonality_Ico_all A B hp hp' hpp'

/-- Hermitian closed-interval form. -/
theorem ramanujan_incomplete_orthogonality_Icc_conj
    (A B : ℤ) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Icc A B,
      ramanujanSum p n * conj (ramanujanSum p' n)‖ ≤
      2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) := by
  simpa only [conj_ramanujanSum] using!
    ramanujan_incomplete_orthogonality_Icc A B hp hp' hpp'

private theorem sum_Icc_natCast_eq_sum_Icc_int
    (i j : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Icc i j, f (n : ℤ)) =
      ∑ z ∈ Icc (i : ℤ) (j : ℤ), f z := by
  refine Finset.sum_bij (fun n _ ↦ (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    change (n : ℤ) ∈ Icc (i : ℤ) (j : ℤ)
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    change (n₁ : ℤ) = (n₂ : ℤ) at heq
    exact_mod_cast heq
  · intro z hz
    have hz' := Finset.mem_Icc.mp hz
    have hzNonneg : 0 ≤ z := (by positivity : (0 : ℤ) ≤ (i : ℤ)).trans hz'.1
    have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzNonneg
    refine ⟨z.toNat, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have hiZ : (i : ℤ) ≤ (z.toNat : ℤ) := by simpa [hcast] using! hz'.1
      have hjZ : (z.toNat : ℤ) ≤ (j : ℤ) := by simpa [hcast] using! hz'.2
      constructor
      · exact_mod_cast hiZ
      · exact_mod_cast hjZ
    · change (z.toNat : ℤ) = z
      exact hcast
  · intro n hn
    rfl

/-- Natural-number closed-interval form, matching the indexing convention
of finite Abel summation. -/
theorem ramanujan_incomplete_orthogonality_nat_Icc
    (i j : ℕ) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Icc i j,
      ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)‖ ≤
      2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) := by
  calc
    ‖∑ n ∈ Icc i j,
      ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)‖ =
      ‖∑ z ∈ Icc (i : ℤ) (j : ℤ),
        ramanujanSum p z * ramanujanSum p' z‖ := by
          congr 1
          exact sum_Icc_natCast_eq_sum_Icc_int i j
            (fun z ↦ ramanujanSum p z * ramanujanSum p' z)
    _ ≤ 2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) :=
      ramanujan_incomplete_orthogonality_Icc (i : ℤ) (j : ℤ) hp hp' hpp'

/-- Finite bounded-variation/Abel corollary.  Both the right endpoint and
every discrete variation term are explicit, so no convergence or hidden
boundary assumption is needed. -/
theorem norm_weighted_ramanujan_product_le
    (w : ℕ → ℂ) {u v p p' : ℕ} (huv : u ≤ v)
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Icc u v,
      (ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) * w n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        (‖w v‖ + ∑ n ∈ Ico u v, ‖w n - w (n + 1)‖) := by
  apply norm_sum_mul_le_intervalBound
    (fun n : ℕ ↦ ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ))
    w huv
  intro i j hij
  exact ramanujan_incomplete_orthogonality_nat_Icc i j hp hp' hpp'

end

end Erdos1002
