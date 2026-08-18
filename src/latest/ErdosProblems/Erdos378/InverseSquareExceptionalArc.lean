/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.PrimeWeightedInterval
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A trigonometric majorant for the inverse-square exceptional arc

The bad fractional-part interval has length `19/100`.  The fourth power of a
shifted cosine has mean `21875/52488 < 1/2`, which is the strict inequality
needed in Granville--Ramaré Proposition 3.3.
-/

open scoped BigOperators

namespace Erdos378
namespace InverseSquareExceptionalArc

open PrimeReciprocal
open ReciprocalExponential
open InverseSquareCorrelation
open PrimeWeightedInterval
open ReciprocalPrimeSelection

noncomputable section

def exceptionalArcMean : ℝ := 21875 / 52488

lemma exceptionalArcMean_lt_half : exceptionalArcMean < 1 / 2 := by
  norm_num [exceptionalArcMean]

def exceptionalArcMajorant (t : ℝ) : ℝ :=
  (625 / 6561 : ℝ) *
    ((35 / 8 : ℝ) + 7 * Real.cos t +
      (7 / 2 : ℝ) * Real.cos (2 * t) + Real.cos (3 * t) +
        (1 / 8 : ℝ) * Real.cos (4 * t))

lemma exceptionalArcMajorant_factor (t : ℝ) :
    exceptionalArcMajorant t =
      (625 / 6561 : ℝ) * (1 + Real.cos t) ^ 4 := by
  unfold exceptionalArcMajorant
  rw [show 4 * t = 2 * (2 * t) by ring,
    Real.cos_two_mul (2 * t), Real.cos_two_mul t, Real.cos_three_mul]
  ring

lemma exceptional_arc_cos_lower {u : ℝ}
    (hu₀ : 81 / 100 ≤ u) (hu₁ : u ≤ 1) :
    4 / 5 ≤ Real.cos (2 * Real.pi * (u - 181 / 200)) := by
  let v : ℝ := u - 181 / 200
  let t : ℝ := 2 * Real.pi * v
  have hv : |v| ≤ 19 / 200 := by
    rw [abs_le]
    dsimp only [v]
    constructor <;> linarith
  have ht : |t| ≤ 19 * Real.pi / 100 := by
    dsimp only [t]
    rw [abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le]
    norm_num
    nlinarith [Real.pi_pos]
  have hpi : Real.pi < 315 / 100 := by
    convert Real.pi_lt_d2 using 1 <;> norm_num
  have ht' : |t| < 3 / 5 := by
    calc
      |t| ≤ 19 * Real.pi / 100 := ht
      _ < 3 / 5 := by nlinarith
  have hsq : t ^ 2 < (3 / 5 : ℝ) ^ 2 := by
    rw [sq_lt_sq]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5)]
    exact ht'
  have hcos : 1 - t ^ 2 / 2 ≤ Real.cos t :=
    Real.one_sub_sq_div_two_le_cos
  have hout : (4 / 5 : ℝ) ≤ Real.cos t := by nlinarith [hsq, hcos]
  simpa only [t, v] using hout

lemma one_le_exceptionalArcMajorant {u : ℝ}
    (hu₀ : 81 / 100 ≤ u) (hu₁ : u ≤ 1) :
    1 ≤ exceptionalArcMajorant (2 * Real.pi * (u - 181 / 200)) := by
  rw [exceptionalArcMajorant_factor]
  have hc := exceptional_arc_cos_lower hu₀ hu₁
  have hb : (9 / 5 : ℝ) ≤
      1 + Real.cos (2 * Real.pi * (u - 181 / 200)) := by linarith
  have hp : (9 / 5 : ℝ) ^ 4 ≤
      (1 + Real.cos (2 * Real.pi * (u - 181 / 200))) ^ 4 := by
    exact pow_le_pow_left₀ (by norm_num) hb 4
  calc
    (1 : ℝ) = (625 / 6561 : ℝ) * (9 / 5 : ℝ) ^ 4 := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)

def inverseSquarePrimeMode (h n k : ℕ) : ℂ :=
  PrimeWeightedInterval.primeWeightedInterval
    (inverseSquareWeight ((h * n : ℕ) : ℝ))
    (Nat.sqrt k) (sourcePrimeUpper k)

def shiftedInverseSquarePrimeMode (h n k : ℕ) : ℂ :=
  e ((181 : ℝ) * h / 200) * inverseSquarePrimeMode h n k

lemma shifted_inverseSquareWeight_re (h n p : ℕ) (hp : 0 < p) :
    (e ((181 : ℝ) * h / 200) *
        inverseSquareWeight ((h * n : ℕ) : ℝ) p).re =
      Real.cos (h * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) := by
  unfold inverseSquareWeight
  rw [← e_add]
  have hpR : (p : ℝ) ^ 2 ≠ 0 := by positivity
  rw [show (181 : ℝ) * h / 200 + -((h * n : ℕ) : ℝ) / (p : ℝ) ^ 2 =
      -(h * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200)) by
    push_cast
    field_simp
    ring]
  rw [ReciprocalPrimeSelection.e_re]
  rw [show 2 * Real.pi * (-(h * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) =
      -(h * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) by ring,
    Real.cos_neg]

lemma inverse_square_phase_cos_eq_mod (h n p : ℕ) (hp : 0 < p) :
    Real.cos (h * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) =
      Real.cos (h * (2 * Real.pi *
        (((n % p ^ 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) := by
  have hp2 : 0 < p ^ 2 := pow_pos hp 2
  have hnquot : (n : ℝ) / (p : ℝ) ^ 2 =
      (n / p ^ 2 : ℕ) + (n % p ^ 2 : ℕ) / (p : ℝ) ^ 2 := by
    have hpR : (p : ℝ) ^ 2 ≠ 0 := by positivity
    push_cast
    field_simp
    exact_mod_cast (show n = p ^ 2 * (n / p ^ 2) + n % p ^ 2 by
      simpa using (Nat.div_add_mod n (p ^ 2)).symm)
  rw [hnquot]
  rw [show h * (2 * Real.pi *
      (((n / p ^ 2 : ℕ) : ℝ) + (n % p ^ 2 : ℕ) / (p : ℝ) ^ 2 - 181 / 200)) =
      h * (2 * Real.pi *
        ((n % p ^ 2 : ℕ) / (p : ℝ) ^ 2 - 181 / 200)) +
        (h * (n / p ^ 2) : ℕ) * (2 * Real.pi) by
    push_cast
    ring]
  exact Real.cos_add_nat_mul_two_pi _ _

def exceptionalPrimeSet (n k : ℕ) : Finset ℕ :=
  (sourcePrimeSet k).filter fun p ↦ 81 * p ^ 2 ≤ 100 * (n % p ^ 2)

def exceptionalPrimeLogMass (n k : ℕ) : ℝ :=
  ∑ p ∈ exceptionalPrimeSet n k, Real.log (p : ℝ)

def exceptionalArcMajorantSum (n k : ℕ) : ℝ :=
  ∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) *
    exceptionalArcMajorant
      (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))

lemma exceptionalPrimeLogMass_le_majorantSum (n k : ℕ) :
    exceptionalPrimeLogMass n k ≤ exceptionalArcMajorantSum n k := by
  unfold exceptionalPrimeLogMass exceptionalArcMajorantSum exceptionalPrimeSet
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p hp
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
  split_ifs with hbad
  · have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hp2R : (0 : ℝ) < (p : ℝ) ^ 2 := pow_pos hpR 2
    have hfrac0 : (81 / 100 : ℝ) ≤
        ((n % p ^ 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 := by
      rw [le_div_iff₀ hp2R]
      have hbadR : (81 : ℝ) * (p : ℝ) ^ 2 ≤
          100 * (n % p ^ 2 : ℕ) := by exact_mod_cast hbad
      nlinarith
    have hfrac1 : ((n % p ^ 2 : ℕ) : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one hp2R]
      exact_mod_cast (Nat.mod_lt n (pow_pos hpprime.pos 2)).le
    have hmaj := one_le_exceptionalArcMajorant hfrac0 hfrac1
    have hfactor : exceptionalArcMajorant
        (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200)) =
      exceptionalArcMajorant
        (2 * Real.pi * (((n % p ^ 2 : ℕ) : ℝ) /
          (p : ℝ) ^ 2 - 181 / 200)) := by
      unfold exceptionalArcMajorant
      have hm (j : ℕ) : Real.cos (j *
          (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) =
        Real.cos (j * (2 * Real.pi * (((n % p ^ 2 : ℕ) : ℝ) /
          (p : ℝ) ^ 2 - 181 / 200))) := inverse_square_phase_cos_eq_mod j n p hpprime.pos
      have h1 := hm 1
      have h2 := hm 2
      have h3 := hm 3
      have h4 := hm 4
      norm_num at h1
      norm_num at h2 h3 h4
      rw [h1, h2, h3, h4]
    rw [hfactor]
    have hlog : 0 ≤ Real.log (p : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hpprime.one_lt.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmaj hlog
  · have hlog : 0 ≤ Real.log (p : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hpprime.one_lt.le
    exact mul_nonneg hlog
      (by
        rw [exceptionalArcMajorant_factor]
        positivity)

lemma shiftedInverseSquarePrimeMode_re (h n k : ℕ) :
    (shiftedInverseSquarePrimeMode h n k).re =
      ∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) *
        Real.cos (h * (2 * Real.pi *
          ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) := by
  unfold shiftedInverseSquarePrimeMode inverseSquarePrimeMode
  unfold PrimeWeightedInterval.primeWeightedInterval sourcePrimeSet
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show e (181 * (h : ℝ) / 200) *
      ((Real.log (p : ℝ) : ℂ) * inverseSquareWeight ((h * n : ℕ) : ℝ) p) =
        (Real.log (p : ℝ) : ℂ) *
          (e (181 * (h : ℝ) / 200) *
            inverseSquareWeight ((h * n : ℕ) : ℝ) p) by ring]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  exact shifted_inverseSquareWeight_re h n p (Finset.mem_filter.mp hp).2.pos

lemma exceptionalArcMajorantSum_eq_modes (n k : ℕ) :
    exceptionalArcMajorantSum n k =
      exceptionalArcMean * sourcePrimeLogMass k +
        (625 / 6561 : ℝ) *
          (7 * (shiftedInverseSquarePrimeMode 1 n k).re +
            (7 / 2 : ℝ) * (shiftedInverseSquarePrimeMode 2 n k).re +
            (shiftedInverseSquarePrimeMode 3 n k).re +
            (1 / 8 : ℝ) * (shiftedInverseSquarePrimeMode 4 n k).re) := by
  unfold exceptionalArcMajorantSum exceptionalArcMajorant exceptionalArcMean
  have h1 := shiftedInverseSquarePrimeMode_re 1 n k
  have h2 := shiftedInverseSquarePrimeMode_re 2 n k
  have h3 := shiftedInverseSquarePrimeMode_re 3 n k
  have h4 := shiftedInverseSquarePrimeMode_re 4 n k
  norm_num at h1 h2 h3 h4
  calc
    (∑ p ∈ sourcePrimeSet k,
        Real.log (p : ℝ) *
          ((625 / 6561 : ℝ) *
            ((35 / 8 : ℝ) + 7 * Real.cos
                (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200)) +
              (7 / 2 : ℝ) * Real.cos
                (2 * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) +
              Real.cos
                (3 * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) +
              (1 / 8 : ℝ) * Real.cos
                (4 * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200)))))) =
      (625 / 6561 : ℝ) *
        ((35 / 8 : ℝ) * (∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ)) +
          7 * (∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) * Real.cos
            (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))) +
          (7 / 2 : ℝ) * (∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) * Real.cos
            (2 * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200)))) +
          (∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) * Real.cos
            (3 * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200)))) +
          (1 / 8 : ℝ) * (∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) * Real.cos
            (4 * (2 * Real.pi * ((n : ℝ) / (p : ℝ) ^ 2 - 181 / 200))))) := by
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
    _ = _ := by
      rw [← h1, ← h2, ← h3, ← h4]
      unfold sourcePrimeLogMass
      ring

end

end InverseSquareExceptionalArc
end Erdos378
