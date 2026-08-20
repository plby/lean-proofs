/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.SmoothNumbers

namespace Erdos783

open Finset

noncomputable section

/-- Positive integers all of whose prime factors are at most `y`. -/
def IsSmoothAt (y a : ℕ) : Prop :=
  a ∈ Nat.smoothNumbers (y + 1)

instance (y : ℕ) : DecidablePred (IsSmoothAt y) := by
  intro a
  unfold IsSmoothAt
  infer_instance

/-- Mathlib's exact count of positive `y`-smooth integers at most `x`. -/
def smoothCountingFunction (x y : ℕ) : ℕ :=
  (Nat.smoothNumbersUpTo x (y + 1)).card

/-- The usual logarithmic smoothness parameter `log x / log y`. -/
def smoothParameter (x y : ℕ) : ℝ :=
  Real.log x / Real.log y

/-- On positive inputs with `y > 1`, being in the first smoothness strip is
exactly the elementary inequality `x ≤ y`. -/
theorem smoothParameter_le_one_iff_le
    {x y : ℕ} (hx : 0 < x) (hy : 2 ≤ y) :
    smoothParameter x y ≤ 1 ↔ x ≤ y := by
  have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
  have hyReal : 0 < (y : ℝ) := by positivity
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  constructor
  · intro hparameter
    have hlog : Real.log (x : ℝ) ≤ Real.log (y : ℝ) := by
      rw [smoothParameter, div_le_one hlogy] at hparameter
      exact hparameter
    have hcast : (x : ℝ) ≤ (y : ℝ) := by
      calc
        (x : ℝ) = Real.exp (Real.log (x : ℝ)) :=
          (Real.exp_log hxReal).symm
        _ ≤ Real.exp (Real.log (y : ℝ)) :=
          Real.exp_le_exp.mpr hlog
        _ = (y : ℝ) := Real.exp_log hyReal
    exact_mod_cast hcast
  · intro hxy
    rw [smoothParameter, div_le_one hlogy]
    exact Real.log_le_log hxReal (by exact_mod_cast hxy)

theorem smoothParameter_nonneg
    {x y : ℕ} (hx : 0 < x) (hy : 2 ≤ y) :
    0 ≤ smoothParameter x y := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hx))
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))

/-- A bound on the smoothness parameter is equivalent to the corresponding
real-power bound on `x`. -/
theorem natCast_le_rpow_of_smoothParameter_le
    {x y : ℕ} {U : ℝ}
    (hx : 0 < x) (hy : 2 ≤ y)
    (hparameter : smoothParameter x y ≤ U) :
    (x : ℝ) ≤ (y : ℝ) ^ U := by
  have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
  have hyReal : 0 < (y : ℝ) := by positivity
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog :
      Real.log (x : ℝ) ≤ U * Real.log (y : ℝ) := by
    rw [smoothParameter] at hparameter
    have := (div_le_iff₀ hlogY).mp hparameter
    linarith
  calc
    (x : ℝ) = Real.exp (Real.log (x : ℝ)) :=
      (Real.exp_log hxReal).symm
    _ ≤ Real.exp (U * Real.log (y : ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ = (y : ℝ) ^ U := by
      rw [Real.rpow_def_of_pos hyReal]
      congr 1
      ring

/-- Buchstab descent: removing a prime larger than the current smoothness
cutoff lowers the smoothness parameter by more than one. -/
theorem smoothParameter_div_lt_pred
    {x y p : ℕ} {k : ℕ}
    (hx : 0 < x) (hy : 2 ≤ y)
    (hyp : y < p) (hpx : p ≤ x)
    (hparameter : smoothParameter x y ≤ (k : ℝ) + 1) :
    smoothParameter (x / p) p < k := by
  have hpPos : 0 < p := by omega
  have hdivPos : 0 < x / p := Nat.div_pos hpx hpPos
  have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hpPos
  have hlogP : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogYltP : Real.log (y : ℝ) < Real.log (p : ℝ) :=
    Real.strictMonoOn_log
      (show (y : ℝ) ∈ Set.Ioi 0 by
        simp only [Set.mem_Ioi]
        exact_mod_cast (show (0 : ℕ) < y by omega))
      (show (p : ℝ) ∈ Set.Ioi 0 by
        simp only [Set.mem_Ioi]
        exact_mod_cast hpPos)
      (by exact_mod_cast hyp)
  have hlogX :
      Real.log (x : ℝ) ≤ ((k : ℝ) + 1) * Real.log (y : ℝ) := by
    rw [smoothParameter] at hparameter
    exact (div_le_iff₀ hlogY).mp hparameter
  have hcastDiv : ((x / p : ℕ) : ℝ) ≤ (x : ℝ) / p :=
    Nat.cast_div_le
  have hcastDivPos : 0 < ((x / p : ℕ) : ℝ) := by
    exact_mod_cast hdivPos
  have hlogDiv :
      Real.log ((x / p : ℕ) : ℝ) ≤ Real.log ((x : ℝ) / p) :=
    Real.log_le_log hcastDivPos hcastDiv
  have hlogQuot :
      Real.log ((x : ℝ) / p) =
        Real.log (x : ℝ) - Real.log (p : ℝ) :=
    Real.log_div hxReal.ne' hpReal.ne'
  rw [smoothParameter]
  apply (div_lt_iff₀ hlogP).2
  calc
    Real.log ((x / p : ℕ) : ℝ) ≤
        Real.log ((x : ℝ) / p) := hlogDiv
    _ = Real.log (x : ℝ) - Real.log (p : ℝ) := hlogQuot
    _ ≤ ((k : ℝ) + 1) * Real.log (y : ℝ) -
        Real.log (p : ℝ) := by linarith
    _ < (k : ℝ) * Real.log (p : ℝ) := by
      have hk0 : (0 : ℝ) ≤ k := by positivity
      nlinarith [mul_lt_mul_of_pos_left hlogYltP
        (by positivity : 0 < (k : ℝ) + 1)]

/-- Replacing the real quotient `x / p` by natural-number division changes
the logarithmic Buchstab parameter by at most `log 2 / log p`. -/
theorem smoothParameter_div_approx
    {x p : ℕ} (hp : 2 ≤ p) (hpx : p ≤ x) :
    |smoothParameter (x / p) p -
        (Real.log (x : ℝ) / Real.log (p : ℝ) - 1)| ≤
      Real.log 2 / Real.log (p : ℝ) := by
  have hpPos : 0 < p := by omega
  have hxPos : 0 < x := hpPos.trans_le hpx
  have hqPos : 0 < x / p := Nat.div_pos hpx hpPos
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hpPos
  have hxReal : 0 < (x : ℝ) := by exact_mod_cast hxPos
  have hqReal : 0 < ((x / p : ℕ) : ℝ) := by exact_mod_cast hqPos
  have hlogP : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  let r : ℝ := (x : ℝ) / (p : ℝ)
  have hrPos : 0 < r := div_pos hxReal hpReal
  have hqLeR : ((x / p : ℕ) : ℝ) ≤ r := Nat.cast_div_le
  have hrLt : r < ((x / p : ℕ) : ℝ) + 1 := by
    have hnat := Nat.lt_mul_div_succ x hpPos
    have hcast : (x : ℝ) < (p : ℝ) * ((x / p : ℕ) + 1) := by
      exact_mod_cast hnat
    exact (div_lt_iff₀ hpReal).2 (by
      simpa [r, mul_comm, mul_left_comm, mul_assoc] using hcast)
  have hqOne : (1 : ℝ) ≤ (x / p : ℕ) := by exact_mod_cast hqPos
  have hrLeTwoQ : r ≤ 2 * ((x / p : ℕ) : ℝ) := by
    calc
      r ≤ ((x / p : ℕ) : ℝ) + 1 := hrLt.le
      _ ≤ 2 * ((x / p : ℕ) : ℝ) := by linarith
  have hlogLow :
      Real.log ((x / p : ℕ) : ℝ) ≤ Real.log r :=
    Real.log_le_log hqReal hqLeR
  have hlogHigh :
      Real.log r ≤ Real.log 2 + Real.log ((x / p : ℕ) : ℝ) := by
    calc
      Real.log r ≤ Real.log (2 * ((x / p : ℕ) : ℝ)) :=
        Real.log_le_log hrPos hrLeTwoQ
      _ = Real.log 2 + Real.log ((x / p : ℕ) : ℝ) := by
        rw [Real.log_mul (by norm_num) hqReal.ne']
  have hideal :
      Real.log (x : ℝ) / Real.log (p : ℝ) - 1 =
        Real.log r / Real.log (p : ℝ) := by
    dsimp only [r]
    rw [Real.log_div hxReal.ne' hpReal.ne']
    field_simp [hlogP.ne']
  rw [hideal, smoothParameter]
  have hnonneg :
      0 ≤ Real.log r / Real.log (p : ℝ) -
        Real.log ((x / p : ℕ) : ℝ) / Real.log (p : ℝ) :=
    sub_nonneg.mpr ((div_le_div_iff_of_pos_right hlogP).2 hlogLow)
  rw [abs_sub_comm, abs_of_nonneg hnonneg]
  have hdivHigh := (div_le_div_iff_of_pos_right hlogP).2 hlogHigh
  calc
    Real.log r / Real.log (p : ℝ) -
        Real.log ((x / p : ℕ) : ℝ) / Real.log (p : ℝ) ≤
      (Real.log 2 + Real.log ((x / p : ℕ) : ℝ)) /
          Real.log (p : ℝ) -
        Real.log ((x / p : ℕ) : ℝ) / Real.log (p : ℝ) :=
      sub_le_sub_right hdivHigh _
    _ = Real.log 2 / Real.log (p : ℝ) := by ring

@[simp] theorem smoothCountingFunction_zero (y : ℕ) :
    smoothCountingFunction 0 y = 0 := by
  rw [smoothCountingFunction, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨k, hk⟩
  rw [Nat.mem_smoothNumbersUpTo] at hk
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk.1
  subst k
  exact Nat.ne_zero_of_mem_smoothNumbers hk.2 rfl

/-- Before the first transition every positive integer up to `x` is smooth. -/
theorem smoothCountingFunction_eq_self_of_le {x y : ℕ} (hxy : x ≤ y) :
    smoothCountingFunction x y = x := by
  have hset : Nat.smoothNumbersUpTo x (y + 1) = Finset.Icc 1 x := by
    ext m
    rw [Nat.mem_smoothNumbersUpTo, Finset.mem_Icc]
    constructor
    · rintro ⟨hmx, hsmooth⟩
      exact ⟨Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_zero_of_mem_smoothNumbers hsmooth), hmx⟩
    · rintro ⟨hmPos, hmx⟩
      exact ⟨hmx, Nat.mem_smoothNumbers_of_lt (by omega) (by omega)⟩
  rw [smoothCountingFunction, hset, Nat.card_Icc]
  omega

/-!
## Exact largest-prime Buchstab decomposition

For a prime `p`, `largestPrimeFiber x p` consists of the integers
`p * m ≤ x` for which every prime factor of `m` is at most `p`.
Thus `p` is the largest prime factor (with one copy removed), and the
fibres for different primes are disjoint.
-/

def largestPrimeFiber (x p : ℕ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo (x / p) (p + 1)).image
    (fun m ↦ p * m)

theorem card_largestPrimeFiber
    {x p : ℕ} (hp : p.Prime) :
    (largestPrimeFiber x p).card =
      smoothCountingFunction (x / p) p := by
  rw [largestPrimeFiber, smoothCountingFunction,
    Finset.card_image_iff]
  intro m _hm n _hn hmn
  exact Nat.eq_of_mul_eq_mul_left hp.pos hmn

private theorem largestPrimeFiber_disjoint
    {x p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Disjoint (largestPrimeFiber x p)
      (largestPrimeFiber x q) := by
  rw [Finset.disjoint_left]
  intro k hkp hkq
  rw [largestPrimeFiber, Finset.mem_image] at hkp hkq
  obtain ⟨m, hm, rfl⟩ := hkp
  obtain ⟨n, hn, hEq⟩ := hkq
  rw [Nat.mem_smoothNumbersUpTo] at hm hn
  by_cases hpLtq : p < q
  · have hqDvd : q ∣ p * m := by
      rw [← hEq]
      exact dvd_mul_right q n
    have hqNotDvdP : ¬q ∣ p := by
      intro hqp
      have := Nat.le_of_dvd hp.pos hqp
      omega
    have hqDvdM : q ∣ m :=
      (hq.dvd_mul.mp hqDvd).resolve_left hqNotDvdP
    have hqUpper :
        q < p + 1 := by
      rw [Nat.mem_smoothNumbers'] at hm
      exact hm.2 q hq hqDvdM
    omega
  · have hqLtp : q < p := by omega
    have hpDvd : p ∣ q * n := by
      rw [hEq]
      exact dvd_mul_right p m
    have hpNotDvdQ : ¬p ∣ q := by
      intro hpqDvd
      have := Nat.le_of_dvd hq.pos hpqDvd
      omega
    have hpDvdN : p ∣ n :=
      (hp.dvd_mul.mp hpDvd).resolve_left hpNotDvdQ
    have hpUpper :
        p < q + 1 := by
      rw [Nat.mem_smoothNumbers'] at hn
      exact hn.2 p hp hpDvdN
    omega

private theorem nonsmoothUpTo_eq_biUnion_largestPrimeFiber
    (x y : ℕ) :
    (Finset.Icc 1 x).filter (fun k ↦ ¬IsSmoothAt y k) =
      ((Finset.Ioc y x).filter Nat.Prime).biUnion
        (largestPrimeFiber x) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_biUnion, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hkPos, hkx⟩, hkNotSmooth⟩
    rw [IsSmoothAt, Nat.mem_smoothNumbers'] at hkNotSmooth
    push Not at hkNotSmooth
    obtain ⟨q, hqPrime, hqDvd, hyq⟩ := hkNotSmooth
    have hkNe : k ≠ 0 := Nat.ne_of_gt hkPos
    have hqMem : q ∈ k.primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hqPrime, hqDvd, hkNe⟩
    have hnonempty : k.primeFactors.Nonempty :=
      ⟨q, hqMem⟩
    let p : ℕ := k.primeFactors.max' hnonempty
    have hpMem : p ∈ k.primeFactors :=
      Finset.max'_mem _ _
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors hpMem
    have hpDvd : p ∣ k :=
      Nat.dvd_of_mem_primeFactors hpMem
    have hqp : q ≤ p :=
      Finset.le_max' _ _ hqMem
    have hyp : y < p := by omega
    have hpk : p ≤ k :=
      Nat.le_of_dvd hkPos hpDvd
    refine ⟨p, ⟨⟨hyp, hpk.trans hkx⟩, hpPrime⟩, ?_⟩
    rw [largestPrimeFiber, Finset.mem_image]
    refine ⟨k / p, ?_, ?_⟩
    · rw [Nat.mem_smoothNumbersUpTo]
      refine ⟨Nat.div_le_div_right hkx, ?_⟩
      rw [Nat.mem_smoothNumbers']
      intro r hrPrime hrDvd
      have hrDvdK : r ∣ k := by
        rw [← Nat.div_mul_cancel hpDvd]
        exact dvd_mul_of_dvd_left hrDvd p
      have hrMem : r ∈ k.primeFactors :=
        Nat.mem_primeFactors.mpr
          ⟨hrPrime, hrDvdK, hkNe⟩
      have hrp : r ≤ p :=
        Finset.le_max' _ _ hrMem
      omega
    · exact Nat.mul_div_cancel' hpDvd
  · rintro ⟨p, ⟨⟨hyp, hpx⟩, hpPrime⟩, hkp⟩
    rw [largestPrimeFiber, Finset.mem_image] at hkp
    obtain ⟨m, hm, rfl⟩ := hkp
    rw [Nat.mem_smoothNumbersUpTo] at hm
    have hmPos : 0 < m :=
      Nat.pos_of_ne_zero
        (Nat.ne_zero_of_mem_smoothNumbers hm.2)
    have hpmLe : p * m ≤ x := by
      have := (Nat.le_div_iff_mul_le hpPrime.pos).mp hm.1
      simpa [Nat.mul_comm] using this
    refine ⟨⟨Nat.mul_pos hpPrime.pos hmPos, hpmLe⟩, ?_⟩
    rw [IsSmoothAt, Nat.mem_smoothNumbers']
    push Not
    refine ⟨p, hpPrime, dvd_mul_right p m, ?_⟩
    omega

/--
Exact Buchstab identity, classified by the largest prime factor.
The subtraction is a natural subtraction; the preceding partition
also proves that the prime-fibre sum is at most `x`.
-/
theorem smoothCountingFunction_buchstab
    (x y : ℕ) :
    smoothCountingFunction x y =
      x -
        ∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
          smoothCountingFunction (x / p) p := by
  have hpartition :=
    Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card
      x (y + 1)
  have hrough :
      Nat.roughNumbersUpTo x (y + 1) =
        (Finset.Icc 1 x).filter
          (fun k ↦ ¬IsSmoothAt y k) := by
    apply Finset.ext
    intro k
    simp only [Nat.roughNumbersUpTo, Finset.mem_filter,
      Finset.mem_range, Nat.lt_add_one_iff]
    rw [Finset.mem_Icc]
    simp only [IsSmoothAt]
    constructor
    · rintro ⟨hkx, hk0, hkSmooth⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hk0, hkx⟩,
        hkSmooth⟩
    · rintro ⟨⟨hk1, hkx⟩, hkSmooth⟩
      exact ⟨hkx, Nat.ne_of_gt hk1, hkSmooth⟩
  have hdisjoint :
      ∀ p ∈ (Finset.Ioc y x).filter Nat.Prime,
        ∀ q ∈ (Finset.Ioc y x).filter Nat.Prime,
          p ≠ q →
            Disjoint (largestPrimeFiber x p)
              (largestPrimeFiber x q) := by
    intro p hp q hq hpq
    exact largestPrimeFiber_disjoint
      (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2 hpq
  rw [hrough,
    nonsmoothUpTo_eq_biUnion_largestPrimeFiber,
    Finset.card_biUnion hdisjoint] at hpartition
  rw [smoothCountingFunction]
  have hsum :
      ∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
          (largestPrimeFiber x p).card =
        ∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
          smoothCountingFunction (x / p) p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact card_largestPrimeFiber
      (Finset.mem_filter.mp hp).2
  rw [hsum] at hpartition
  omega


end

end Erdos783
