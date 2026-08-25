import ErdosProblems.Erdos448.HalberstamComplete448
import ErdosProblems.Erdos67.MRTMajorArc

/-!
# The Halberstam--Richert input in Granville--Soundararajan Lemma 7.1

For a multiplicative coefficient `f`, let `g = f * μ`.  The proof of
Granville--Soundararajan Lemma 7.1 applies Halberstam--Richert to `|g|`.
This file supplies that input without an analytic premise: it proves the
prime-power identity

`g (p^(j+1)) = f (p^(j+1)) - f (p^j)`

and deduces the explicit finite Halberstam--Richert bound from the existing
axiom-free Erdos448 engine.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Erdos67

/-- Put a coefficient on positive naturals into Mathlib's arithmetic-function
type, whose value at zero is required to vanish. -/
noncomputable def positiveArithmeticFunction (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

@[simp] theorem positiveArithmeticFunction_zero (f : ℕ → ℂ) :
    positiveArithmeticFunction f 0 = 0 := by
  simp [positiveArithmeticFunction]

@[simp] theorem positiveArithmeticFunction_apply {f : ℕ → ℂ} {n : ℕ}
    (hn : n ≠ 0) : positiveArithmeticFunction f n = f n := by
  simp [positiveArithmeticFunction, hn]

theorem positiveArithmeticFunction_isMultiplicative
    {f : ℕ → ℂ} (hf : IsMultiplicativeOnPositiveNat f) :
    ArithmeticFunction.IsMultiplicative (positiveArithmeticFunction f) := by
  refine ⟨by simpa using hf.1, ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp
  simp only [positiveArithmeticFunction_apply hm,
    positiveArithmeticFunction_apply hn,
    positiveArithmeticFunction_apply (Nat.mul_ne_zero hm hn)]
  exact hf.2 m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn

/-- The coefficient `g = f * μ` from GS Lemma 7.1. -/
noncomputable def gsMoebiusCoefficient (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  positiveArithmeticFunction f *
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

theorem gsMoebiusCoefficient_isMultiplicative
    {f : ℕ → ℂ} (hf : IsMultiplicativeOnPositiveNat f) :
    ArithmeticFunction.IsMultiplicative (gsMoebiusCoefficient f) := by
  exact (positiveArithmeticFunction_isMultiplicative hf).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast

@[simp] theorem gsMoebiusCoefficient_zero (f : ℕ → ℂ) :
    gsMoebiusCoefficient f 0 = 0 := ArithmeticFunction.map_zero

@[simp] theorem gsMoebiusCoefficient_one {f : ℕ → ℂ}
    (hf : IsMultiplicativeOnPositiveNat f) : gsMoebiusCoefficient f 1 = 1 := by
  exact (gsMoebiusCoefficient_isMultiplicative hf).1

theorem gsMoebiusCoefficient_mul_zeta
    (f : ℕ → ℂ) :
    gsMoebiusCoefficient f *
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) =
      positiveArithmeticFunction f := by
  rw [gsMoebiusCoefficient, mul_assoc,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]

/-- At prime powers, `f * μ` is the first difference of `f`. -/
theorem gsMoebiusCoefficient_prime_pow_succ
    (f : ℕ → ℂ) {p j : ℕ} (hp : p.Prime) :
    gsMoebiusCoefficient f (p ^ (j + 1)) =
      f (p ^ (j + 1)) - f (p ^ j) := by
  let g := gsMoebiusCoefficient f
  have hconv : g * (ArithmeticFunction.zeta : ArithmeticFunction ℂ) =
      positiveArithmeticFunction f := gsMoebiusCoefficient_mul_zeta f
  have hsum (k : ℕ) :
      (∑ i ∈ Finset.range (k + 1), g (p ^ i)) = f (p ^ k) := by
    have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
    calc
      (∑ i ∈ Finset.range (k + 1), g (p ^ i)) =
          ∑ d ∈ (p ^ k).divisors, g d := by
            symm
            exact Nat.sum_divisors_prime_pow hp
      _ = (g * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (p ^ k) := by
            rw [ArithmeticFunction.coe_mul_zeta_apply]
      _ = positiveArithmeticFunction f (p ^ k) := by rw [hconv]
      _ = f (p ^ k) := positiveArithmeticFunction_apply hpk
  have hnext := hsum (j + 1)
  have hprev := hsum j
  rw [show j + 1 + 1 = (j + 1) + 1 by omega,
    Finset.sum_range_succ] at hnext
  rw [show j + 1 = j + 1 by rfl] at hprev
  dsimp [g] at hnext hprev ⊢
  rw [hprev] at hnext
  linear_combination hnext

/-- The nonnegative multiplicative weight to which Halberstam--Richert is
applied in the proof of GS Lemma 7.1. -/
noncomputable def gsMoebiusNorm (f : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖gsMoebiusCoefficient f n‖

@[simp] theorem gsMoebiusNorm_zero (f : ℕ → ℂ) :
    gsMoebiusNorm f 0 = 0 := by simp [gsMoebiusNorm]

@[simp] theorem gsMoebiusNorm_one {f : ℕ → ℂ}
    (hf : IsMultiplicativeOnPositiveNat f) : gsMoebiusNorm f 1 = 1 := by
  simp [gsMoebiusNorm, gsMoebiusCoefficient_one hf]

theorem gsMoebiusNorm_nonneg (f : ℕ → ℂ) (n : ℕ) :
    0 ≤ gsMoebiusNorm f n := norm_nonneg _

theorem gsMoebiusNorm_mul
    {f : ℕ → ℂ} (hf : IsMultiplicativeOnPositiveNat f)
    {m n : ℕ} (hmn : m.Coprime n) :
    gsMoebiusNorm f (m * n) = gsMoebiusNorm f m * gsMoebiusNorm f n := by
  rw [gsMoebiusNorm, gsMoebiusNorm, gsMoebiusNorm,
    (gsMoebiusCoefficient_isMultiplicative hf).map_mul_of_coprime hmn,
    norm_mul]

theorem gsMoebiusNorm_prime_pow_succ_le_two
    {f : ℕ → ℂ} (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {p j : ℕ} (hp : p.Prime) :
    gsMoebiusNorm f (p ^ (j + 1)) ≤ 2 := by
  rw [gsMoebiusNorm, gsMoebiusCoefficient_prime_pow_succ f hp]
  calc
    ‖f (p ^ (j + 1)) - f (p ^ j)‖
        ≤ ‖f (p ^ (j + 1))‖ + ‖f (p ^ j)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (hone _) (hone _)
    _ = 2 := by norm_num

/-- The first local coefficient records precisely the prime discrepancy from
the constant function. -/
theorem gsMoebiusNorm_prime
    {f : ℕ → ℂ} (hf : IsMultiplicativeOnPositiveNat f)
    {p : ℕ} (hp : p.Prime) :
    gsMoebiusNorm f p = ‖f p - 1‖ := by
  rw [← pow_one p, gsMoebiusNorm,
    gsMoebiusCoefficient_prime_pow_succ f (j := 0) hp, pow_zero, hf.1]

/-- The refined local Euler factor used in GS Lemma 7.1.  Unlike the crude
uniform `2/(p-1)` estimate, it preserves the first coefficient
`‖f p - 1‖/p`; the remaining prime-power tail is `O(p⁻²)`. -/
theorem gsMoebiusNorm_localFactor_le
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, gsMoebiusNorm f (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      1 + ‖f p - 1‖ / (p : ℝ) + 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  let term : ℕ → ℝ := fun j =>
    gsMoebiusNorm f (p ^ j) / ((p ^ j : ℕ) : ℝ)
  let r : ℝ := (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ r := inv_nonneg.mpr hpR.le
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (lt_of_lt_of_le one_lt_two hpTwo)
  have htailBound (j : ℕ) : term (j + 2) ≤ 2 * r ^ (j + 2) := by
    have hden : (0 : ℝ) < ((p ^ (j + 2) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_pos hp.pos
    have hnum : gsMoebiusNorm f (p ^ (j + 2)) ≤ 2 := by
      convert gsMoebiusNorm_prime_pow_succ_le_two hone hp using 1 <;> omega
    calc
      term (j + 2) = gsMoebiusNorm f (p ^ (j + 2)) /
          ((p ^ (j + 2) : ℕ) : ℝ) := rfl
      _ ≤ 2 / ((p ^ (j + 2) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = 2 * r ^ (j + 2) := by
        rw [Nat.cast_pow]
        simp only [r, div_eq_mul_inv, inv_pow]
  have hmajorSummable : Summable (fun j : ℕ => 2 * r ^ (j + 2)) := by
    have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * r ^ 2)
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using hs
  have htailNonneg (j : ℕ) : 0 ≤ term (j + 2) := by
    exact div_nonneg (gsMoebiusNorm_nonneg f _) (Nat.cast_nonneg _)
  have htailSummable : Summable (fun j : ℕ => term (j + 2)) :=
    Summable.of_nonneg_of_le htailNonneg htailBound hmajorSummable
  have htermSummable : Summable term := (summable_nat_add_iff 2).1 htailSummable
  have hshiftSummable : Summable (fun j : ℕ => term (j + 1)) :=
    (summable_nat_add_iff 1).2 htermSummable
  have htailTsum :
      (∑' j : ℕ, term (j + 2)) ≤ ∑' j : ℕ, 2 * r ^ (j + 2) :=
    htailSummable.tsum_le_tsum htailBound hmajorSummable
  have hmajorTsum :
      (∑' j : ℕ, 2 * r ^ (j + 2)) = 2 * r ^ 2 / (1 - r) := by
    have hs := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * r ^ 2)).tsum_eq
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hs
  have hzero : term 0 = 1 := by
    simp [term, gsMoebiusNorm_one hmul]
  have honeTerm : term 1 = ‖f p - 1‖ / (p : ℝ) := by
    simp [term, gsMoebiusNorm_prime hmul hp]
  rw [show (∑' j : ℕ, gsMoebiusNorm f (p ^ j) /
      ((p ^ j : ℕ) : ℝ)) = ∑' j : ℕ, term j by rfl]
  rw [htermSummable.tsum_eq_zero_add, hzero,
    hshiftSummable.tsum_eq_zero_add, honeTerm]
  have htailFinal :
      (∑' j : ℕ, term (j + 2)) ≤
        2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    calc
      (∑' j : ℕ, term (j + 2))
          ≤ ∑' j : ℕ, 2 * r ^ (j + 2) := htailTsum
      _ = 2 * r ^ 2 / (1 - r) := hmajorTsum
      _ = 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        dsimp [r]
        have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hpR
        have hp1 : (p : ℝ) - 1 ≠ 0 :=
          ne_of_gt (sub_pos.mpr (lt_of_lt_of_le one_lt_two hpTwo))
        field_simp [hp0, hp1]
  linarith

/-- The prime sum appearing in the exponential Euler-product majorant for
the GS Möbius coefficient. -/
noncomputable def gsEulerExponent (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ (N + 1).primesBelow,
    (‖f p - 1‖ / (p : ℝ) + 2 / ((p : ℝ) * ((p : ℝ) - 1)))

theorem gsEulerExponent_nonneg (f : ℕ → ℂ) (N : ℕ) :
    0 ≤ gsEulerExponent f N := by
  unfold gsEulerExponent
  refine Finset.sum_nonneg fun p hp => add_nonneg
    (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) ?_
  have hpPrime := Nat.prime_of_mem_primesBelow hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  positivity

/-- The finite Euler product in Halberstam--Richert is at most the
exponential of the GS discrepancy prime sum plus the summable `p⁻²` tail. -/
theorem gsMoebiusNorm_eulerProduct_le_exp
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, gsMoebiusNorm f (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      Real.exp (gsEulerExponent f N) := by
  let E : ℕ → ℝ := fun p =>
    ‖f p - 1‖ / (p : ℝ) + 2 / ((p : ℝ) * ((p : ℝ) - 1))
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, gsMoebiusNorm f (p ^ j) / ((p ^ j : ℕ) : ℝ))
        ≤ ∏ p ∈ (N + 1).primesBelow, (1 + E p) := by
          apply Finset.prod_le_prod
          · intro p hp
            exact tsum_nonneg fun j =>
              div_nonneg (gsMoebiusNorm_nonneg f _) (Nat.cast_nonneg _)
          · intro p hp
            have hlocal := gsMoebiusNorm_localFactor_le hmul hone
              (Nat.prime_of_mem_primesBelow hp)
            dsimp [E]
            linarith
    _ ≤ Real.exp (∑ p ∈ (N + 1).primesBelow, E p) := by
      apply Real.prod_one_add_le_exp_sum
      intro p
      dsimp [E]
      by_cases hp0 : p = 0
      · subst p
        simp
      by_cases hp1 : p = 1
      · subst p
        simp
      have hp2 : 2 ≤ p := by omega
      have hp1R : (1 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hp2)
      exact add_nonneg (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (by positivity)
    _ = Real.exp (gsEulerExponent f N) := by rfl

/-- Explicit Halberstam--Richert control of the GS Möbius coefficient.
All hypotheses are structural hypotheses on `f`; there is no mean-value or
desired-bound premise. -/
theorem gsMoebiusNorm_partialSum_le
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) :
    HalberstamScratch.partialSum (gsMoebiusNorm f) N ≤
      (HalberstamScratch.explicitMassConstant 2 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, gsMoebiusNorm f (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply HalberstamComplete448.halberstam_richert_explicit
      (gsMoebiusNorm f) (gsMoebiusNorm_zero f)
      (gsMoebiusNorm_one hmul) (gsMoebiusNorm_mul hmul)
      (gsMoebiusNorm_nonneg f) 2 1 (by norm_num) (by norm_num)
      (by norm_num) ?_ N hN
  intro p hp j
  simpa using gsMoebiusNorm_prime_pow_succ_le_two hone hp

/-- The Halberstam--Richert estimate in the exponential form used in the
proof of GS Lemma 7.1. -/
theorem gsMoebiusNorm_partialSum_le_exp
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hone : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) :
    HalberstamScratch.partialSum (gsMoebiusNorm f) N ≤
      (HalberstamScratch.explicitMassConstant 2 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) * Real.exp (gsEulerExponent f N) := by
  have hbase := gsMoebiusNorm_partialSum_le hmul hone N hN
  have heuler := gsMoebiusNorm_eulerProduct_le_exp hmul hone N
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hfactor : 0 ≤
      (HalberstamScratch.explicitMassConstant 2 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
          zero_le_one)
        (Nat.cast_nonneg _))
      hlog.le
  exact hbase.trans (mul_le_mul_of_nonneg_left heuler hfactor)

end Erdos67
