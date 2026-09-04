/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AdelicMinkowski

/-!
# Simultaneous approximation in `ℤ[1/6]`

This file proves the elementary simultaneous-approximation lemma used in the
rational, three-place specialization of Evertse's basis lemma.  Given one
target at the real place and one target at each of the `2`- and `3`-adic
places, it constructs a single element of `ℤ[1/6]` which is within `1/2` at
the real place and within the unit ball at both finite places.

The construction first takes the `2`-primary and `3`-primary fractional parts
of the two finite-place targets.  The resulting sum has the required finite
approximations.  Adding a nearest integer then gives the real approximation
without changing either finite-place bound.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators

namespace SIntegerApproximation

open Erdos407.AdelicMinkowski

/-- The one-coordinate presentation of an element of `ℤ[1/6]`. -/
def InZOneSixScalar (q : ℚ) : Prop :=
  InZOneSix (fun _ : Fin 1 ↦ q)

theorem inZOneSixScalar_iff (q : ℚ) :
    InZOneSixScalar q ↔ ∃ k : ℕ, ∃ z : ℤ, q = (z : ℚ) / denominator k := by
  constructor
  · rintro ⟨k, z, hz⟩
    exact ⟨k, z 0, hz 0⟩
  · rintro ⟨k, z, hz⟩
    refine ⟨k, fun _ ↦ z, fun i ↦ ?_⟩
    simpa [InZOneSixScalar] using hz

theorem InZOneSixScalar.zero : InZOneSixScalar 0 := by
  rw [inZOneSixScalar_iff]
  exact ⟨0, 0, by simp [denominator]⟩

theorem InZOneSixScalar.neg {q : ℚ} (hq : InZOneSixScalar q) :
    InZOneSixScalar (-q) := by
  unfold InZOneSixScalar at hq ⊢
  convert AdelicMinkowski.InZOneSix.neg hq using 1
  funext i
  rfl

theorem InZOneSixScalar.add {q r : ℚ}
    (hq : InZOneSixScalar q) (hr : InZOneSixScalar r) :
    InZOneSixScalar (q + r) := by
  unfold InZOneSixScalar at hq hr ⊢
  convert AdelicMinkowski.InZOneSix.add hq hr using 1
  funext i
  rfl

theorem InZOneSixScalar.intCast (z : ℤ) : InZOneSixScalar (z : ℚ) := by
  rw [inZOneSixScalar_iff]
  exact ⟨0, z, by simp [denominator]⟩

theorem InZOneSixScalar.mul {q r : ℚ}
    (hq : InZOneSixScalar q) (hr : InZOneSixScalar r) :
    InZOneSixScalar (q * r) := by
  obtain ⟨k, z, hz⟩ := hq
  obtain ⟨l, w, hw⟩ := hr
  refine ⟨k + l, ⟨fun _ ↦ z 0 * w 0, fun i ↦ ?_⟩⟩
  fin_cases i
  change q * r = ((z 0 * w 0 : ℤ) : ℚ) / denominator (k + l)
  have hzq : q = (z 0 : ℚ) / denominator k := by simpa using hz 0
  have hwr : r = (w 0 : ℚ) / denominator l := by simpa using hw 0
  rw [hzq, hwr]
  simp only [denominator, pow_add, Int.cast_mul, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  ring

/-- Multiplying an `S`-integer vector by an `S`-integer scalar preserves
membership in `ℤ[1/6]^n`. -/
theorem InZOneSixScalar.smul {n : ℕ} {q : ℚ} {x : Fin n → ℚ}
    (hq : InZOneSixScalar q) (hx : InZOneSix x) :
    InZOneSix (q • x) := by
  obtain ⟨k, z, hz⟩ := hq
  obtain ⟨l, w, hw⟩ := hx
  refine ⟨k + l, ⟨fun i ↦ z 0 * w i, fun i ↦ ?_⟩⟩
  simp only [Pi.smul_apply, smul_eq_mul, hz 0, hw i, denominator, pow_add,
    Int.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The denominator left after removing its full `p`-primary part. -/
def primeFreeDenominator (p : ℕ) (q : ℚ) : ℕ :=
  q.den / p ^ padicValNat p q.den

theorem prime_pow_mul_primeFreeDenominator (p : ℕ) [Fact p.Prime]
    (q : ℚ) :
    p ^ padicValNat p q.den * primeFreeDenominator p q = q.den := by
  exact Nat.mul_div_cancel' pow_padicValNat_dvd

theorem prime_not_dvd_primeFreeDenominator (p : ℕ) [Fact p.Prime]
    (q : ℚ) : ¬ p ∣ primeFreeDenominator p q := by
  intro hp
  have hdvd : p ^ (padicValNat p q.den + 1) ∣ q.den := by
    rw [pow_succ]
    calc
      p ^ padicValNat p q.den * p ∣
          p ^ padicValNat p q.den * primeFreeDenominator p q :=
        Nat.mul_dvd_mul_left _ hp
      _ = q.den := prime_pow_mul_primeFreeDenominator p q
  exact (pow_succ_padicValNat_not_dvd (p := p) q.den_ne_zero) hdvd

/-- An integral inverse of the prime-free denominator modulo the removed
prime power. -/
def primaryInverse (p : ℕ) (q : ℚ) : ℤ :=
  Nat.gcdA (primeFreeDenominator p q) (p ^ padicValNat p q.den)

theorem primary_bezout (p : ℕ) [Fact p.Prime] (q : ℚ) :
    (primeFreeDenominator p q : ℤ) * primaryInverse p q +
        (p ^ padicValNat p q.den : ℕ) *
          Nat.gcdB (primeFreeDenominator p q)
            (p ^ padicValNat p q.den) = 1 := by
  have hcop : Nat.Coprime (primeFreeDenominator p q)
      (p ^ padicValNat p q.den) := by
    exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd
      (prime_not_dvd_primeFreeDenominator p q)
  simpa [primaryInverse, hcop.gcd_eq_one] using
    (Nat.gcd_eq_gcd_ab (primeFreeDenominator p q)
      (p ^ padicValNat p q.den)).symm

/-- The `p`-primary fractional part of a rational number. -/
def primaryFraction (p : ℕ) (q : ℚ) : ℚ :=
  ((q.num * primaryInverse p q : ℤ) : ℚ) /
    (p ^ padicValNat p q.den : ℕ)

private theorem bezout_fraction_sub
    (num u w : ℤ) (s e : ℕ) (hs : s ≠ 0) (he : e ≠ 0)
    (hb : (e : ℤ) * u + (s : ℤ) * w = 1) :
    (((num * u : ℤ) : ℚ) / s -
        (num : ℚ) / (s * e : ℕ)) =
      ((-(num * w) : ℤ) : ℚ) / e := by
  have hbq : (e : ℚ) * (u : ℚ) + (s : ℚ) * (w : ℚ) = 1 := by
    exact_mod_cast hb
  have hrewrite : (e : ℚ) * (u : ℚ) - 1 = -(s : ℚ) * (w : ℚ) := by
    linarith
  calc
    (((num * u : ℤ) : ℚ) / s - (num : ℚ) / (s * e : ℕ)) =
        (num : ℚ) *
          (((e : ℚ) * (u : ℚ) - 1) / ((s : ℚ) * (e : ℚ))) := by
      push_cast
      field_simp
    _ = (num : ℚ) *
          ((-(s : ℚ) * (w : ℚ)) / ((s : ℚ) * (e : ℚ))) := by
      rw [hrewrite]
    _ = ((-(num * w) : ℤ) : ℚ) / e := by
      push_cast
      field_simp

theorem primaryFraction_sub_eq (p : ℕ) [Fact p.Prime] (q : ℚ) :
    primaryFraction p q - q =
      ((-(q.num * Nat.gcdB (primeFreeDenominator p q)
          (p ^ padicValNat p q.den)) : ℤ) : ℚ) /
        primeFreeDenominator p q := by
  have hp0 : (p ^ padicValNat p q.den : ℕ) ≠ 0 := by
    exact pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero
  have he0 : primeFreeDenominator p q ≠ 0 := by
    intro he
    have h := prime_pow_mul_primeFreeDenominator p q
    rw [he, mul_zero] at h
    exact q.den_ne_zero h.symm
  rw [primaryFraction]
  calc
    ((q.num * primaryInverse p q : ℤ) : ℚ) /
          (p ^ padicValNat p q.den : ℕ) - q =
        ((q.num * primaryInverse p q : ℤ) : ℚ) /
          (p ^ padicValNat p q.den : ℕ) -
            (q.num : ℚ) / q.den := by
      congr 1
      exact q.num_div_den.symm
    _ = ((q.num * primaryInverse p q : ℤ) : ℚ) /
          (p ^ padicValNat p q.den : ℕ) -
            (q.num : ℚ) /
              ((p ^ padicValNat p q.den) * primeFreeDenominator p q : ℕ) := by
      rw [prime_pow_mul_primeFreeDenominator p q]
    _ = ((-(q.num * Nat.gcdB (primeFreeDenominator p q)
          (p ^ padicValNat p q.den)) : ℤ) : ℚ) /
        primeFreeDenominator p q := by
      exact bezout_fraction_sub q.num (primaryInverse p q)
        (Nat.gcdB (primeFreeDenominator p q)
          (p ^ padicValNat p q.den))
        (p ^ padicValNat p q.den) (primeFreeDenominator p q)
        hp0 he0 (primary_bezout p q)

theorem padicNorm_primaryFraction_sub_le_one (p : ℕ) [Fact p.Prime]
    (q : ℚ) : padicNorm p (primaryFraction p q - q) ≤ 1 := by
  rw [primaryFraction_sub_eq, padicNorm.div]
  have hden : padicNorm p (primeFreeDenominator p q : ℚ) = 1 := by
    exact (padicNorm.nat_eq_one_iff _).mpr
      (prime_not_dvd_primeFreeDenominator p q)
  rw [hden, div_one]
  exact padicNorm.of_int _

theorem primaryFraction_inZOneSix_two (q : ℚ) :
    InZOneSixScalar (primaryFraction 2 q) := by
  rw [inZOneSixScalar_iff]
  let k := padicValNat 2 q.den
  refine ⟨k, (q.num * primaryInverse 2 q) * (3 : ℤ) ^ k, ?_⟩
  simp only [primaryFraction, denominator, k, Nat.cast_pow, Nat.cast_ofNat,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [show (6 : ℚ) ^ padicValNat 2 q.den =
      (3 : ℚ) ^ padicValNat 2 q.den *
        (2 : ℚ) ^ padicValNat 2 q.den by
    rw [← mul_pow]
    norm_num]
  field_simp

theorem primaryFraction_inZOneSix_three (q : ℚ) :
    InZOneSixScalar (primaryFraction 3 q) := by
  rw [inZOneSixScalar_iff]
  let k := padicValNat 3 q.den
  refine ⟨k, (q.num * primaryInverse 3 q) * (2 : ℤ) ^ k, ?_⟩
  simp only [primaryFraction, denominator, k, Nat.cast_pow, Nat.cast_ofNat,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [show (6 : ℚ) ^ padicValNat 3 q.den =
      (2 : ℚ) ^ padicValNat 3 q.den *
        (3 : ℚ) ^ padicValNat 3 q.den by
    rw [← mul_pow]
    norm_num]
  field_simp

/-- The sum of the two primary fractions, before the final real-place
translation. -/
def finitePlaceApproximation (q₂ q₃ : ℚ) : ℚ :=
  primaryFraction 2 q₂ + primaryFraction 3 q₃

theorem finitePlaceApproximation_mem (q₂ q₃ : ℚ) :
    InZOneSixScalar (finitePlaceApproximation q₂ q₃) :=
  (primaryFraction_inZOneSix_two q₂).add
    (primaryFraction_inZOneSix_three q₃)

theorem padicNorm_three_primaryFraction_two_le_one (q : ℚ) :
    padicNorm 3 (primaryFraction 2 q) ≤ 1 := by
  rw [primaryFraction, padicNorm.div]
  have hcop : Nat.Coprime 3 (2 ^ padicValNat 2 q.den) :=
    (by norm_num : Nat.Coprime 3 2).pow_right _
  have hden : padicNorm 3 ((2 ^ padicValNat 2 q.den : ℕ) : ℚ) = 1 := by
    exact (padicNorm.nat_eq_one_iff _).mpr
      ((Nat.prime_three.coprime_iff_not_dvd).mp hcop)
  rw [hden, div_one]
  exact padicNorm.of_int _

theorem padicNorm_two_primaryFraction_three_le_one (q : ℚ) :
    padicNorm 2 (primaryFraction 3 q) ≤ 1 := by
  rw [primaryFraction, padicNorm.div]
  have hcop : Nat.Coprime 2 (3 ^ padicValNat 3 q.den) :=
    (by norm_num : Nat.Coprime 2 3).pow_right _
  have hden : padicNorm 2 ((3 ^ padicValNat 3 q.den : ℕ) : ℚ) = 1 := by
    exact (padicNorm.nat_eq_one_iff _).mpr
      ((Nat.prime_two.coprime_iff_not_dvd).mp hcop)
  rw [hden, div_one]
  exact padicNorm.of_int _

theorem finitePlaceApproximation_two (q₂ q₃ : ℚ) :
    padicNorm 2 (finitePlaceApproximation q₂ q₃ - q₂) ≤ 1 := by
  have h1 := padicNorm_primaryFraction_sub_le_one 2 q₂
  have h2 := padicNorm_two_primaryFraction_three_le_one q₃
  calc
    padicNorm 2 (finitePlaceApproximation q₂ q₃ - q₂) =
        padicNorm 2 ((primaryFraction 2 q₂ - q₂) +
          primaryFraction 3 q₃) := by
      congr 1
      simp only [finitePlaceApproximation]
      ring
    _ ≤ max (padicNorm 2 (primaryFraction 2 q₂ - q₂))
          (padicNorm 2 (primaryFraction 3 q₃)) := padicNorm.nonarchimedean
    _ ≤ 1 := max_le h1 h2

theorem finitePlaceApproximation_three (q₂ q₃ : ℚ) :
    padicNorm 3 (finitePlaceApproximation q₂ q₃ - q₃) ≤ 1 := by
  have h1 := padicNorm_primaryFraction_sub_le_one 3 q₃
  have h2 := padicNorm_three_primaryFraction_two_le_one q₂
  calc
    padicNorm 3 (finitePlaceApproximation q₂ q₃ - q₃) =
        padicNorm 3 (primaryFraction 2 q₂ +
          (primaryFraction 3 q₃ - q₃)) := by
      congr 1
      simp only [finitePlaceApproximation]
      ring
    _ ≤ max (padicNorm 3 (primaryFraction 2 q₂))
          (padicNorm 3 (primaryFraction 3 q₃ - q₃)) :=
      padicNorm.nonarchimedean
    _ ≤ 1 := max_le h2 h1

/-- The nearest-integer choice obtained by flooring `q + 1/2`. -/
noncomputable def nearestInteger (q : ℚ) : ℤ :=
  ⌊(q : ℝ) + 1 / 2⌋

theorem abs_nearestInteger_sub_le_half (q : ℚ) :
    |((nearestInteger q : ℤ) : ℝ) - (q : ℝ)| ≤ 1 / 2 := by
  have hlo := Int.floor_le ((q : ℝ) + 1 / 2)
  have hhi := Int.lt_floor_add_one ((q : ℝ) + 1 / 2)
  rw [abs_le]
  constructor <;> dsimp [nearestInteger] at * <;> linarith

/-- The simultaneous approximant: first correct the two finite places, then
translate by a nearest integer at the real place. -/
noncomputable def simultaneousApproximation (qInf q₂ q₃ : ℚ) : ℚ :=
  finitePlaceApproximation q₂ q₃ +
    nearestInteger (qInf - finitePlaceApproximation q₂ q₃)

theorem simultaneousApproximation_mem (qInf q₂ q₃ : ℚ) :
    InZOneSixScalar (simultaneousApproximation qInf q₂ q₃) := by
  exact (finitePlaceApproximation_mem q₂ q₃).add
    (InZOneSixScalar.intCast _)

theorem simultaneousApproximation_real (qInf q₂ q₃ : ℚ) :
    abs (((simultaneousApproximation qInf q₂ q₃ - qInf : ℚ) : ℝ)) ≤ 1 / 2 := by
  have h := abs_nearestInteger_sub_le_half
    (qInf - finitePlaceApproximation q₂ q₃)
  push_cast at h
  rw [simultaneousApproximation]
  push_cast
  convert h using 1
  ring_nf

theorem simultaneousApproximation_two (qInf q₂ q₃ : ℚ) :
    padicNorm 2 (simultaneousApproximation qInf q₂ q₃ - q₂) ≤ 1 := by
  calc
    padicNorm 2 (simultaneousApproximation qInf q₂ q₃ - q₂) =
        padicNorm 2 ((finitePlaceApproximation q₂ q₃ - q₂) +
          nearestInteger (qInf - finitePlaceApproximation q₂ q₃)) := by
      congr 1
      simp only [simultaneousApproximation]
      ring
    _ ≤ max (padicNorm 2 (finitePlaceApproximation q₂ q₃ - q₂))
          (padicNorm 2 (nearestInteger
            (qInf - finitePlaceApproximation q₂ q₃) : ℚ)) :=
      padicNorm.nonarchimedean
    _ ≤ 1 := max_le (finitePlaceApproximation_two q₂ q₃) (padicNorm.of_int _)

theorem simultaneousApproximation_three (qInf q₂ q₃ : ℚ) :
    padicNorm 3 (simultaneousApproximation qInf q₂ q₃ - q₃) ≤ 1 := by
  calc
    padicNorm 3 (simultaneousApproximation qInf q₂ q₃ - q₃) =
        padicNorm 3 ((finitePlaceApproximation q₂ q₃ - q₃) +
          nearestInteger (qInf - finitePlaceApproximation q₂ q₃)) := by
      congr 1
      simp only [simultaneousApproximation]
      ring
    _ ≤ max (padicNorm 3 (finitePlaceApproximation q₂ q₃ - q₃))
          (padicNorm 3 (nearestInteger
            (qInf - finitePlaceApproximation q₂ q₃) : ℚ)) :=
      padicNorm.nonarchimedean
    _ ≤ 1 := max_le (finitePlaceApproximation_three q₂ q₃) (padicNorm.of_int _)

/-- Simultaneous weak approximation by an `S`-integer for
`S = {∞, 2, 3}`. -/
theorem exists_inZOneSix_approximation (qInf q₂ q₃ : ℚ) :
    ∃ a : ℚ,
      InZOneSixScalar a ∧
      abs (((a - qInf : ℚ) : ℝ)) ≤ 1 / 2 ∧
      padicNorm 2 (a - q₂) ≤ 1 ∧
      padicNorm 3 (a - q₃) ≤ 1 := by
  exact ⟨simultaneousApproximation qInf q₂ q₃,
    simultaneousApproximation_mem qInf q₂ q₃,
    simultaneousApproximation_real qInf q₂ q₃,
    simultaneousApproximation_two qInf q₂ q₃,
    simultaneousApproximation_three qInf q₂ q₃⟩

end SIntegerApproximation

end Erdos407.PadicSubspace
