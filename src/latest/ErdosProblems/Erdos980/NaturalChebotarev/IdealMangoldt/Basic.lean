/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# The von Mangoldt coefficient of a number field

For a number field `K`, `PrimeIdealPower K` is the type of pairs `(𝔭, m)`, where `𝔭` is a
nonzero prime ideal of `𝓞 K` and `m ≥ 1`.  The coefficient `idealMangoldt K n` is

`∑ N(𝔭)^m = n, log N(𝔭)`.

The norm fibers are finite.  Thus this is an honest finite sum, despite being presented using
the canonical, unbounded type of all prime-ideal powers.
-/

open NumberField
open scoped BigOperators nonZeroDivisors

namespace Erdos980.NaturalChebotarev.IdealMangoldt

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- A nonzero prime ideal of the ring of integers of `K`. -/
abbrev PrimeIdeal := {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}

/-- A positive power of a nonzero prime ideal. -/
def PrimeIdealPower := {x : PrimeIdeal K × ℕ // 0 < x.2}

namespace PrimeIdealPower

variable {K}

/-- The prime ideal underlying a prime-ideal power. -/
def prime (x : PrimeIdealPower K) : Ideal (𝓞 K) := x.1.1.1

/-- The positive exponent of a prime-ideal power. -/
def exponent (x : PrimeIdealPower K) : ℕ := x.1.2

/-- The ideal represented by a prime-ideal power. -/
def ideal (x : PrimeIdealPower K) : Ideal (𝓞 K) := x.prime ^ x.exponent

/-- The (absolute) norm represented by a prime-ideal power. -/
def norm (x : PrimeIdealPower K) : ℕ := Ideal.absNorm x.prime ^ x.exponent

/-- Its von Mangoldt weight. -/
def weight (x : PrimeIdealPower K) : ℝ := Real.log (Ideal.absNorm x.prime : ℝ)

theorem prime_isPrime (x : PrimeIdealPower K) : x.prime.IsPrime := x.1.1.2.1

theorem prime_ne_bot (x : PrimeIdealPower K) : x.prime ≠ ⊥ := x.1.1.2.2

theorem exponent_pos (x : PrimeIdealPower K) : 0 < x.exponent := x.2

theorem two_le_absNorm (x : PrimeIdealPower K) : 2 ≤ Ideal.absNorm x.prime := by
  have h0 : Ideal.absNorm x.prime ≠ 0 :=
    fun h ↦ x.prime_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm x.prime ≠ 1 :=
    fun h ↦ x.prime_isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem weight_pos (x : PrimeIdealPower K) : 0 < x.weight := by
  rw [weight, Real.log_pos_iff]
  exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two x.two_le_absNorm)
  positivity

theorem weight_nonneg (x : PrimeIdealPower K) : 0 ≤ x.weight := x.weight_pos.le

@[simp] theorem absNorm_ideal (x : PrimeIdealPower K) :
    Ideal.absNorm x.ideal = x.norm := by
  simp [ideal, norm]

private theorem self_le_two_pow : ∀ m : ℕ, m ≤ 2 ^ m
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ]
    have hm := self_le_two_pow m
    calc
      m + 1 ≤ 2 ^ m + 1 := Nat.add_le_add_right hm 1
      _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ m * 2 := by ring

/-- The exponent in a prime-power representation of `n` is at most `n`. -/
theorem exponent_le_norm (x : PrimeIdealPower K) : x.exponent ≤ x.norm := by
  calc
    x.exponent ≤ 2 ^ x.exponent := self_le_two_pow x.exponent
    _ ≤ Ideal.absNorm x.prime ^ x.exponent :=
      Nat.pow_le_pow_left x.two_le_absNorm x.exponent

/-- The prime norm in a prime-power representation is at most the represented norm. -/
theorem absNorm_prime_le_norm (x : PrimeIdealPower K) : Ideal.absNorm x.prime ≤ x.norm := by
  rw [norm]
  exact Nat.le_pow x.exponent_pos

end PrimeIdealPower

/-- The prime-ideal powers having norm exactly `n`. -/
def normFiber (n : ℕ) := {x : PrimeIdealPower K // x.norm = n}

/-- Every norm fiber of prime-ideal powers is finite. -/
instance normFiber_finite (n : ℕ) : Finite (normFiber K n) := by
  let f : normFiber K n →
      {𝔭 : Ideal (𝓞 K) // Ideal.absNorm 𝔭 ≤ n} × {m // m ∈ Finset.Icc 1 n} :=
    fun x ↦
      ⟨⟨x.1.prime, x.1.absNorm_prime_le_norm.trans_eq x.2⟩,
        ⟨x.1.exponent, by
          simp only [Finset.mem_Icc]
          exact ⟨x.1.exponent_pos, x.1.exponent_le_norm.trans_eq x.2⟩⟩⟩
  letI : Finite {𝔭 : Ideal (𝓞 K) // Ideal.absNorm 𝔭 ≤ n} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) n).to_subtype
  exact Finite.of_injective f fun x y h ↦ by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z ↦ z.1.1) h
    · exact congrArg (fun z ↦ z.2.1) h

noncomputable instance normFiber_fintype (n : ℕ) : Fintype (normFiber K n) :=
  Fintype.ofFinite _

/-- The ideal von Mangoldt coefficient at `n`.

It sums `log N𝔭` once for every positive exponent `m` such that `(N𝔭)^m = n`. -/
def idealMangoldt (n : ℕ) : ℝ :=
  ∑ x : normFiber K n, x.1.weight

theorem idealMangoldt_nonneg (n : ℕ) : 0 ≤ idealMangoldt K n := by
  exact Finset.sum_nonneg fun _ _ ↦ PrimeIdealPower.weight_nonneg _

/-- Pointwise nonnegativity, in the function-order form used by Tauberian theorems. -/
theorem idealMangoldt_nonnegative : 0 ≤ idealMangoldt K :=
  fun n ↦ idealMangoldt_nonneg K n

theorem idealMangoldt_pos_iff (n : ℕ) :
    0 < idealMangoldt K n ↔ Nonempty (normFiber K n) := by
  classical
  constructor
  · intro h
    by_contra hf
    haveI : IsEmpty (normFiber K n) := not_nonempty_iff.mp hf
    simpa [idealMangoldt] using h
  · rintro ⟨x⟩
    rw [idealMangoldt]
    exact Finset.sum_pos' (fun (y : normFiber K n) _ ↦ y.1.weight_nonneg)
      ⟨x, Finset.mem_univ x, x.1.weight_pos⟩

theorem idealMangoldt_ne_zero_iff (n : ℕ) :
    idealMangoldt K n ≠ 0 ↔ Nonempty (normFiber K n) := by
  rw [← idealMangoldt_pos_iff]
  exact ⟨fun h ↦ lt_of_le_of_ne (idealMangoldt_nonneg K n) (Ne.symm h), ne_of_gt⟩

theorem mem_support_iff (n : ℕ) :
    n ∈ Function.support (idealMangoldt K) ↔
      ∃ (𝔭 : Ideal (𝓞 K)) (m : ℕ),
        𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ 0 < m ∧ Ideal.absNorm 𝔭 ^ m = n := by
  rw [Function.mem_support, idealMangoldt_ne_zero_iff]
  constructor
  · rintro ⟨x⟩
    exact ⟨x.1.prime, x.1.exponent, x.1.prime_isPrime, x.1.prime_ne_bot,
      x.1.exponent_pos, x.2⟩
  · rintro ⟨𝔭, m, hp, hbot, hm, hpow⟩
    exact ⟨⟨⟨⟨⟨𝔭, hp, hbot⟩, m⟩, hm⟩, hpow⟩⟩

@[simp] theorem idealMangoldt_zero : idealMangoldt K 0 = 0 := by
  by_contra h
  obtain ⟨x⟩ := (idealMangoldt_ne_zero_iff K 0).mp h
  have hpos : 0 < x.1.norm := by
    simp only [PrimeIdealPower.norm]
    exact Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) x.1.two_le_absNorm)
  have hnorm := x.2
  omega

@[simp] theorem idealMangoldt_one : idealMangoldt K 1 = 0 := by
  by_contra h
  obtain ⟨x⟩ := (idealMangoldt_ne_zero_iff K 1).mp h
  have htwo := x.1.two_le_absNorm
  have hle := x.1.absNorm_prime_le_norm
  rw [x.2] at hle
  omega

end

end Erdos980.NaturalChebotarev.IdealMangoldt
