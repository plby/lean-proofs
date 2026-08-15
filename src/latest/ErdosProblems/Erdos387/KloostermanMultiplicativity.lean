/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BezoutAdditiveCharacter
import ErdosProblems.Erdos387.CompositeKloostermanCompletion

/-!
# Chinese-remainder multiplicativity of complete Kloosterman sums

The complete composite-modulus estimate in BNPZ Lemma 8.2 is assembled from
local prime-power estimates.  This file verifies its exact CRT algebra,
including the inverse map and the twists imposed by the standard additive
character convention.
-/

namespace Erdos387

open scoped BigOperators

namespace Kloosterman

/-- The canonical Bézout coefficient `gcdA m n` is a unit modulo `n`
when `m` and `n` are coprime. -/
theorem isUnit_gcdA
    (m n : ℕ) [NeZero n] (hcop : Nat.Coprime m n) :
    IsUnit (Nat.gcdA m n : ZMod n) := by
  have hbez : (1 : ℤ) =
      (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n := by
    simpa [hcop.gcd_eq_one] using Nat.gcd_eq_gcd_ab m n
  have hmul :
      ((m : ℤ) : ZMod n) * ((Nat.gcdA m n : ℤ) : ZMod n) = 1 := by
    calc
      ((m : ℤ) : ZMod n) * ((Nat.gcdA m n : ℤ) : ZMod n) =
          (((m : ℤ) * Nat.gcdA m n +
            (n : ℤ) * Nat.gcdB m n : ℤ) : ZMod n) := by
        push_cast
        simp
      _ = 1 := by rw [← hbez]; simp
  exact IsUnit.of_mul_eq_one (((m : ℤ) : ZMod n)) (by
    simpa [mul_comm] using hmul)

/-- The canonical Bézout coefficient `gcdB m n` is a unit modulo `m`
when `m` and `n` are coprime. -/
theorem isUnit_gcdB
    (m n : ℕ) [NeZero m] (hcop : Nat.Coprime m n) :
    IsUnit (Nat.gcdB m n : ZMod m) := by
  have hbez : (1 : ℤ) =
      (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n := by
    simpa [hcop.gcd_eq_one] using Nat.gcd_eq_gcd_ab m n
  have hmul :
      ((n : ℤ) : ZMod m) * ((Nat.gcdB m n : ℤ) : ZMod m) = 1 := by
    calc
      ((n : ℤ) : ZMod m) * ((Nat.gcdB m n : ℤ) : ZMod m) =
          (((m : ℤ) * Nat.gcdA m n +
            (n : ℤ) * Nat.gcdB m n : ℤ) : ZMod m) := by
        push_cast
        simp [add_comm]
      _ = 1 := by rw [← hbez]; simp
  exact IsUnit.of_mul_eq_one (((n : ℤ) : ZMod m)) (by
    simpa [mul_comm] using hmul)

theorem chineseRemainder_inv_of_isUnit
    {m n : ℕ} (hcop : Nat.Coprime m n) (x : ZMod (m * n))
    (hx : IsUnit x) :
    ZMod.chineseRemainder hcop x⁻¹ =
      ((ZMod.chineseRemainder hcop x).1⁻¹,
        (ZMod.chineseRemainder hcop x).2⁻¹) := by
  let e := ZMod.chineseRemainder hcop
  have hmul : e x * e x⁻¹ = 1 := by
    rw [← e.map_mul]
    simpa using congrArg e (ZMod.mul_inv_of_unit x hx)
  apply Prod.ext
  · have hfst : (e x).1 * (e x⁻¹).1 = 1 := by
      exact congrArg Prod.fst hmul
    exact (ZMod.inv_eq_of_mul_eq_one m (e x).1 (e x⁻¹).1 hfst).symm
  · have hsnd : (e x).2 * (e x⁻¹).2 = 1 := by
      exact congrArg Prod.snd hmul
    exact (ZMod.inv_eq_of_mul_eq_one n (e x).2 (e x⁻¹).2 hsnd).symm

/-- One zero-extended complete Kloosterman integrand factors into its two
CRT-coordinate integrands. -/
theorem completeIntegrand_product
    (m n : ℕ) [NeZero m] [NeZero n] (hcop : Nat.Coprime m n)
    (a b x : ZMod (m * n)) :
    (if IsUnit x then ZMod.stdAddChar (a * x + b * x⁻¹) else 0) =
      (if IsUnit (ZMod.chineseRemainder hcop x).2 then
        ZMod.stdAddChar
          (((ZMod.chineseRemainder hcop a).2 *
              (Nat.gcdA m n : ZMod n)) *
            (ZMod.chineseRemainder hcop x).2 +
           ((ZMod.chineseRemainder hcop b).2 *
              (Nat.gcdA m n : ZMod n)) *
            (ZMod.chineseRemainder hcop x).2⁻¹)
       else 0) *
      (if IsUnit (ZMod.chineseRemainder hcop x).1 then
        ZMod.stdAddChar
          (((ZMod.chineseRemainder hcop a).1 *
              (Nat.gcdB m n : ZMod m)) *
            (ZMod.chineseRemainder hcop x).1 +
           ((ZMod.chineseRemainder hcop b).1 *
              (Nat.gcdB m n : ZMod m)) *
            (ZMod.chineseRemainder hcop x).1⁻¹)
       else 0) := by
  let e := ZMod.chineseRemainder hcop
  by_cases hx : IsUnit x
  · have hex : IsUnit (e x) := hx.map e.toRingHom
    have hcoord : IsUnit (e x).1 ∧ IsUnit (e x).2 :=
      Prod.isUnit_iff.mp hex
    rw [if_pos hx, if_pos hcoord.2, if_pos hcoord.1]
    rw [BezoutAdditiveCharacter.stdAddChar_product_crt m n hcop]
    have hinv := chineseRemainder_inv_of_isUnit hcop x hx
    change
      ZMod.stdAddChar
          ((e (a * x + b * x⁻¹)).2 *
            (Nat.gcdA m n : ZMod n)) *
        ZMod.stdAddChar
          ((e (a * x + b * x⁻¹)).1 *
            (Nat.gcdB m n : ZMod m)) = _
    rw [e.map_add, e.map_mul, e.map_mul, hinv]
    apply congrArg₂ (· * ·)
    · congr 1
      simp only [Prod.snd_add, Prod.snd_mul]
      ring
    · congr 1
      simp only [Prod.fst_add, Prod.fst_mul]
      ring
  · rw [if_neg hx]
    by_cases hfst : IsUnit (e x).1
    · have hsnd : ¬IsUnit (e x).2 := by
        intro hsnd
        have hex : IsUnit (e x) := Prod.isUnit_iff.mpr ⟨hfst, hsnd⟩
        exact hx ((MulEquiv.isUnit_map e).mp hex)
      rw [if_neg hsnd, zero_mul]
    · rw [if_neg hfst, mul_zero]

/-- Complete Kloosterman sums are multiplicative across coprime moduli,
with the canonical additive-character twists supplied by Bézout. -/
theorem sum_product
    (m n : ℕ) [NeZero m] [NeZero n] (hcop : Nat.Coprime m n)
    (a b : ZMod (m * n)) :
    sum (m * n) a b =
      sum n
          ((ZMod.chineseRemainder hcop a).2 *
            (Nat.gcdA m n : ZMod n))
          ((ZMod.chineseRemainder hcop b).2 *
            (Nat.gcdA m n : ZMod n)) *
        sum m
          ((ZMod.chineseRemainder hcop a).1 *
            (Nat.gcdB m n : ZMod m))
          ((ZMod.chineseRemainder hcop b).1 *
            (Nat.gcdB m n : ZMod m)) := by
  let e := ZMod.chineseRemainder hcop
  let F₂ : ZMod n → ℂ := fun v =>
    if IsUnit v then
      ZMod.stdAddChar
        (((e a).2 * (Nat.gcdA m n : ZMod n)) * v +
          ((e b).2 * (Nat.gcdA m n : ZMod n)) * v⁻¹)
    else 0
  let F₁ : ZMod m → ℂ := fun u =>
    if IsUnit u then
      ZMod.stdAddChar
        (((e a).1 * (Nat.gcdB m n : ZMod m)) * u +
          ((e b).1 * (Nat.gcdB m n : ZMod m)) * u⁻¹)
    else 0
  rw [sum_eq_inverse_phase]
  calc
    (∑ x : ZMod (m * n),
        if IsUnit x then
          ZMod.stdAddChar (a * x + b * x⁻¹)
        else 0) =
      ∑ x : ZMod (m * n), F₂ (e x).2 * F₁ (e x).1 := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact completeIntegrand_product m n hcop a b x
    _ = ∑ y : ZMod m × ZMod n, F₂ y.2 * F₁ y.1 := by
      exact e.sum_comp (fun y => F₂ y.2 * F₁ y.1)
    _ = ∑ u : ZMod m, ∑ v : ZMod n, F₂ v * F₁ u := by
      rw [show (Finset.univ : Finset (ZMod m × ZMod n)) =
          (Finset.univ : Finset (ZMod m)) ×ˢ
            (Finset.univ : Finset (ZMod n)) by ext; simp]
      exact Finset.sum_product _ _ _
    _ = ∑ u : ZMod m, (∑ v : ZMod n, F₂ v) * F₁ u := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.sum_mul]
    _ = (∑ v : ZMod n, F₂ v) * ∑ u : ZMod m, F₁ u := by
      rw [Finset.mul_sum]
    _ = sum n
          ((e a).2 * (Nat.gcdA m n : ZMod n))
          ((e b).2 * (Nat.gcdA m n : ZMod n)) *
        sum m
          ((e a).1 * (Nat.gcdB m n : ZMod m))
          ((e b).1 * (Nat.gcdB m n : ZMod m)) := by
      rw [sum_eq_inverse_phase, sum_eq_inverse_phase]

end Kloosterman

end Erdos387
