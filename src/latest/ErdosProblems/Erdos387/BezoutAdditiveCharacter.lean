/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AdditiveCharacterOrthogonality
import Mathlib.Data.Int.GCD

/-!
# Bézout reciprocity for standard additive characters

This is the exact character-valued form of BNPZ Lemma 8.3.  It splits a
phase of coprime product conductor into the two reciprocal phases needed
after Chinese-remainder elimination.
-/

namespace Erdos387

namespace BezoutAdditiveCharacter

/-- If `q₁` and `q₂` are coprime, their standard product-modulus
character splits using the canonical Bézout coefficients.  The coefficient
`gcdA q₁ q₂` is an inverse of `q₁` modulo `q₂`, and `gcdB q₁ q₂`
is an inverse of `q₂` modulo `q₁`. -/
theorem stdAddChar_product
    (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (hcop : Nat.Coprime q₁ q₂) (a : ℤ) :
    ZMod.stdAddChar (a : ZMod (q₁ * q₂)) =
      ZMod.stdAddChar
          ((a * Nat.gcdA q₁ q₂ : ℤ) : ZMod q₂) *
        ZMod.stdAddChar
          ((a * Nat.gcdB q₁ q₂ : ℤ) : ZMod q₁) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
    ZMod.stdAddChar_coe, ← Complex.exp_add]
  apply congrArg Complex.exp
  have hbez : (1 : ℤ) =
      (q₁ : ℤ) * Nat.gcdA q₁ q₂ +
        (q₂ : ℤ) * Nat.gcdB q₁ q₂ := by
    simpa [hcop.gcd_eq_one] using Nat.gcd_eq_gcd_ab q₁ q₂
  have hq₁ : (q₁ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q₁
  have hq₂ : (q₂ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q₂
  have hbezC : (1 : ℂ) =
      (q₁ : ℂ) * (Nat.gcdA q₁ q₂ : ℂ) +
        (q₂ : ℂ) * (Nat.gcdB q₁ q₂ : ℂ) := by
    exact_mod_cast hbez
  push_cast
  field_simp [hq₁, hq₂]
  linear_combination (a : ℂ) * hbezC

/-- Coordinate form of `stdAddChar_product`: the product-modulus character
is the product of the two CRT-coordinate characters, twisted by the
canonical inverse coefficients.  This formulation avoids choosing integer
representatives in later exponential-sum arguments. -/
theorem stdAddChar_product_crt
    (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (hcop : Nat.Coprime q₁ q₂) (x : ZMod (q₁ * q₂)) :
    ZMod.stdAddChar x =
      ZMod.stdAddChar
          ((ZMod.chineseRemainder hcop x).2 *
            (Nat.gcdA q₁ q₂ : ZMod q₂)) *
        ZMod.stdAddChar
          ((ZMod.chineseRemainder hcop x).1 *
            (Nat.gcdB q₁ q₂ : ZMod q₁)) := by
  calc
    ZMod.stdAddChar x =
        ZMod.stdAddChar ((x.val : ℤ) : ZMod (q₁ * q₂)) := by simp
    _ = ZMod.stdAddChar
          (((x.val : ℤ) * Nat.gcdA q₁ q₂ : ℤ) : ZMod q₂) *
        ZMod.stdAddChar
          (((x.val : ℤ) * Nat.gcdB q₁ q₂ : ℤ) : ZMod q₁) :=
      stdAddChar_product q₁ q₂ hcop (x.val : ℤ)
    _ = _ := by
      congr 2 <;>
        simp [ZMod.chineseRemainder, ZMod.castHom_apply]

end BezoutAdditiveCharacter

end Erdos387
