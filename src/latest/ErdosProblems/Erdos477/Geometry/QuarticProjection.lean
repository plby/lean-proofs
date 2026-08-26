/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The explicit projection and inverse when both missing coordinates have prescribed squares.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

def quarticProjection {R : Type*} [CommRing R] (h g t : R) : R :=
  t ^ 4 - 2 * (h + g) * t ^ 2 + (h - g) ^ 2

lemma quarticProjection_of_squares {R : Type*} [CommRing R]
    (u y h g : R) (hu : u ^ 2 = h) (hy : y ^ 2 = g) : quarticProjection h g (u + y) = 0 := by
  rw [← hu, ← hy]
  dsimp only [quarticProjection]
  ring

def squareSexticQuotient {R : Type*} [CommRing R] (n m h g d : R) : R :=
  n ^ 4 + n ^ 2 * h * d ^ 2 + h ^ 2 * d ^ 4 +
    m ^ 4 + m ^ 2 * g * d ^ 2 + g ^ 2 * d ^ 4

lemma square_sextic_certificate {R : Type*} [CommRing R] (n m h g d q : R)
    (hn : n ^ 2 - h * d ^ 2 = q) (hm : m ^ 2 - g * d ^ 2 = q) :
    n ^ 6 + m ^ 6 - (h ^ 3 + g ^ 3) * d ^ 6 = q * squareSexticQuotient n m h g d := by
  dsimp only [squareSexticQuotient]
  linear_combination (n ^ 4 + n ^ 2 * h * d ^ 2 + h ^ 2 * d ^ 4) * hn +
    (m ^ 4 + m ^ 2 * g * d ^ 2 + g ^ 2 * d ^ 4) * hm

theorem quartic_rational_certificate {R : Type*} [CommRing R] (h g t x k : R)
    (hsextic : h ^ 3 + g ^ 3 - x ^ 6 = k) :
    quarticProjection h g t ∣ (t ^ 2 + h - g) ^ 6 +
      (t * (2 * t) - (t ^ 2 + h - g)) ^ 6 - x ^ 6 * (2 * t) ^ 6 - k * (2 * t) ^ 6 := by
  have hn : (t ^ 2 + h - g) ^ 2 - h * (2 * t) ^ 2 = quarticProjection h g t := by
    dsimp only [quarticProjection]
    ring
  have hm : (t * (2 * t) - (t ^ 2 + h - g)) ^ 2 - g * (2 * t) ^ 2 =
      quarticProjection h g t := by dsimp only [quarticProjection]; ring
  refine ⟨squareSexticQuotient (t ^ 2 + h - g) (t * (2 * t) - (t ^ 2 + h - g)) h g (2 * t), ?_⟩
  have hcert := square_sextic_certificate _ _ _ _ _ _ hn hm
  linear_combination hcert + (2 * t) ^ 6 * hsextic

variable {K : Type*} [Field K] [CharZero K]

lemma quarticProjection_recover (u y h g : K) (hu : u ^ 2 = h) (hy : y ^ 2 = g)
    (ht : u + y ≠ 0) :
    ((u + y) ^ 2 + h - g) / (2 * (u + y)) = u ∧
      ((u + y) ^ 2 - h + g) / (2 * (u + y)) = y := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  constructor
  · apply (div_eq_iff (mul_ne_zero h2 ht)).mpr
    rw [← hu, ← hy]
    ring
  · apply (div_eq_iff (mul_ne_zero h2 ht)).mpr
    rw [← hu, ← hy]
    ring

theorem quarticProjection_lift (h g t : K) (ht : t ≠ 0) (hq : quarticProjection h g t = 0) :
    ((t ^ 2 + h - g) / (2 * t)) ^ 2 = h ∧
      ((t ^ 2 - h + g) / (2 * t)) ^ 2 = g ∧
      (t ^ 2 + h - g) / (2 * t) + (t ^ 2 - h + g) / (2 * t) = t := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  dsimp only [quarticProjection] at hq
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination hq
  · field_simp
    linear_combination hq
  · field_simp
    ring

theorem quarticProjection_sextic_lift (h g t x c : K) (ht : t ≠ 0)
    (hq : quarticProjection h g t = 0) (hsextic : h ^ 3 + g ^ 3 - x ^ 6 = c) :
    ((t ^ 2 + h - g) / (2 * t)) ^ 6 +
      ((t ^ 2 - h + g) / (2 * t)) ^ 6 - x ^ 6 = c := by
  have hsquares := quarticProjection_lift h g t ht hq
  have hu : ((t ^ 2 + h - g) / (2 * t)) ^ 6 = h ^ 3 := by
    rw [show 6 = 2 * 3 from rfl, pow_mul, hsquares.1]
  have hy : ((t ^ 2 - h + g) / (2 * t)) ^ 6 = g ^ 3 := by
    rw [show 6 = 2 * 3 from rfl, pow_mul, hsquares.2.1]
  rwa [hu, hy]

#print axioms quarticProjection_sextic_lift
-- 'Erdos477.Geometry.quarticProjection_sextic_lift' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms quartic_rational_certificate
-- 'Erdos477.Geometry.quartic_rational_certificate' depends on axioms:
-- [propext, Quot.sound]

end Erdos477.Geometry
