/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Root congruences in a local binomial ring, for the sextic determinant method.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.BinomialApproximation

namespace Erdos477.Counting

variable {R : Type*} [CommRing R]

/-- The factor remaining after dividing a difference of sixth powers by the
difference of the bases. -/
def sixthQuotient (x y : R) : R :=
  x ^ 5 + x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + x * y ^ 4 + y ^ 5

lemma sixthQuotient_identity (x y : R) :
    (x - y) * sixthQuotient x y = x ^ 6 - y ^ 6 := by
  unfold sixthQuotient
  ring

lemma sixthQuotient_congr_one (p x y : R) (hx : p ∣ x - 1) (hy : p ∣ y - 1) :
    p ∣ sixthQuotient x y - 6 := by
  let I : Ideal R := Ideal.span {p}
  let φ := Ideal.Quotient.mk I
  have hx' : φ x = 1 := by
    have h : φ x = φ 1 := Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hx)
    simpa only [map_one] using h
  have hy' : φ y = 1 := by
    have h : φ y = φ 1 := Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hy)
    simpa only [map_one] using h
  have hz : φ (sixthQuotient x y - 6) = 0 := by
    simp only [sixthQuotient, map_sub, map_add, map_mul, map_pow, map_ofNat, hx', hy']
    norm_num
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- Changing a unit by a multiple of a nonunit preserves invertibility in a
local ring. -/
lemma isUnit_of_congr_nonunit [IsLocalRing R] (p a b : R) (hp : ¬ IsUnit p)
    (hb : IsUnit b) (h : p ∣ a - b) : IsUnit a := by
  by_contra ha
  have hpI : p ∈ IsLocalRing.maximalIdeal R := hp
  have haI : a ∈ IsLocalRing.maximalIdeal R := ha
  have hdI : a - b ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).mem_of_dvd h hpI
  have hbI : b ∈ IsLocalRing.maximalIdeal R := by
    simpa only [sub_sub_cancel] using (IsLocalRing.maximalIdeal R).sub_mem haI hdI
  exact hbI hb

lemma sixthQuotient_isUnit [IsLocalRing R] (p x y : R) (hp : ¬ IsUnit p)
    (h6 : IsUnit (6 : R)) (hx : p ∣ x - 1) (hy : p ∣ y - 1) :
    IsUnit (sixthQuotient x y) :=
  isUnit_of_congr_nonunit p _ 6 hp h6 (sixthQuotient_congr_one p x y hx hy)

lemma dvd_sub_of_dvd_sixth_sub [IsLocalRing R] (p x y : R) (hp : ¬ IsUnit p)
    (h6 : IsUnit (6 : R)) (hx : p ∣ x - 1) (hy : p ∣ y - 1) (N : ℕ)
    (hpow : p ^ N ∣ x ^ 6 - y ^ 6) : p ^ N ∣ x - y := by
  obtain ⟨u, hu⟩ := sixthQuotient_isUnit p x y hp h6 hx hy
  rw [← sixthQuotient_identity, ← hu] at hpow
  have hmul := dvd_mul_of_dvd_left hpow (↑u⁻¹ : R)
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hmul

/-- The truncated binomial series approximates the actual sixth root, not
just its sixth power, to any prescribed order in the local parameter. -/
theorem pow_dvd_rootApprox_sub_root [IsLocalRing R] [BinomialRing R]
    (a : R) (ha : 6 * a = 1) (p q z : R) (hp : ¬ IsUnit p)
    (hq : p ∣ q - 1) (hz : p ∣ z) (hroot : q ^ 6 = 1 + z) (N : ℕ) :
    p ^ N ∣ q - (rootApprox a N).eval z := by
  by_cases hN : 0 < N
  · have h6 : IsUnit (6 : R) := IsUnit.of_mul_eq_one a ha
    have hy := dvd_rootApprox_sub_one a p z hz hN
    have herr := pow_dvd_rootApprox_error a ha p z hz N
    apply dvd_sub_of_dvd_sixth_sub p q ((rootApprox a N).eval z) hp h6 hq hy N
    rw [hroot]
    simpa only [neg_sub] using (dvd_neg.mpr herr)
  · have hN0 : N = 0 := by omega
    simp only [hN0, pow_zero, one_dvd]

#print axioms pow_dvd_rootApprox_sub_root
-- 'Erdos477.Counting.pow_dvd_rootApprox_sub_root' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
