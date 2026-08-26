import ErdosProblems.Erdos394.GeneralEulerInterval

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact powered algebra for the hierarchy exponent gap
-/

open Nat Finset

namespace Erdos394

/-- Combining the sharp numerator power and denominator power gains leaves
exactly one extra power of the common Euler-density bound. -/
theorem hierarchy_euler_ratio_pow_le
    (K : ℕ) (A B E : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 < E)
    (hnum : A ^ (K + 1) ≤ B ^ K)
    (hden : 1 ≤ B ^ 2 * E ^ (2 * K + 1)) :
    (A / E) ^ ((K + 1) * (2 * K + 1)) ≤
      B ^ ((K + 1) * (2 * K + 1) + 1) := by
  let a := K + 1
  let b := 2 * K + 1
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [b]; omega
  have hEpow : 0 < E ^ b := pow_pos hE b
  have hinv : (1 / E) ^ b ≤ B ^ 2 := by
    rw [one_div_pow]
    calc
      1 / E ^ b ≤ (B ^ 2 * E ^ b) / E ^ b :=
        div_le_div_of_nonneg_right hden hEpow.le
      _ = B ^ 2 := by field_simp
  have hnum' : A ^ a ≤ B ^ K := by simpa [a] using hnum
  have hnumPow : (A ^ a) ^ b ≤ (B ^ K) ^ b := by
    exact pow_le_pow_left₀ (pow_nonneg hA a) hnum' b
  have hinvPow : ((1 / E) ^ b) ^ a ≤ (B ^ 2) ^ a := by
    exact pow_le_pow_left₀ (by positivity) hinv a
  have hmul := mul_le_mul hnumPow hinvPow (by positivity) (by positivity)
  have hinvReorder : ((E⁻¹) ^ b) ^ a = (E⁻¹) ^ (a * b) := by
    rw [← pow_mul]
    congr 1
    exact Nat.mul_comm b a
  calc
    (A / E) ^ ((K + 1) * (2 * K + 1)) =
        (A ^ a) ^ b * ((1 / E) ^ b) ^ a := by
      change (A / E) ^ (a * b) =
        (A ^ a) ^ b * ((1 / E) ^ b) ^ a
      simp only [one_div]
      rw [div_eq_mul_inv, mul_pow, pow_mul A a b, ← hinvReorder]
    _ ≤ (B ^ K) ^ b * (B ^ 2) ^ a := hmul
    _ = B ^ ((K + 1) * (2 * K + 1) + 1) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      dsimp [a, b]
      ring

/-- Prime-interval specialization: the ratio of the `(K+1)`-block numerator
Euler factor to the `K`-block denominator Euler factor has an extra powered
saving in the interval-density upper bound. -/
theorem primeInterval_hierarchy_euler_ratio_pow_le
    (K : ℕ) (hK : 0 < K) {z y : ℕ}
    (hzlarge : 2 * (2 * K + 1) ≤ z) (hzy : z ≤ y)
    {C : ℝ} (hC : 0 < C)
    (hlower : C ≤ localEulerProduct z.primesLE (fun p ↦ 1 / (p : ℝ))) :
    let V := localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ))
    let A := V * ∏ p ∈ primeInterval z y,
      (1 + (1 / (p : ℝ)) / ((K + 1 : ℕ) : ℝ))
    let E := ∏ p ∈ primeInterval z y,
      (1 + (1 / (p : ℝ)) / (K : ℝ))
    let B := 1 / (C * Real.log (y + 1 : ℕ))
    (A / E) ^ ((K + 1) * (2 * K + 1)) ≤
      B ^ ((K + 1) * (2 * K + 1) + 1) := by
  dsimp only
  let V := localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ))
  let A := V * ∏ p ∈ primeInterval z y,
    (1 + (1 / (p : ℝ)) / ((K + 1 : ℕ) : ℝ))
  let E := ∏ p ∈ primeInterval z y,
    (1 + (1 / (p : ℝ)) / (K : ℝ))
  let B := 1 / (C * Real.log (y + 1 : ℕ))
  have hz : 0 < z := by omega
  have hy : 0 < y := hz.trans_le hzy
  have hlogy : 0 < Real.log (y + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y + 1 by omega))
  have hA0 : 0 ≤ A := by
    dsimp [A, V]
    apply mul_nonneg
    · apply localEulerProduct_nonneg
      · intro p hp; positivity
      · intro p hp
        have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
        exact (div_le_one hp0).2 (by exact_mod_cast hpprime.one_le)
    · positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hEpos : 0 < E := by dsimp [E]; positivity
  have hnum : A ^ (K + 1) ≤ B ^ K := by
    dsimp [A, B, V]
    exact primeInterval_combinedEuler_pow_le (K + 1) (by omega)
      (by omega) hzy hC hlower
  have hden : 1 ≤ B ^ 2 * E ^ (2 * K + 1) := by
    dsimp [B, E]
    exact one_le_primeInterval_denominatorEuler_bound K hK
      hzlarge hzy hC hlower
  exact hierarchy_euler_ratio_pow_le K A B E hA0 hB0 hEpos hnum hden

end Erdos394
