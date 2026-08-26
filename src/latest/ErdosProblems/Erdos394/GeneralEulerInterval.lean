import ErdosProblems.Erdos394.GeneralEulerPower
import ErdosProblems.Erdos394.PrimeEuler

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sharp Euler comparisons on a moving prime interval
-/

open Nat Finset

namespace Erdos394

/-- If the Euler density up to the lower endpoint has any positive lower
bound `C`, F-080 gives a sharp upper bound for the density on `(z,y]`. -/
theorem primeInterval_euler_le_inv_mul_log
    {z y : ℕ} (hz : 0 < z) (hzy : z ≤ y) {C : ℝ} (hC : 0 < C)
    (hlower : C ≤ localEulerProduct z.primesLE (fun p ↦ 1 / (p : ℝ))) :
    localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ)) ≤
      1 / (C * Real.log (y + 1 : ℕ)) := by
  have hy : 0 < y := hz.trans_le hzy
  have hsub : z.primesLE ⊆ y.primesLE := Nat.primesLE_mono hzy
  have hsplit := localEulerProduct_mul_sdiff
    y.primesLE z.primesLE hsub (fun p ↦ 1 / (p : ℝ))
  have hinterval : y.primesLE \ z.primesLE = primeInterval z y := rfl
  rw [hinterval] at hsplit
  have hyEuler := primeEuler_le_inv_log_add_one hy
  have hlogpos : 0 < Real.log (y + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y + 1 by omega))
  have hVint0 : 0 ≤ localEulerProduct (primeInterval z y)
      (fun p ↦ 1 / (p : ℝ)) := by
    apply localEulerProduct_nonneg
    · intro p hp; positivity
    · intro p hp
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      exact (div_le_one hp0).2 (by exact_mod_cast hpprime.one_le)
  have hmul : C * localEulerProduct (primeInterval z y)
      (fun p ↦ 1 / (p : ℝ)) ≤ 1 / Real.log (y + 1 : ℕ) := by
    calc
      C * localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ)) ≤
        localEulerProduct z.primesLE (fun p ↦ 1 / (p : ℝ)) *
          localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hlower hVint0
      _ = localEulerProduct y.primesLE (fun p ↦ 1 / (p : ℝ)) := hsplit
      _ ≤ 1 / Real.log (y + 1 : ℕ) := hyEuler
  rw [le_div_iff₀ (mul_pos hC hlogpos)]
  calc
    localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ)) *
        (C * Real.log (y + 1 : ℕ)) =
      (C * localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ))) *
        Real.log (y + 1 : ℕ) := by ring
    _ ≤ (1 / Real.log (y + 1 : ℕ)) * Real.log (y + 1 : ℕ) :=
      mul_le_mul_of_nonneg_right hmul hlogpos.le
    _ = 1 := by field_simp

/-- Powered sharp numerator decay on `(z,y]`. -/
theorem primeInterval_combinedEuler_pow_le
    (K : ℕ) (hK : 0 < K) {z y : ℕ} (hz : 0 < z) (hzy : z ≤ y)
    {C : ℝ} (hC : 0 < C)
    (hlower : C ≤ localEulerProduct z.primesLE (fun p ↦ 1 / (p : ℝ))) :
    (localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ)) *
      ∏ p ∈ primeInterval z y, (1 + (1 / (p : ℝ)) / (K : ℝ))) ^ K ≤
      (1 / (C * Real.log (y + 1 : ℕ))) ^ (K - 1) := by
  have hbase := combinedEulerProduct_pow_le K hK (primeInterval z y)
    (fun p ↦ 1 / (p : ℝ)) (fun p hp ↦ by positivity) (fun p hp ↦ by
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      exact (div_le_one hp0).2 (by exact_mod_cast hpprime.one_le))
  apply hbase.trans
  apply pow_le_pow_left₀
  · apply localEulerProduct_nonneg
    · intro p hp; positivity
    · intro p hp
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      exact (div_le_one hp0).2 (by exact_mod_cast hpprime.one_le)
  · exact primeInterval_euler_le_inv_mul_log hz hzy hC hlower

/-- Powered denominator growth on `(z,y]`, with exponent `2/(2K+1)`. -/
theorem one_le_primeInterval_denominatorEuler_bound
    (K : ℕ) (hK : 0 < K) {z y : ℕ}
    (hzlarge : 2 * (2 * K + 1) ≤ z) (hzy : z ≤ y)
    {C : ℝ} (hC : 0 < C)
    (hlower : C ≤ localEulerProduct z.primesLE (fun p ↦ 1 / (p : ℝ))) :
    1 ≤ (1 / (C * Real.log (y + 1 : ℕ))) ^ 2 *
      (∏ p ∈ primeInterval z y,
        (1 + (1 / (p : ℝ)) / (K : ℝ))) ^ (2 * K + 1) := by
  have hz : 0 < z := by omega
  let V := localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ))
  let E := ∏ p ∈ primeInterval z y, (1 + (1 / (p : ℝ)) / (K : ℝ))
  have hlocal := one_le_denominatorEulerProduct K hK (primeInterval z y)
    (fun p ↦ 1 / (p : ℝ)) (fun p hp ↦ by positivity) (fun p hp ↦ by
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
      have hpz : z < p := by
        exact lt_of_not_ge (fun h ↦ (Finset.mem_sdiff.mp hp).2
          (Nat.mem_primesLE.mpr ⟨h, hpprime⟩))
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      rw [show 2 * (2 * K + 1 : ℕ) * (1 / (p : ℝ)) =
          ((2 * (2 * K + 1 : ℕ) : ℕ) : ℝ) / p by push_cast; ring]
      exact (div_le_one hpR).2 (by exact_mod_cast hzlarge.trans hpz.le))
  have hVle : V ≤ 1 / (C * Real.log (y + 1 : ℕ)) := by
    dsimp [V]
    exact primeInterval_euler_le_inv_mul_log hz hzy hC hlower
  have hV0 : 0 ≤ V := by
    dsimp [V]
    apply localEulerProduct_nonneg
    · intro p hp; positivity
    · intro p hp
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      exact (div_le_one hp0).2 (by exact_mod_cast hpprime.one_le)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hpowV : V ^ 2 ≤ (1 / (C * Real.log (y + 1 : ℕ))) ^ 2 :=
    pow_le_pow_left₀ hV0 hVle 2
  exact hlocal.trans (mul_le_mul_of_nonneg_right hpowV (pow_nonneg hE0 _))

end Erdos394
