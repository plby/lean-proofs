import ErdosProblems.Erdos964.PrimeLogScaleError
import ErdosProblems.Erdos964.ScalarPrimeIntegrand
import ErdosProblems.Erdos964.ScalarAffinePrimeSupport

/-!
# Exact prime-support and two-piece quadrature identities
-/

namespace Erdos964

theorem scalarSmallPrimeSupport_eq_primeInterval (η : ℝ) (K t : ℕ) :
    scalarSmallPrimeSupport η K t =
      (Finset.Ioc ⌊Real.rpow (K * t : ℕ) η⌋₊ (t / (K + 1))).filter Nat.Prime := by
  classical
  ext p
  have hpow : 0 ≤ Real.rpow (K * t : ℕ) η := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simp only [scalarSmallPrimeSupport, Finset.mem_filter, Nat.mem_primesLE,
    Finset.mem_Ioc, Nat.floor_lt hpow]
  tauto

theorem scalarSmallPrimeSupport_log_lower (η : ℝ) (K t p : ℕ)
    (hη : 0 ≤ η) (hK : 1 ≤ K) (ht : 1 ≤ t)
    (hp : p ∈ scalarSmallPrimeSupport η K t) : η * Real.log t ≤ Real.log p := by
  have hspec := scalarSmallPrimeSupport_spec η K t p hp
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hKtR : (0 : ℝ) < (K * t : ℕ) := by exact_mod_cast Nat.mul_pos hK ht
  have htKt : (t : ℝ) ≤ (K * t : ℕ) := by exact_mod_cast Nat.le_mul_of_pos_left t hK
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hKtR η) hspec.2.2.le
  rw [Real.log_rpow hKtR] at hlog
  exact (mul_le_mul_of_nonneg_left (Real.log_le_log htR htKt) hη).trans hlog

theorem scalarSmallPrimeSupport_sum_eq_primeLogScaleSum (η : ℝ) (K t R : ℕ)
    (g : ℝ → ℝ) :
    (∑ p ∈ scalarSmallPrimeSupport η K t,
      (Real.log p / (p : ℝ)) * g (Real.log p / Real.log R) / Real.log R) =
      primeLogScaleSum (Real.log R) (Real.rpow (K * t : ℕ) η) (t / (K + 1) : ℕ) g := by
  rw [scalarSmallPrimeSupport_eq_primeInterval, primeLogScaleSum, Nat.floor_natCast]

theorem primeLogScaleSum_split (L x r y : ℝ) (hxr : x ≤ r) (hry : r ≤ y)
    (g : ℝ → ℝ) :
    primeLogScaleSum L x y g = primeLogScaleSum L x r g + primeLogScaleSum L r y g := by
  classical
  unfold primeLogScaleSum
  simp only [Finset.sum_filter]
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.floor_le_floor hxr) (Nat.floor_le_floor hry),
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]

theorem scalarPrimeLogScaleSum_split (a x y : ℝ) (R : ℕ) (hR : 2 ≤ R)
    (hxR : x ≤ R) (hRy : (R : ℝ) ≤ y) :
    primeLogScaleSum (Real.log R) x y (scalarPrimeIntegrand a) =
      primeLogScaleSum (Real.log R) x R (scalarSmallPrimeIntegrand a) +
        primeLogScaleSum (Real.log R) R y (scalarLargePrimeIntegrand a) := by
  have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  rw [primeLogScaleSum_split (Real.log R) x R y hxR hRy]
  congr 1
  · unfold primeLogScaleSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpR : p ≤ R := by
      simpa only [Nat.floor_natCast] using (Finset.mem_Ioc.mp hp'.1).2
    have hz : Real.log p / Real.log R ≤ 1 := (div_le_one hL).mpr
      (Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hpR))
    rw [scalarPrimeIntegrand_eq_small a _ hz]
  · unfold primeLogScaleSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hRp : R < p := by
      simpa only [Nat.floor_natCast] using (Finset.mem_Ioc.mp hp'.1).1
    have hz : 1 ≤ Real.log p / Real.log R := (one_le_div hL).mpr
      (Real.log_le_log (by exact_mod_cast (show 0 < R by omega)) (by exact_mod_cast hRp.le))
    rw [scalarPrimeIntegrand_eq_large a _ hz]

end Erdos964
