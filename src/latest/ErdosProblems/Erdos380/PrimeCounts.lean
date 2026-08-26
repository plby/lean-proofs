import ErdosProblems.Erdos380.PrimeProductMixing
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# Sizes of the finite prime pools

This uses the repository's proved prime number theorem, not a new analytic
assumption. The constants are deliberately coarse for the mixing estimate.
-/

open scoped BigOperators Topology Asymptotics
open Filter Asymptotics

namespace Erdos380

def dyadicPrimes (N : ℕ) : Finset ℕ := (Finset.Ioc N (2 * N)).filter Nat.Prime

lemma dyadicPrimes_eq_sdiff (N : ℕ) :
    dyadicPrimes N = (2 * N).primesLE \ N.primesLE := by
  ext p
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
    Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    exact ⟨⟨hhi, hp⟩, fun h => (not_le_of_gt hlo) h.1⟩
  · rintro ⟨⟨hhi, hp⟩, hnot⟩
    have hlo : ¬ p ≤ N := fun h => hnot ⟨h, hp⟩
    exact ⟨⟨Nat.lt_of_not_ge hlo, hhi⟩, hp⟩

lemma dyadicPrimes_card_add (N : ℕ) :
    (dyadicPrimes N).card + Nat.primeCounting N = Nat.primeCounting (2 * N) := by
  rw [dyadicPrimes_eq_sdiff, ← Nat.primesLE_card_eq_primeCounting N,
    ← Nat.primesLE_card_eq_primeCounting (2 * N)]
  apply Finset.card_sdiff_add_card_eq_card
  exact Nat.primesLE_mono (by omega)

theorem eventually_primeCounting_bounds : ∀ᶠ N : ℕ in atTop,
    (9 / 10 : ℝ) * ((N : ℝ) / Real.log N) ≤ Nat.primeCounting N ∧
      (Nat.primeCounting N : ℝ) ≤ (11 / 10 : ℝ) * ((N : ℝ) / Real.log N) := by
  have h := BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent.isLittleO.def
    (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [h, eventually_ge_atTop 2] with N hN hN2
  have hpos : 0 ≤ (N : ℝ) / Real.log N :=
    div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hN
  obtain ⟨hlo, hhi⟩ := abs_le.mp hN
  constructor <;> linarith

lemma log_two_mul_le_three_halves {N : ℕ} (hN : 4 ≤ N) :
    Real.log ((2 * N : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * Real.log N := by
  have hnpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog : Real.log 4 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hnpos.ne']
  linarith

theorem eventually_dyadicPrimes_card_bounds : ∀ᶠ N : ℕ in atTop,
    ((N : ℝ) / Real.log N) / 10 ≤ ((dyadicPrimes N).card : ℝ) ∧
      ((dyadicPrimes N).card : ℝ) ≤ 3 * ((N : ℝ) / Real.log N) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_primeCounting_bounds
  filter_upwards [eventually_ge_atTop (max N₀ 4)] with N hN
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN4 : 4 ≤ N := (le_max_right _ _).trans hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlog2 : 0 < Real.log ((2 * N : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * N))
  have hband := dyadicPrimes_card_add N
  have hbandR : ((dyadicPrimes N).card : ℝ) + (Nat.primeCounting N : ℝ) =
      (Nat.primeCounting (2 * N) : ℝ) := by exact_mod_cast hband
  obtain ⟨hlo, hhi⟩ := hN₀ N hN0
  obtain ⟨hlo2, hhi2⟩ := hN₀ (2 * N) (by omega)
  have hlogratio := log_two_mul_le_three_halves hN4
  have hlogmono : Real.log (N : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) :=
    Real.log_le_log hn (by exact_mod_cast (by omega : N ≤ 2 * N))
  have hscale : (6 / 5 : ℝ) * ((N : ℝ) / Real.log N) ≤
      (9 / 10 : ℝ) * (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_div_iff₀ hlog (by simpa using hlog2)).mpr
    have hm := mul_le_mul_of_nonneg_left hlogratio hn.le
    push_cast at hm
    nlinarith
  have hscale2 : (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) ≤
      2 * ((N : ℝ) / Real.log N) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hlog2 hlog).mpr
    push_cast
    exact mul_le_mul_of_nonneg_left (by simpa using hlogmono) (by positivity)
  have hnonneg : 0 ≤ (N : ℝ) / Real.log N := div_nonneg hn.le hlog.le
  constructor <;> nlinarith

end Erdos380
