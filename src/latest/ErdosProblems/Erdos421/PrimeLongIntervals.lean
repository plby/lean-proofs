import ErdosProblems.Erdos421.ThetaLongIntervals
import Mathlib.Algebra.BigOperators.Intervals

/-! # Counting actual primes in the logarithmically long reference intervals -/

namespace Erdos421

noncomputable def primesInRealInterval (u v : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime

theorem mem_primesInRealInterval {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (p : ℕ) :
    p ∈ primesInRealInterval u v ↔ p.Prime ∧ u < p ∧ (p : ℝ) ≤ v := by
  have hv : 0 ≤ v := hu.trans huv
  simp only [primesInRealInterval, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    exact ⟨hp, (Nat.floor_lt hu).mp hlo, (Nat.cast_le.mpr hhi).trans (Nat.floor_le hv)⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨(Nat.floor_lt hu).mpr hlo, (Nat.le_floor_iff hv).mpr hhi⟩, hp⟩

theorem theta_sub_eq_prime_interval_sum {u v : ℝ} (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u =
      ∑ p ∈ primesInRealInterval u v, Real.log (p : ℝ) := by
  have hsum := Finset.sum_Ioc_consecutive (fun p : ℕ ↦ if p.Prime then Real.log (p : ℝ) else 0)
    (Nat.zero_le ⌊u⌋₊) (Nat.floor_mono huv)
  unfold Chebyshev.theta primesInRealInterval
  simp only [Finset.sum_filter]
  linarith only [hsum]

theorem theta_sub_le_prime_card_mul_log {u v : ℝ} (hv : 0 < v) (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta u ≤ (primesInRealInterval u v).card * Real.log v := by
  rw [theta_sub_eq_prime_interval_sum huv]
  calc
    _ ≤ ∑ _p ∈ primesInRealInterval u v, Real.log v := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
      have hpn : p ≤ ⌊v⌋₊ := (Finset.mem_Ioc.mp hinterval).2
      exact Real.log_le_log (Nat.cast_pos.mpr hprime.pos)
        ((Nat.cast_le.mpr hpn).trans (Nat.floor_le hv.le))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem prime_long_interval_card_lower_bound {B : ℝ} (hB : 0 ≤ B) :
    ∃ X₀ > 1, ∀ X u v : ℝ, X₀ ≤ X → X ≤ u → u ≤ v → v ≤ 2 * X →
      X / (Real.log X) ^ B ≤ v - u →
      (v - u) / (2 * Real.log (2 * X)) ≤ (primesInRealInterval u v).card := by
  obtain ⟨X₀, hX₀, htheta⟩ := theta_long_interval_lower_bound hB
  refine ⟨X₀, hX₀, ?_⟩
  intro X u v hX hXu huv hvX hlen
  have hX1 : 1 < X := hX₀.trans_le hX
  have hXp : 0 < X := by linarith
  have hvp : 0 < v := hXp.trans_le (hXu.trans huv)
  have hlog : 0 < Real.log (2 * X) := Real.log_pos (by linarith)
  have hlower := htheta X u v hX hXu huv hvX hlen
  have hupper := theta_sub_le_prime_card_mul_log hvp huv
  have hlogv : Real.log v ≤ Real.log (2 * X) := Real.log_le_log hvp hvX
  have hm := mul_le_mul_of_nonneg_left hlogv
    (Nat.cast_nonneg (primesInRealInterval u v).card : (0 : ℝ) ≤ (primesInRealInterval u v).card)
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log (2 * X))).mpr
  nlinarith

end Erdos421
