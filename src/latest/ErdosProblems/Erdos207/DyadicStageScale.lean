/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DyadicPowerScale
import ErdosProblems.Erdos207.KSSSHomogeneousScale

/-! # Compare a stage's dyadic process scale with the common vortex base -/

namespace Erdos207

theorem dyadicStageScale_le_base
    (t n D R : ℕ) (ht : 1 ≤ t) (hn : n ≠ 0) (hR : D + 1 ≤ R)
    (hupper : n ≤ t ^ (D + 1)) : dyadicPowerScale R n ≤ t := by
  have hRpos : 0 < R := by omega
  have hp : (dyadicPowerScale R n) ^ R ≤ t ^ R :=
    (dyadicPowerScale_pow_le hn).trans
      (hupper.trans (Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le ht) hR))
  exact (Nat.pow_le_pow_iff_left (by omega : R ≠ 0)).mp hp

theorem dyadicStageScale_cutoff_power_lower
    (t n D R c d : ℕ) (ht : 0 < t) (hR : 0 < R)
    (hlower : t ^ D ≤ n) (hgap : R * (d + 1) ≤ D * c) (hround : 2 ^ c ≤ t) :
    t ^ d ≤ (dyadicPowerScale R n) ^ c := by
  let u := dyadicPowerScale R n
  have hpow : (t ^ (d + 1)) ^ R ≤ (t * u ^ c) ^ R := by
    calc
      _ = t ^ (R * (d + 1)) := by rw [← pow_mul, Nat.mul_comm (d + 1) R]
      _ ≤ t ^ (D * c) := Nat.pow_le_pow_right ht hgap
      _ = (t ^ D) ^ c := pow_mul _ _ _
      _ ≤ n ^ c := Nat.pow_le_pow_left hlower c
      _ ≤ (2 ^ R * u ^ R) ^ c := Nat.pow_le_pow_left (le_two_pow_mul_dyadicPowerScale_pow hR) c
      _ = (2 ^ c * u ^ c) ^ R := by
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm R c]
      _ ≤ (t * u ^ c) ^ R := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hround) R
  have hbase : t ^ (d + 1) ≤ t * u ^ c :=
    (Nat.pow_le_pow_iff_left (by omega : R ≠ 0)).mp hpow
  rw [pow_succ'] at hbase
  exact Nat.le_of_mul_le_mul_left hbase ht

theorem exists_scaled_ksss_stage_exponents
    (q b B k Rmin D d : ℕ) (hmin : 1 ≤ Rmin)
    (hgap : ksssPowerDenominatorExponent q b B k Rmin * (d + 1) ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧
      D + 1 ≤ ksssPowerDenominatorExponent q (b * c) B (k * c) (Rmin * c) ∧
      ksssPowerDenominatorExponent q (b * c) B (k * c) (Rmin * c) * (d + 1) ≤ D * c := by
  let c := D + 1
  have hc : 1 ≤ c := by dsimp only [c]; omega
  have hminScale : c ≤ Rmin * c := by
    simpa only [one_mul] using Nat.mul_le_mul_right c hmin
  have hminR : Rmin * c ≤ ksssPowerDenominatorExponent q (b * c) B (k * c) (Rmin * c) := by
    unfold ksssPowerDenominatorExponent
    omega
  refine ⟨c, hc, hminScale.trans hminR, ?_⟩
  calc
    _ ≤ (ksssPowerDenominatorExponent q b B k Rmin * c) * (d + 1) :=
      Nat.mul_le_mul_right _ (ksssPowerDenominatorExponent_scale_le q b B k Rmin c hc)
    _ = (ksssPowerDenominatorExponent q b B k Rmin * (d + 1)) * c := by ring
    _ ≤ D * c := Nat.mul_le_mul_right c hgap

theorem exists_ksss_stage_scale_comparison
    (q b B k Rmin D d : ℕ) (hmin : 1 ≤ Rmin)
    (hgap : ksssPowerDenominatorExponent q b B k Rmin * (d + 1) ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ t n : ℕ, 1 ≤ t → t ^ D ≤ n → n ≤ t ^ (D + 1) → 2 ^ c ≤ t →
      let R := ksssPowerDenominatorExponent q (b * c) B (k * c) (Rmin * c)
      dyadicPowerScale R n ≤ t ∧ t ^ d ≤ (dyadicPowerScale R n) ^ c := by
  obtain ⟨c, hc, hRlower, hRgap⟩ := exists_scaled_ksss_stage_exponents q b B k Rmin D d hmin hgap
  refine ⟨c, hc, ?_⟩
  intro t n ht hlower hupper hround
  have htpos : 0 < t := Nat.zero_lt_one.trans_le ht
  have hn : n ≠ 0 := Nat.ne_of_gt ((pow_pos htpos _).trans_le hlower)
  exact ⟨dyadicStageScale_le_base _ _ _ _ ht hn hRlower hupper,
    dyadicStageScale_cutoff_power_lower _ _ _ _ _ _ htpos (by omega) hlower hRgap hround⟩

end Erdos207
