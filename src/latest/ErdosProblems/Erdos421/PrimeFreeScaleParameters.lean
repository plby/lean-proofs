import ErdosProblems.Erdos421.PrimeShortWidth
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The final gap cutoff dominates every short prime-window length below its endpoint -/

namespace Erdos421

open Filter Topology

theorem eventually_primeShortLength_final_scale :
    ∀ᶠ u : ℕ in atTop,
      primeShortLength (2 ^ (180 * (u + 1)) : ℕ) ≤ (2 ^ (19 * u) : ℕ) := by
  let C : ℝ := 1 + 64 * Real.pi * (2 : ℝ) ^ (909 / 50 : ℝ)
  have hpow : Tendsto (fun u : ℕ ↦ (2 : ℕ) ^ u) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hsave := hpow.eventually
    (eventually_constant_rpow_le C (by norm_num : (909 / 50 : ℝ) < 19))
  filter_upwards [hsave] with u hsaveu
  have hN : 1 ≤ (2 : ℕ) ^ u := by
    have h : 0 < (2 : ℕ) ^ u := by positivity
    omega
  have hR1 : (1 : ℝ) ≤ (2 ^ u : ℕ) := by exact_mod_cast hN
  have hRp : 1 ≤ ((2 ^ u : ℕ) : ℝ) ^ (909 / 50 : ℝ) :=
    Real.one_le_rpow hR1 (by norm_num)
  have hB : ((2 ^ (180 * (u + 1)) : ℕ) : ℝ) ^ (101 / 1000 : ℝ) =
      (2 : ℝ) ^ (909 / 50 : ℝ) * ((2 ^ u : ℕ) : ℝ) ^ (909 / 50 : ℝ) := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have hH : ((2 ^ u : ℕ) : ℝ) ^ (19 : ℝ) = ((2 ^ (19 * u) : ℕ) : ℝ) := by
    norm_num only [Real.rpow_ofNat, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul]
    congr 1
    omega
  rw [hH] at hsaveu
  unfold primeShortLength
  rw [hB]
  calc
    _ ≤ C * ((2 ^ u : ℕ) : ℝ) ^ (909 / 50 : ℝ) := by dsimp only [C]; nlinarith
    _ ≤ _ := hsaveu

end Erdos421
