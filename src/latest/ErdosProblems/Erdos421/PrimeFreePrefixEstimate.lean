import ErdosProblems.Erdos421.PrimeFreeDyadicEstimate
import ErdosProblems.Erdos421.PrimeFreeDyadicPrefix
import ErdosProblems.Erdos421.PrimeFreeScaleParameters

/-! # The complete prime-free prefix is negligible at the scales of the gap construction -/

namespace Erdos421

open Filter Topology

theorem primeFreeStarts_final_prefix_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ᶠ u : ℕ in atTop,
      ((primeFreeStarts (2 ^ (180 * (u + 1))) (2 ^ (19 * u))).card : ℝ) ≤
        (2 : ℝ) ^ K + ε * (2 : ℝ) ^ (180 * (u + 1)) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (primeFreeDyadicStarts_eventually_small hε)
  have hpow : Tendsto (fun k : ℕ ↦ (2 : ℕ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp hpow M
  refine ⟨K, ?_⟩
  filter_upwards [eventually_primeShortLength_final_scale, eventually_ge_atTop K]
    with u hlength hu
  apply primeFreeStarts_dyadic_prefix_bound (by omega : K ≤ 180 * (u + 1)) hε.le
  intro k hKk hk
  have hpowB : (2 : ℕ) ^ k ≤ 2 ^ (180 * (u + 1)) :=
    Nat.pow_le_pow_right (by decide) hk.le
  have hlen : primeShortLength (2 ^ k : ℕ) ≤ (2 ^ (19 * u) : ℕ) :=
    (primeShortLength_mono (Nat.cast_nonneg _) (by exact_mod_cast hpowB)).trans hlength
  have h := hM (2 ^ k) (hK k hKk) (2 ^ (19 * u)) hlen
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

theorem primeFreeStarts_final_scale_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      ((primeFreeStarts (2 ^ (180 * (u + 1))) (2 ^ (19 * u))).card : ℝ) ≤
        ε * (2 : ℝ) ^ (180 * u) := by
  have hη : 0 < ε / (2 * (2 : ℝ) ^ (180 : ℕ)) := by positivity
  obtain ⟨K, hbound⟩ := primeFreeStarts_final_prefix_bound hη
  have hpow : Tendsto (fun u : ℕ ↦ (2 : ℝ) ^ (180 * u)) atTop atTop := by
    simpa only [pow_mul] using tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1 : ℝ) < (2 : ℝ) ^ (180 : ℕ))
  filter_upwards [hbound, hpow.eventually_ge_atTop ((2 : ℝ) ^ K / (ε / 2))]
    with u hboundu hsmall
  have hconst : (2 : ℝ) ^ K ≤ (ε / 2) * (2 : ℝ) ^ (180 * u) := by
    have h := (div_le_iff₀ (by positivity : 0 < ε / 2)).mp hsmall
    simpa only [mul_comm] using h
  have hmain : (ε / (2 * (2 : ℝ) ^ (180 : ℕ))) * (2 : ℝ) ^ (180 * (u + 1)) =
      (ε / 2) * (2 : ℝ) ^ (180 * u) := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
    field_simp
  calc
    _ ≤ _ := hboundu
    _ ≤ (ε / 2) * (2 : ℝ) ^ (180 * u) + (ε / 2) * (2 : ℝ) ^ (180 * u) :=
      add_le_add hconst hmain.le
    _ = _ := by ring

theorem primeFreeStarts_final_ratio_tendsto :
    Tendsto (fun u : ℕ ↦
      ((primeFreeStarts (2 ^ (180 * (u + 1))) (2 ^ (19 * u))).card : ℝ) /
        (2 : ℝ) ^ (180 * u)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ ↦ ha.trans_le (by positivity))
  · intro b hb
    filter_upwards [primeFreeStarts_final_scale_eventually_small (by positivity : 0 < b / 2)]
      with u hu
    have h := (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (180 * u))).mpr hu
    linarith

end Erdos421
