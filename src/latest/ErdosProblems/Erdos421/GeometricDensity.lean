import Util.Density
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Passing geometric prefix bounds to natural density -/

namespace Erdos421

open Filter
open scoped Topology

noncomputable def prefixCount (S : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (· ∈ S)).card

theorem prefixCount_mono (S : Set ℕ) : Monotone (prefixCount S) := by
  classical
  intro M N hMN
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hMN))

theorem partialDensity_eq_prefixCount (S : Set ℕ) (N : ℕ) :
    S.partialDensity Set.univ N = (prefixCount S N : ℝ) / N := by
  classical
  have hset : S ∩ Set.Iio N = ↑((Finset.range N).filter (· ∈ S)) := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat,
    hset, Set.ncard_coe_finset, prefixCount]

theorem nat_log_tendsto {b : ℕ} (hb : 1 < b) : Tendsto (Nat.log b) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro m
  exact ⟨b ^ m, fun n hn ↦ Nat.le_log_of_pow_le hb hn⟩

/-- A monotone counting function bounded by a smaller geometric progression
on geometric scales has zero density at every integer endpoint. -/
theorem geometric_prefix_ratio_tendsto {f : ℕ → ℕ} (hf : Monotone f)
    {a b C N₀ : ℕ} (hb : 1 < b) (hab : a < b)
    (hbound : ∀ u, N₀ ≤ u → f (b ^ u) ≤ C * a ^ u) :
    Tendsto (fun n : ℕ ↦ (f n : ℝ) / n) atTop (𝓝 0) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hratio : (a : ℝ) / b < 1 := (div_lt_one hbpos).mpr (by exact_mod_cast hab)
  have hpow : Tendsto (fun u : ℕ ↦ ((a : ℝ) / b) ^ u) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hratio
  have hlim : Tendsto (fun n : ℕ ↦ (C : ℝ) * a *
      ((a : ℝ) / b) ^ Nat.log b n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (hpow.comp (nat_log_tendsto hb)).const_mul ((C : ℝ) * a)
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ by positivity)) _ hlim
  filter_upwards [(nat_log_tendsto hb).eventually (eventually_ge_atTop N₀),
    eventually_gt_atTop 0] with n hn hnpos
  let u := Nat.log b n
  have hnupper : n ≤ b ^ (u + 1) := (Nat.lt_pow_succ_log_self hb n).le
  have hnlower : b ^ u ≤ n := Nat.pow_log_le_self b hnpos.ne'
  have hcount : f n ≤ C * a ^ (u + 1) :=
    (hf hnupper).trans (hbound (u + 1) (by dsimp only [u]; omega))
  have hden : (0 : ℝ) < (b : ℝ) ^ u := pow_pos hbpos _
  calc
    (f n : ℝ) / n ≤ (C * a ^ (u + 1) : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast hcount
    _ ≤ (C * a ^ (u + 1) : ℝ) / (b : ℝ) ^ u := by
      apply div_le_div_of_nonneg_left (by positivity) hden
      exact_mod_cast hnlower
    _ = (C : ℝ) * a * ((a : ℝ) / b) ^ u := by rw [pow_succ, div_pow]; ring

theorem hasDensity_zero_of_geometric_bound (S : Set ℕ) {a b C N₀ : ℕ}
    (hb : 1 < b) (hab : a < b)
    (hbound : ∀ u, N₀ ≤ u → prefixCount S (b ^ u) ≤ C * a ^ u) :
    S.HasDensity 0 := by
  simp only [Set.HasDensity, partialDensity_eq_prefixCount]
  exact geometric_prefix_ratio_tendsto (prefixCount_mono S) hb hab hbound

end Erdos421
