import ErdosProblems.Erdos421.PrimeFreePrefixEstimate
import ErdosProblems.Erdos421.GeometricDensityLimit
import ErdosProblems.Erdos421.BoundedOmissionCount

/-! # Density one of Chojecki's actual gap-greedy candidate -/

namespace Erdos421

open Filter Topology

theorem candidate_compl_prefix_scale_tendsto :
    Tendsto (fun u : ℕ ↦ (prefixCount candidateᶜ (2 ^ (180 * u)) : ℝ) /
      (2 : ℝ) ^ (180 * u)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun u : ℕ ↦ (2 : ℝ) ^ (180 * u)) atTop atTop := by
    simpa only [pow_mul] using tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1 : ℝ) < (2 : ℝ) ^ (180 : ℕ))
  have hconst := hpow.const_div_atTop (2 : ℝ)
  have hratio : (2 : ℝ) ^ (179 : ℕ) / (2 : ℝ) ^ (180 : ℕ) < 1 := by norm_num
  have hrpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hratio
  have hshort : Tendsto (fun u : ℕ ↦
      (7 : ℝ) * (2 : ℝ) ^ (179 * (u + 1)) / (2 : ℝ) ^ (180 * u)) atTop (𝓝 0) := by
    have hlim := hrpow.const_mul ((7 : ℝ) * (2 : ℝ) ^ (179 : ℕ))
    simp only [mul_zero] at hlim
    apply hlim.congr'
    apply Eventually.of_forall
    intro u
    simp only [Nat.mul_add, Nat.mul_one, pow_add, pow_mul, div_pow]
    ring
  have hmajor := (hconst.add hshort).add (primeFreeStarts_final_ratio_tendsto.const_mul 2)
  simp only [add_zero, mul_zero] at hmajor
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) _ hmajor
  filter_upwards [eventually_ge_atTop 12] with u hu
  have h := candidate_compl_bounded_prefix_scale hu
  have hR : (prefixCount candidateᶜ (2 ^ (180 * u)) : ℝ) ≤
      2 + 7 * (2 : ℝ) ^ (179 * (u + 1)) +
        2 * (primeFreeStarts (2 ^ (180 * (u + 1))) (2 ^ (19 * u))).card := by exact_mod_cast h
  calc
    _ ≤ (2 + 7 * (2 : ℝ) ^ (179 * (u + 1)) +
        2 * (primeFreeStarts (2 ^ (180 * (u + 1))) (2 ^ (19 * u))).card) /
          (2 : ℝ) ^ (180 * u) := div_le_div_of_nonneg_right hR (by positivity)
    _ = _ := by ring

theorem candidate_compl_hasDensity_zero : candidateᶜ.HasDensity 0 := by
  apply hasDensity_zero_of_geometric_limit candidateᶜ (b := 2 ^ 180) (by norm_num)
  simpa only [pow_mul, Nat.cast_pow, Nat.cast_ofNat] using candidate_compl_prefix_scale_tendsto

theorem prefixCount_add_compl (S : Set ℕ) (N : ℕ) :
    prefixCount S N + prefixCount Sᶜ N = N := by
  classical
  simpa only [prefixCount, Set.mem_compl_iff, Finset.card_range] using
    Finset.card_filter_add_card_filter_not (s := Finset.range N) (p := fun n ↦ n ∈ S)

theorem partialDensity_eq_one_sub_compl (S : Set ℕ) {N : ℕ} (hN : 0 < N) :
    S.partialDensity Set.univ N = 1 - Sᶜ.partialDensity Set.univ N := by
  rw [partialDensity_eq_prefixCount, partialDensity_eq_prefixCount]
  have hcard : (prefixCount S N : ℝ) + (prefixCount Sᶜ N : ℝ) = N :=
    by exact_mod_cast prefixCount_add_compl S N
  apply (eq_sub_iff_add_eq).mpr
  rw [← add_div, hcard, div_self (by exact_mod_cast hN.ne')]

theorem candidate_hasDensity_one : candidate.HasDensity 1 := by
  have hlim : Tendsto (fun N : ℕ ↦ (1 : ℝ) - candidateᶜ.partialDensity Set.univ N) atTop
      (𝓝 (1 - 0)) := tendsto_const_nhds.sub candidate_compl_hasDensity_zero
  norm_num only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (partialDensity_eq_one_sub_compl candidate hN).symm

end Erdos421
