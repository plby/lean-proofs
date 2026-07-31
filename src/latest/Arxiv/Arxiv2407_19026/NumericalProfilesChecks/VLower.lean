import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

namespace Arxiv2407_19026
namespace Beta0Affine

private lemma v_large_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) ≤ beta0VLarge z := by
  intro z hz
  have hz0 : 0 ≤ z := hz.1
  have h1z : 0 ≤ 1 - z := by linarith [hz.2]
  rw [← sub_nonneg]
  have hidentity :
      beta0VLarge z - 3 / 4 =
        (38875639503 / 25000000000 : ℝ) * (1 - z) ^ 9 +
        9 * (10743784489153 / 9000000000000 : ℝ) * z * (1 - z) ^ 8 +
        36 * (32836727707489 / 36000000000000 : ℝ) * z ^ 2 * (1 - z) ^ 7 +
        84 * (1818773559817 / 2625000000000 : ℝ) * z ^ 3 * (1 - z) ^ 6 +
        126 * (13064535220157 / 25200000000000 : ℝ) * z ^ 4 * (1 - z) ^ 5 +
        126 * (2967380966687 / 7875000000000 : ℝ) * z ^ 5 * (1 - z) ^ 4 +
        84 * (3122754243403 / 12000000000000 : ℝ) * z ^ 6 * (1 - z) ^ 3 +
        36 * (2932515150511 / 18000000000000 : ℝ) * z ^ 7 * (1 - z) ^ 2 +
        9 * (80848647367 / 1000000000000 : ℝ) * z ^ 8 * (1 - z) +
        (5471976167 / 500000000000 : ℝ) * z ^ 9 := by
    unfold beta0VLarge
    norm_num
    ring
  rw [hidentity]
  positivity

lemma v_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, (3 / 4 : ℝ) ≤ beta0V z := by
  intro z hz
  by_cases hzsmall : z ≤ 3 / 1000
  · simp [beta0V, if_pos hzsmall]
    norm_num
  · simp only [beta0V, if_neg hzsmall]
    exact v_large_lower z hz

end Beta0Affine
end Arxiv2407_19026
