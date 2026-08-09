import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

namespace Arxiv2407_19026
namespace Beta0Affine

lemma u_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, (2 / 5 : ℝ) ≤ beta0U z := by
  intro z hz
  have hz0 : 0 ≤ z := hz.1
  have h1z : 0 ≤ 1 - z := by linarith [hz.2]
  rw [← sub_nonneg]
  have hidentity :
      beta0U z - 2 / 5 =
        (221131187851 / 250000000000 : ℝ) * (1 - z) ^ 9 +
        9 * (2914647382799 / 4500000000000 : ℝ) * z * (1 - z) ^ 8 +
        36 * (17682753892777 / 36000000000000 : ℝ) * z ^ 2 * (1 - z) ^ 7 +
        84 * (2256744486307 / 6000000000000 : ℝ) * z ^ 3 * (1 - z) ^ 6 +
        126 * (36504115318691 / 126000000000000 : ℝ) * z ^ 4 * (1 - z) ^ 5 +
        126 * (6989948232517 / 31500000000000 : ℝ) * z ^ 5 * (1 - z) ^ 4 +
        84 * (706151471381 / 4200000000000 : ℝ) * z ^ 6 * (1 - z) ^ 3 +
        36 * (23320774931 / 187500000000 : ℝ) * z ^ 7 * (1 - z) ^ 2 +
        9 * (31808327189 / 360000000000 : ℝ) * z ^ 8 * (1 - z) +
        (29123563817 / 500000000000 : ℝ) * z ^ 9 := by
    unfold beta0U
    norm_num
    ring
  rw [hidentity]
  positivity

end Beta0Affine
end Arxiv2407_19026
