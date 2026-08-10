import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

namespace Arxiv2407_19026
namespace Beta0Affine

private lemma x_large_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 5 : ℝ) ≤ 1 - z * beta0VLarge z := by
  intro z hz
  have hz0 : 0 ≤ z := hz.1
  have h1z : 0 ≤ 1 - z := by linarith [hz.2]
  rw [← sub_nonneg]
  have hidentity :
      1 - z * beta0VLarge z - 1 / 5 =
        (4 / 5 : ℝ) * (1 - z) ^ 11 +
        11 * (162374360497 / 275000000000 : ℝ) * z * (1 - z) ^ 10 +
        55 * (24201189930727 / 55000000000000 : ℝ) * z ^ 2 * (1 - z) ^ 9 +
        165 * (27334743901679 / 82500000000000 : ℝ) * z ^ 3 * (1 - z) ^ 8 +
        330 * (27654172792789 / 110000000000000 : ℝ) * z ^ 4 * (1 - z) ^ 7 +
        462 * (4217931904051 / 22000000000000 : ℝ) * z ^ 5 * (1 - z) ^ 6 +
        462 * (22599742810741 / 154000000000000 : ℝ) * z ^ 6 * (1 - z) ^ 5 +
        330 * (1126140146339 / 10000000000000 : ℝ) * z ^ 7 * (1 - z) ^ 4 +
        165 * (4758563331719 / 55000000000000 : ℝ) * z ^ 8 * (1 - z) ^ 3 +
        55 * (146293274907 / 2200000000000 : ℝ) * z ^ 9 * (1 - z) ^ 2 +
        11 * (561418221363 / 11000000000000 : ℝ) * z ^ 10 * (1 - z) +
        (19528023833 / 500000000000 : ℝ) * z ^ 11 := by
    unfold beta0VLarge
    norm_num
    ring
  rw [hidentity]
  positivity

lemma x_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 5 : ℝ) ≤ beta0PolynomialX z := by
  intro z hz
  by_cases hzsmall : z ≤ 3 / 1000
  · rw [beta0PolynomialX, beta0V, if_pos hzsmall]
    norm_num at hz ⊢
    nlinarith [hz.1]
  · rw [beta0PolynomialX, beta0V, if_neg hzsmall]
    exact x_large_lower z hz

end Beta0Affine
end Arxiv2407_19026
