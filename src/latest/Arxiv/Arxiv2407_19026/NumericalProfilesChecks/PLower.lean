import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

namespace Arxiv2407_19026
namespace Beta0Affine

lemma p_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 2 : ℝ) ≤ beta0PolynomialP z := by
  intro z hz
  have hz0 : 0 ≤ z := hz.1
  have h1z : 0 ≤ 1 - z := by linarith [hz.2]
  rw [← sub_nonneg]
  have hidentity :
      beta0PolynomialP z - 1 / 2 =
        (1 / 2 : ℝ) * (1 - z) ^ 10 +
        10 * (928868812149 / 2500000000000 : ℝ) * z * (1 - z) ^ 9 +
        45 * (6535352617201 / 22500000000000 : ℝ) * z ^ 2 * (1 - z) ^ 8 +
        120 * (27917246107223 / 120000000000000 : ℝ) * z ^ 3 * (1 - z) ^ 7 +
        210 * (2843255513693 / 15000000000000 : ℝ) * z ^ 4 * (1 - z) ^ 6 +
        252 * (39095884681309 / 252000000000000 : ℝ) * z ^ 5 * (1 - z) ^ 5 +
        210 * (6660051767483 / 52500000000000 : ℝ) * z ^ 6 * (1 - z) ^ 4 +
        120 * (613848528619 / 6000000000000 : ℝ) * z ^ 7 * (1 - z) ^ 3 +
        45 * (18866725069 / 234375000000 : ℝ) * z ^ 8 * (1 - z) ^ 2 +
        10 * (24191672811 / 400000000000 : ℝ) * z ^ 9 * (1 - z) +
        (20876436183 / 500000000000 : ℝ) * z ^ 10 := by
    unfold beta0PolynomialP beta0U
    norm_num
    ring
  rw [hidentity]
  positivity

end Beta0Affine
end Arxiv2407_19026
