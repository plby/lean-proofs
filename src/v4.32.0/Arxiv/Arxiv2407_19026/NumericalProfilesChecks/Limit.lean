import Arxiv.Arxiv2407_19026.NumericalProfilesLimitPositive

namespace Arxiv2407_19026
namespace Beta0Affine

lemma limit_pos :
    ∀ z ∈ Set.Ioc (3 / 1000 : ℝ) 1,
      0 < beta0PolynomialLimitLogMargin z := by
  exact fun _ hz =>
    beta0_polynomial_limit_log_margin_large_pos hz

end Beta0Affine
end Arxiv2407_19026
