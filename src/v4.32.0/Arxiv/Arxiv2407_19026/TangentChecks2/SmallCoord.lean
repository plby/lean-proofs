import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound2Native

/-- The small-coordinate derivative bound in the second tangent round. -/
lemma small_coord_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
      (1 / 20 : ℝ) ≤
        tangentSmallCoordLogPrime (9 / 200) (33 / 1000) z := by
  intro z hz
  exact tangent_small_coord_prime_lower (by norm_num) (by norm_num) hz

end TangentRound2Native
end Arxiv2407_19026
