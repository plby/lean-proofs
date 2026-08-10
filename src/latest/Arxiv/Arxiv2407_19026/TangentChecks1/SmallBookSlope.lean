import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound1Native

/-- The small-book derivative bound in the first tangent round. -/
lemma small_book_prime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
      (1 / 1000 : ℝ) ≤
        tangentSmallBookMarginPrime (2 / 25) (9 / 200) z := by
  intro z hz
  exact tangent_small_book_prime_lower (by norm_num) (by norm_num) hz

end TangentRound1Native
end Arxiv2407_19026
