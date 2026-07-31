import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound2Native

/-- The small-book derivative bound in the second tangent round. -/
lemma small_book_prime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
      (1 / 1000 : ℝ) ≤
        tangentSmallBookMarginPrime (9 / 200) (33 / 1000) z := by
  intro z hz
  exact tangent_small_book_prime_lower (by norm_num) (by norm_num) hz

end TangentRound2Native
end Arxiv2407_19026
