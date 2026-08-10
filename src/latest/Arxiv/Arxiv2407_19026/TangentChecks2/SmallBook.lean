import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound2Native

/-- The direct small-book bound in the second tangent round. -/
lemma small_book_lower :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
      (1 / 10000 : ℝ) ≤
        tangentSmallBookMargin (9 / 200) (33 / 1000) z := by
  intro z hz
  exact tangent_small_book_lower (by norm_num) (by norm_num) hz

end TangentRound2Native
end Arxiv2407_19026
