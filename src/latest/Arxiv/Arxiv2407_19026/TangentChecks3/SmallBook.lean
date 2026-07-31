import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound3Native

/-- The direct small-book bound in the third tangent round. -/
lemma small_book_lower :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
      (1 / 10000 : ℝ) ≤
        tangentSmallBookMargin (33 / 1000) (3 / 100) z := by
  intro z hz
  exact tangent_small_book_lower (by norm_num) (by norm_num) hz

end TangentRound3Native
end Arxiv2407_19026
