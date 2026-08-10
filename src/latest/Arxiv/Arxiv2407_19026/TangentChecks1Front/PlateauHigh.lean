import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound1Native

lemma plateau_high_lower :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      tangentXLog (9 / 200) z ≤
        tangentALog (2 / 25) (99 / 100) :=
  tangent_plateau_high_round1

end TangentRound1Native
end Arxiv2407_19026
