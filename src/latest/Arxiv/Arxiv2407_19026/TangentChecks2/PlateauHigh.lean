import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound2Native

lemma plateau_high_lower :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      tangentXLog (33 / 1000) z ≤
        tangentALog (9 / 200) (99 / 100) :=
  tangent_plateau_high_round2

end TangentRound2Native
end Arxiv2407_19026
