import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound3Native

lemma plateau_low_lower :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      tangentBLog (33 / 1000) (99 / 100) ≤
        tangentXLog (3 / 100) z :=
  tangent_plateau_low_round3

end TangentRound3Native
end Arxiv2407_19026
