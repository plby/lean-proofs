import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound2Native

lemma plateau_low_lower :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      tangentBLog (9 / 200) (99 / 100) ≤
        tangentXLog (33 / 1000) z :=
  tangent_plateau_low_round2

end TangentRound2Native
end Arxiv2407_19026
