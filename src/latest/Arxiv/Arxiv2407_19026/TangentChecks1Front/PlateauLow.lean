import Arxiv.Arxiv2407_19026.TangentKernelBounds

namespace Arxiv2407_19026
namespace TangentRound1Native

lemma plateau_low_lower :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      tangentBLog (2 / 25) (99 / 100) ≤
        tangentXLog (9 / 200) z :=
  tangent_plateau_low_round1

end TangentRound1Native
end Arxiv2407_19026
