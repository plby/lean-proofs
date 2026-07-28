import Arxiv.Arxiv2407_19026.TangentChecks2
import Arxiv.Arxiv2407_19026.TangentChecks2Front.ForwardCoord
import Arxiv.Arxiv2407_19026.TangentChecks2Front.PlateauBook
import Arxiv.Arxiv2407_19026.TangentChecks2Front.Back2Book

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine

lemma forward_checks :
    checkLowerAffineCover (forwardLogCoord β1 β2 r2ForwardT) 0
        cfg (1 / 10) forwardCoordRefined = true ∧
      checkLowerAffineCover (forwardBook β1 β2 r2ForwardT)
        (1 / 1000000) cfg (1 / 10) forwardMedium = true :=
  ⟨forward_coord_check, forward_book_check⟩

lemma plateau_checks :
    checkLowerAffineCover (plateauLogLow β1 β2 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauLogHigh β1 β2 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauBook β1 β2 plateauT)
        (1 / 1000000) cfg (67 / 250) plateauBookRefined = true :=
  ⟨plateau_coord_checks.1, plateau_coord_checks.2, plateau_book_check⟩

lemma back2_checks :
    checkLowerAffineCover (backwardLogCoord β1 β2 r2Back2T) 0
        cfg (3 / 5) back2Fine = true ∧
      checkLowerAffineCover (backwardBook β1 β2 r2Back2T)
        (1 / 1000000) cfg (3 / 5) back2BookRefined = true :=
  ⟨back2_coord_check, back2_book_check⟩

end TangentRound2Native
end Arxiv2407_19026
