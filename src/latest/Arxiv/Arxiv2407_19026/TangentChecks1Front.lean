import Arxiv.Arxiv2407_19026.TangentChecks1
import Arxiv.Arxiv2407_19026.TangentChecks1Front.ForwardCoord
import Arxiv.Arxiv2407_19026.TangentChecks1Front.ForwardBook
import Arxiv.Arxiv2407_19026.TangentChecks1Front.PlateauLow
import Arxiv.Arxiv2407_19026.TangentChecks1Front.PlateauHigh
import Arxiv.Arxiv2407_19026.TangentChecks1Front.PlateauBook

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine

lemma forward_checks :
    checkLowerAffineCover (forwardLogCoord β0 β1 r1ForwardT) 0
        cfg (1 / 10) forwardCoordRefined = true ∧
      checkLowerAffineCover (forwardBook β0 β1 r1ForwardT)
        (1 / 1000000) cfg (1 / 10) forwardMedium = true :=
  ⟨forward_coord_check, forward_book_check⟩

lemma plateau_checks :
    checkLowerAffineCover (plateauLogLow β0 β1 plateauT) 0
        cfg (269 / 1000) plateauMedium = true ∧
      checkLowerAffineCover (plateauLogHigh β0 β1 plateauT) 0
        cfg (269 / 1000) plateauMedium = true ∧
      checkLowerAffineCover (plateauBook β0 β1 plateauT)
        (1 / 1000000) cfg (269 / 1000) plateauBookRefined = true :=
  ⟨plateau_low_check, plateau_high_check, plateau_book_check⟩

end TangentRound1Native
end Arxiv2407_19026
