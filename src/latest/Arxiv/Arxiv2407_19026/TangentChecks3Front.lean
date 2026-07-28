import Arxiv.Arxiv2407_19026.TangentChecks3
import Arxiv.Arxiv2407_19026.TangentChecks3Front.SmallCoord
import Arxiv.Arxiv2407_19026.TangentChecks3Front.ForwardCoord
import Arxiv.Arxiv2407_19026.TangentChecks3Front.Back2Book

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine

lemma small_checks :
    checkLowerAffineCover (smallCoordSlope β2 β3) (1 / 20)
        cfg 0 smallCoordRefined = true ∧
      checkLowerAffineCover (smallBookSlope β2 β3) (1 / 1000)
        cfg 0 bpsBookSlope = true ∧
      checkLowerAffineCover (smallBook β2 β3) (1 / 10000)
        cfg (1 / 50) bpsBook = true :=
  ⟨small_coord_check, small_book_checks⟩

lemma forward_checks :
    checkLowerAffineCover (forwardLogCoord β2 β3 r3ForwardT) 0
        cfg (1 / 10) forwardCoordRefined = true ∧
      checkLowerAffineCover (forwardBook β2 β3 r3ForwardT)
        (1 / 1000000) cfg (1 / 10) forwardMedium = true :=
  ⟨forward_coord_check, forward_book_check⟩

lemma back2_checks :
    checkLowerAffineCover (backwardLogCoord β2 β3 r3Back2T) 0
        cfg (3 / 5) back2Fine = true ∧
      checkLowerAffineCover (backwardBook β2 β3 r3Back2T)
        (1 / 1000000) cfg (3 / 5) back2BookRefined = true :=
  ⟨back2_coord_check, back2_book_check⟩

end TangentRound3Native
end Arxiv2407_19026
