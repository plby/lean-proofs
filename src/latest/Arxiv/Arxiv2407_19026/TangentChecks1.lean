import Arxiv.Arxiv2407_19026.TangentChecks1.SmallCoord
import Arxiv.Arxiv2407_19026.TangentChecks1.SmallBookSlope
import Arxiv.Arxiv2407_19026.TangentChecks1.SmallBook
import Arxiv.Arxiv2407_19026.TangentChecks1.Back1Coord
import Arxiv.Arxiv2407_19026.TangentChecks1.Back1Book
import Arxiv.Arxiv2407_19026.TangentChecks1.Back2Coord
import Arxiv.Arxiv2407_19026.TangentChecks1.Back2Book

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine

lemma small_checks :
    checkLowerAffineCover (smallCoordSlope β0 β1) (1 / 20)
        cfg 0 bpsSlope = true ∧
      checkLowerAffineCover (smallBookSlope β0 β1) (1 / 1000)
        cfg 0 bpsBookSlope = true ∧
      checkLowerAffineCover (smallBook β0 β1) (1 / 10000)
        cfg (1 / 50) bpsBook = true :=
  ⟨small_coord_check, small_book_slope_check, small_book_check⟩

lemma back1_checks :
    checkLowerAffineCover (backwardLogCoord β0 β1 r1Back1T) 0
        cfg (387 / 1000) back1Fine = true ∧
      checkLowerAffineCover (backwardBook β0 β1 r1Back1T)
        (1 / 1000000) cfg (387 / 1000) back1Medium = true :=
  ⟨back1_coord_check, back1_book_check⟩

lemma back2_checks :
    checkLowerAffineCover (backwardLogCoord β0 β1 r1Back2T) 0
        cfg (3 / 5) back2Fine = true ∧
      checkLowerAffineCover (backwardBook β0 β1 r1Back2T)
        (1 / 1000000) cfg (3 / 5) back2Medium = true :=
  ⟨back2_coord_check, back2_book_check⟩

end TangentRound1Native
end Arxiv2407_19026
