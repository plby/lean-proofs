import Arxiv.Arxiv2407_19026.TangentChecks3.SmallBookSlope
import Arxiv.Arxiv2407_19026.TangentChecks3.SmallBook
import Arxiv.Arxiv2407_19026.TangentChecks3.ForwardBook
import Arxiv.Arxiv2407_19026.TangentChecks3.PlateauLow
import Arxiv.Arxiv2407_19026.TangentChecks3.PlateauHigh
import Arxiv.Arxiv2407_19026.TangentChecks3.PlateauBook
import Arxiv.Arxiv2407_19026.TangentChecks3.Back1Coord
import Arxiv.Arxiv2407_19026.TangentChecks3.Back1Book
import Arxiv.Arxiv2407_19026.TangentChecks3.Back2Coord

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine

lemma small_book_checks :
    checkLowerAffineCover (smallBookSlope β2 β3) (1 / 1000)
        cfg 0 bpsBookSlope = true ∧
      checkLowerAffineCover (smallBook β2 β3) (1 / 10000)
        cfg (1 / 50) bpsBook = true :=
  ⟨small_book_slope_check, small_book_check⟩

lemma plateau_checks :
    checkLowerAffineCover (plateauLogLow β2 β3 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauLogHigh β2 β3 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauBook β2 β3 plateauT)
        (1 / 1000000) cfg (67 / 250) plateauMedium = true :=
  ⟨plateau_low_check, plateau_high_check, plateau_book_check⟩

lemma back1_checks :
    checkLowerAffineCover (backwardLogCoord β2 β3 r3Back1T) 0
        cfg (3 / 8) back1Fine = true ∧
      checkLowerAffineCover (backwardBook β2 β3 r3Back1T)
        (1 / 1000000) cfg (3 / 8) back1Medium = true :=
  ⟨back1_coord_check, back1_book_check⟩

end TangentRound3Native
end Arxiv2407_19026
