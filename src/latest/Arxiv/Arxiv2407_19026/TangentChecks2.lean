import Arxiv.Arxiv2407_19026.TangentChecks2.SmallCoord
import Arxiv.Arxiv2407_19026.TangentChecks2.SmallBookSlope
import Arxiv.Arxiv2407_19026.TangentChecks2.SmallBook
import Arxiv.Arxiv2407_19026.TangentChecks2.ForwardBook
import Arxiv.Arxiv2407_19026.TangentChecks2.PlateauLow
import Arxiv.Arxiv2407_19026.TangentChecks2.PlateauHigh
import Arxiv.Arxiv2407_19026.TangentChecks2.Back1Coord
import Arxiv.Arxiv2407_19026.TangentChecks2.Back1Book
import Arxiv.Arxiv2407_19026.TangentChecks2.Back2Coord

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine

lemma small_checks :
    checkLowerAffineCover (smallCoordSlope β1 β2) (1 / 20)
        cfg 0 bpsSlope = true ∧
      checkLowerAffineCover (smallBookSlope β1 β2) (1 / 1000)
        cfg 0 bpsBookSlope = true ∧
      checkLowerAffineCover (smallBook β1 β2) (1 / 10000)
        cfg (1 / 50) bpsBook = true :=
  ⟨small_coord_check, small_book_slope_check, small_book_check⟩

lemma plateau_coord_checks :
    checkLowerAffineCover (plateauLogLow β1 β2 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauLogHigh β1 β2 plateauT) 0
        cfg (67 / 250) plateauMedium = true :=
  ⟨plateau_low_check, plateau_high_check⟩

lemma back1_checks :
    checkLowerAffineCover (backwardLogCoord β1 β2 r2Back1T) 0
        cfg (189 / 500) back1Fine = true ∧
      checkLowerAffineCover (backwardBook β1 β2 r2Back1T)
        (1 / 1000000) cfg (189 / 500) back1Medium = true :=
  ⟨back1_coord_check, back1_book_check⟩

end TangentRound2Native
end Arxiv2407_19026
