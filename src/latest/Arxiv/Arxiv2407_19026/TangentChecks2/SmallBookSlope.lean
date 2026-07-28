import Arxiv.Arxiv2407_19026.TangentChecks2.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_book_slope_check :
    checkLowerAffineCover (smallBookSlope β1 β2) (1 / 1000)
      cfg 0 bpsBookSlope = true := by
  native_decide

end TangentRound2Native
end Arxiv2407_19026
