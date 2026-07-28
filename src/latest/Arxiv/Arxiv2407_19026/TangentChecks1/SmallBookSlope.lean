import Arxiv.Arxiv2407_19026.TangentChecks1.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_book_slope_check :
    checkLowerAffineCover (smallBookSlope β0 β1) (1 / 1000)
      cfg 0 bpsBookSlope = true := by
  native_decide

end TangentRound1Native
end Arxiv2407_19026
