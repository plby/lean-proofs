import Arxiv.Arxiv2407_19026.TangentChecks1.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back1_coord_check :
    checkLowerAffineCover (backwardLogCoord β0 β1 r1Back1T) 0
      cfg (387 / 1000) back1Fine = true := by
  native_decide

end TangentRound1Native
end Arxiv2407_19026
