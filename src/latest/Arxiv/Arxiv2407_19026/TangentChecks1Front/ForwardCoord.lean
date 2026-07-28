import Arxiv.Arxiv2407_19026.TangentChecks1Front.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_coord_check :
    checkLowerAffineCover (forwardLogCoord β0 β1 r1ForwardT) 0
      cfg (1 / 10) forwardCoordRefined = true := by
  native_decide

end TangentRound1Native
end Arxiv2407_19026
