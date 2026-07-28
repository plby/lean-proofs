import Arxiv.Arxiv2407_19026.TangentChecks2Front.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_coord_check :
    checkLowerAffineCover (forwardLogCoord β1 β2 r2ForwardT) 0
      cfg (1 / 10) forwardCoordRefined = true := by
  native_decide

end TangentRound2Native
end Arxiv2407_19026
