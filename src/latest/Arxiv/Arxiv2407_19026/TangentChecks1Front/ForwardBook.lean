import Arxiv.Arxiv2407_19026.TangentChecks1Front.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_book_check :
    checkLowerAffineCover (forwardBook β0 β1 r1ForwardT)
      (1 / 1000000) cfg (1 / 10) forwardMedium = true := by
  native_decide

end TangentRound1Native
end Arxiv2407_19026
