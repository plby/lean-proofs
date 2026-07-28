import Arxiv.Arxiv2407_19026.TangentChecks3.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_book_check :
    checkLowerAffineCover (forwardBook β2 β3 r3ForwardT)
      (1 / 1000000) cfg (1 / 10) forwardMedium = true := by
  native_decide

end TangentRound3Native
end Arxiv2407_19026
