import Arxiv.Arxiv2407_19026.TangentChecks1.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back2_book_check :
    checkLowerAffineCover (backwardBook β0 β1 r1Back2T)
      (1 / 1000000) cfg (3 / 5) back2Medium = true := by
  native_decide

end TangentRound1Native
end Arxiv2407_19026
