import Arxiv.Arxiv2407_19026.TangentChecks1.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back1_book_check :
    checkLowerAffineCover (backwardBook β0 β1 r1Back1T)
      (1 / 1000000) cfg (387 / 1000) back1Medium = true := by
  native_decide

end TangentRound1Native
end Arxiv2407_19026
