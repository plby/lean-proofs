import Arxiv.Arxiv2407_19026.TangentChecks3.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back1_book_check :
    checkLowerAffineCover (backwardBook β2 β3 r3Back1T)
      (1 / 1000000) cfg (3 / 8) back1Medium = true := by
  native_decide

end TangentRound3Native
end Arxiv2407_19026
