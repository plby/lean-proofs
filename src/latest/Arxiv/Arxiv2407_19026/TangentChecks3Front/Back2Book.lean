import Arxiv.Arxiv2407_19026.TangentChecks3Front.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back2_book_check :
    checkLowerAffineCover (backwardBook β2 β3 r3Back2T)
      (1 / 1000000) cfg (3 / 5) back2BookRefined = true := by
  native_decide

end TangentRound3Native
end Arxiv2407_19026
