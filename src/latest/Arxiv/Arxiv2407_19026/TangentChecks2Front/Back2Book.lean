import Arxiv.Arxiv2407_19026.TangentChecks2Front.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back2_book_check :
    checkLowerAffineCover (backwardBook β1 β2 r2Back2T)
      (1 / 1000000) cfg (3 / 5) back2BookRefined = true := by
  native_decide

end TangentRound2Native
end Arxiv2407_19026
