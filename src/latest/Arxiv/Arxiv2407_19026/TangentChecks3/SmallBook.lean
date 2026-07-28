import Arxiv.Arxiv2407_19026.TangentChecks3.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_book_check :
    checkLowerAffineCover (smallBook β2 β3) (1 / 10000)
      cfg (1 / 50) bpsBook = true := by
  native_decide

end TangentRound3Native
end Arxiv2407_19026
