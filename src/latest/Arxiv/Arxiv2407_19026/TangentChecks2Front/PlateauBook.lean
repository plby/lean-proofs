import Arxiv.Arxiv2407_19026.TangentChecks2Front.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma plateau_book_check :
    checkLowerAffineCover (plateauBook β1 β2 plateauT)
      (1 / 1000000) cfg (67 / 250) plateauBookRefined = true := by
  native_decide

end TangentRound2Native
end Arxiv2407_19026
