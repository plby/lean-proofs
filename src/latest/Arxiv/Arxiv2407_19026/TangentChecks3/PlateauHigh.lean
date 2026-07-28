import Arxiv.Arxiv2407_19026.TangentChecks3.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma plateau_high_check :
    checkLowerAffineCover (plateauLogHigh β2 β3 plateauT) 0
      cfg (67 / 250) plateauMedium = true := by
  native_decide

end TangentRound3Native
end Arxiv2407_19026
