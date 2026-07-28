import Arxiv.Arxiv2407_19026.TangentChecks2.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma plateau_high_check :
    checkLowerAffineCover (plateauLogHigh β1 β2 plateauT) 0
      cfg (67 / 250) plateauMedium = true := by
  native_decide

end TangentRound2Native
end Arxiv2407_19026
