import Arxiv.Arxiv2407_19026.TangentChecks1Front.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma plateau_high_check :
    checkLowerAffineCover (plateauLogHigh β0 β1 plateauT) 0
      cfg (269 / 1000) plateauMedium = true := by
  native_decide

end TangentRound1Native
end Arxiv2407_19026
