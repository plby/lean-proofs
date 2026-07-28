import Arxiv.Arxiv2407_19026.TangentPolyChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentPolyNative

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r1Back1_lower_check :
    checkLowerAffineCover r1Back1T (1 / 100000)
      cfg (387 / 1000) r1Back1Bps = true := by
  native_decide

end TangentPolyNative
end Arxiv2407_19026
