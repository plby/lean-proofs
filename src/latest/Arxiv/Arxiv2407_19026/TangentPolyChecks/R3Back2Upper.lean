import Arxiv.Arxiv2407_19026.TangentPolyChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentPolyNative

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r3Back2_upper_check :
    checkLowerAffineCover (belowOne r3Back2T) (1 / 100000)
      cfg (3 / 5) back2Bps = true := by
  native_decide

end TangentPolyNative
end Arxiv2407_19026
