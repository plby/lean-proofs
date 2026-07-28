import Arxiv.Arxiv2407_19026.TangentChecks1.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_coord_check :
    checkLowerAffineCover (smallCoordSlope β0 β1) (1 / 20)
      cfg 0 bpsSlope = true := by
  native_decide

end TangentRound1Native
end Arxiv2407_19026
