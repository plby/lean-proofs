import Arxiv.Arxiv2407_19026.TangentChecks3Front.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_coord_check :
    checkLowerAffineCover (smallCoordSlope β2 β3) (1 / 20)
      cfg 0 smallCoordRefined = true := by
  native_decide

end TangentRound3Native
end Arxiv2407_19026
