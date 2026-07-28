import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace Beta0Affine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma p_lower_check :
    LeanCert.Validity.checkLowerAffineCover p (1 / 2)
      cfg 0 coarseBreakpoints = true := by
  native_decide

end Beta0Affine
end Arxiv2407_19026
