import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace Beta0Affine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma limit_check :
    LeanCert.Validity.checkLowerAffineCover limit (1 / 10000000000)
      cfg (3 / 1000) positiveBreakpoints = true := by
  native_decide

end Beta0Affine
end Arxiv2407_19026
