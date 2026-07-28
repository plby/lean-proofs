import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace Beta0Affine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma blue_check :
    LeanCert.Validity.checkLowerAffineCover blue (1 / 100000)
      cfg 0 zeroBreakpoints = true := by
  native_decide

end Beta0Affine
end Arxiv2407_19026
