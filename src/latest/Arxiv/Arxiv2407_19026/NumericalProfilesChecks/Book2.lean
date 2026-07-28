import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace Beta0Affine


set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma book_check₂ :
    LeanCert.Validity.checkLowerAffineCover book (1 / 10000000000)
      cfg (1 / 10) bookBreakpoints₂ = true := by
  native_decide

end Beta0Affine
end Arxiv2407_19026
