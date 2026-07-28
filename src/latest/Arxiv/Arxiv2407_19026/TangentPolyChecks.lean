import Arxiv.Arxiv2407_19026.TangentPolyChecks.R1ForwardLower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R1ForwardUpper
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R1Back1Lower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R1Back1Upper
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R1Back2Lower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R1Back2Upper
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R2ForwardLower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R2ForwardUpper
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R2Back1Lower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R2Back1Upper
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R2Back2Lower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R2Back2Upper
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R3ForwardLower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R3ForwardUpper
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R3Back1Lower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R3Back1Upper
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R3Back2Lower
import Arxiv.Arxiv2407_19026.TangentPolyChecks.R3Back2Upper

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentPolyNative

open TangentAffine

lemma r1Forward_checks :
    checkLowerAffineCover r1ForwardT (1 / 100000)
        cfg (1 / 10) r1ForwardBps = true ∧
      checkLowerAffineCover (belowOne r1ForwardT) (1 / 100000)
        cfg (1 / 10) r1ForwardBps = true :=
  ⟨r1Forward_lower_check, r1Forward_upper_check⟩

lemma r1Back1_checks :
    checkLowerAffineCover r1Back1T (1 / 100000)
        cfg (387 / 1000) r1Back1Bps = true ∧
      checkLowerAffineCover (belowOne r1Back1T) (1 / 100000)
        cfg (387 / 1000) r1Back1Bps = true :=
  ⟨r1Back1_lower_check, r1Back1_upper_check⟩

lemma r1Back2_checks :
    checkLowerAffineCover r1Back2T (1 / 100000)
        cfg (3 / 5) back2Bps = true ∧
      checkLowerAffineCover (belowOne r1Back2T) (1 / 100000)
        cfg (3 / 5) back2Bps = true :=
  ⟨r1Back2_lower_check, r1Back2_upper_check⟩

lemma r2Forward_checks :
    checkLowerAffineCover r2ForwardT (1 / 100000)
        cfg (1 / 10) r2ForwardBps = true ∧
      checkLowerAffineCover (belowOne r2ForwardT) (1 / 100000)
        cfg (1 / 10) r2ForwardBps = true :=
  ⟨r2Forward_lower_check, r2Forward_upper_check⟩

lemma r2Back1_checks :
    checkLowerAffineCover r2Back1T (1 / 100000)
        cfg (189 / 500) r2Back1Bps = true ∧
      checkLowerAffineCover (belowOne r2Back1T) (1 / 100000)
        cfg (189 / 500) r2Back1Bps = true :=
  ⟨r2Back1_lower_check, r2Back1_upper_check⟩

lemma r2Back2_checks :
    checkLowerAffineCover r2Back2T (1 / 100000)
        cfg (3 / 5) back2Bps = true ∧
      checkLowerAffineCover (belowOne r2Back2T) (1 / 100000)
        cfg (3 / 5) back2Bps = true :=
  ⟨r2Back2_lower_check, r2Back2_upper_check⟩

lemma r3Forward_checks :
    checkLowerAffineCover r3ForwardT (1 / 100000)
        cfg (1 / 10) r3ForwardBps = true ∧
      checkLowerAffineCover (belowOne r3ForwardT) (1 / 100000)
        cfg (1 / 10) r3ForwardBps = true :=
  ⟨r3Forward_lower_check, r3Forward_upper_check⟩

lemma r3Back1_checks :
    checkLowerAffineCover r3Back1T (1 / 100000)
        cfg (3 / 8) r3Back1Bps = true ∧
      checkLowerAffineCover (belowOne r3Back1T) (1 / 100000)
        cfg (3 / 8) r3Back1Bps = true :=
  ⟨r3Back1_lower_check, r3Back1_upper_check⟩

lemma r3Back2_checks :
    checkLowerAffineCover r3Back2T (1 / 100000)
        cfg (3 / 5) back2Bps = true ∧
      checkLowerAffineCover (belowOne r3Back2T) (1 / 100000)
        cfg (3 / 5) back2Bps = true :=
  ⟨r3Back2_lower_check, r3Back2_upper_check⟩

end TangentPolyNative
end Arxiv2407_19026
