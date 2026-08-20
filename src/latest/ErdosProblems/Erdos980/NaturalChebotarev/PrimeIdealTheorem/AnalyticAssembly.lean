import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PoleSubtraction
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.ZeroFreeLine

/-!
# Unconditional analytic input for the prime ideal theorem

This file combines boundary nonvanishing with pole subtraction.  Its result is the exact
closed-half-plane continuation consumed by Wiener--Ikehara.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Complex NumberField Set

noncomputable section

/-- The pole-subtracted logarithmic derivative of a Dedekind zeta function extends
continuously to the closed half-plane `Re s ≥ 1`. -/
theorem exists_continuous_dedekindZeta_logDeriv_sub_pole
    (K : Type*) [Field K] [NumberField K] :
    ∃ G : ℂ → ℂ,
      ContinuousOn G {s | 1 ≤ s.re} ∧
      EqOn G
        (fun s : ℂ ↦ -logDeriv (NumberField.dedekindZeta K) s - 1 / (s - 1))
        {s | 1 < s.re} := by
  simpa only [PoleSubtraction.closedOneHalfPlane, PoleSubtraction.openOneHalfPlane] using
    PoleSubtraction.exists_continuous_poleSubtractedDedekindLogDeriv K
      (fun s hs hs1 ↦ continuedDedekindZeta_ne_zero_of_one_le_re K hs hs1)

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
