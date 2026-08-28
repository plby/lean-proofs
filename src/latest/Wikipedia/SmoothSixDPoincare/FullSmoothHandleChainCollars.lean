import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryDiskCollar
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodySumCollar
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCapCollar
import Wikipedia.SmoothSixDPoincare.SmoothHandleChainCollars

/-! # Propagate actual inward collars through births, interior handles, and caps -/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} {dimension : ℕ}

theorem hasInwardCollar {U V : SmoothBoundaryBody J} {k : ℕ}
    (c : FullSmoothHandleChain J dimension U V k) (hU : U.HasInwardCollar) :
    V.HasInwardCollar := by
  induction c with
  | nil r => exact SmoothBoundaryBody.hasInwardCollar_transport r hU
  | @birth U V W k N _ _ _ D hdim r tail ih =>
      exact ih (SmoothBoundaryBody.hasInwardCollar_transport r
        (U.sum_hasInwardCollar D.space hU D.hasInwardCollar))
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P hdim r tail ih =>
      exact ih (SmoothBoundaryBody.hasInwardCollar_transport r
        (U.attach_hasInwardCollar A n P hU))
  | @cap U V W k N _ _ _ j hj hopen hdim r tail ih =>
      exact ih (SmoothBoundaryBody.hasInwardCollar_transport r
        (U.cap_hasInwardCollar j hj hopen hU))

end Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
