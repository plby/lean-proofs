import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero.Retraction
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero.RadialTransfer

/-!
# A Jordan boundary winds nontrivially about every interior point

The punctured plane retracts to the actual Jordan boundary parameter, so its
once-around loop cannot contract. A contraction of the angular direction would
give precisely such a contraction by polar reconstruction.
-/

open Set Schoenflies unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero

noncomputable section

open RadialTransfer

/-- The once-around Jordan loop does not contract while avoiding an interior
point. The theorem concerns the supplied parametrization, not a replacement
polygon or a chosen orientation. -/
theorem boundaryLoop_not_homotopic_const {f : AddCircle (1 : ℝ) → Plane}
    (hf : Continuous f) (hfi : Function.Injective f) {x : Plane}
    (hx : x ∈ inside (range f)) :
    ¬ (puncturedPath x (boundaryLoop f hf) (boundaryLoop_avoids hf hx)).HomotopicRel
      (ContinuousMap.const I
        (puncturedPath x (boundaryLoop f hf) (boundaryLoop_avoids hf hx) 0)) {0, 1} := by
  intro h
  obtain ⟨R, hR⟩ := exists_circle_retraction hf hfi hx
  have hc := h.comp_continuousMap R
  have hloop : R.comp (puncturedPath x (boundaryLoop f hf) (boundaryLoop_avoids hf hx)) =
      JordanCurve.Brouwer.acLoop := by
    ext t
    exact hR ((t : ℝ) : AddCircle (1 : ℝ))
  have hconst : R.comp (ContinuousMap.const I
      (puncturedPath x (boundaryLoop f hf) (boundaryLoop_avoids hf hx) 0)) =
      ContinuousMap.const I (0 : AddCircle (1 : ℝ)) := by
    ext t
    exact hR 0
  rw [hloop, hconst] at hc
  exact JordanCurve.Brouwer.acLoop_not_homotopic hc

/-- The angular loop of an actual Jordan boundary is not nullhomotopic around
any point in the Jordan interior. -/
theorem directionLoop_not_homotopic_const {f : AddCircle (1 : ℝ) → Plane}
    (hf : Continuous f) (hfi : Function.Injective f) {x : Plane}
    (hx : x ∈ inside (range f)) :
    ¬ (directionPath (boundaryLoop f hf) x (boundaryLoop_avoids hf hx)).HomotopicRel
      (ContinuousMap.const I
        (directionPath (boundaryLoop f hf) x (boundaryLoop_avoids hf hx) 0)) {0, 1} := by
  intro h
  exact boundaryLoop_not_homotopic_const hf hfi hx
    (direction_null_implies_punctured_null x (boundaryLoop f hf)
      (boundaryLoop_avoids hf hx) (boundaryLoop_closed f hf) h)

end

end Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero
