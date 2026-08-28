import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore

/-!
# Actual local frames and their transition convention

The frame is the vector with scalar coordinate one in the actual native
bundle trivialization.  On an overlap the second frame is the first
multiplied by the inverse of the coordinate transition.  This distinction
fixes the sign convention before constructing any integral Chern cocycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open Set Bundle HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M] (A : TransitionData M ι)

/-- The actual vector with coordinate one in the indicated native local trivialization. -/
def localFrame (i : ι) (x : M) : A.core.Fiber x :=
  (A.core.localTriv i).symm x 1

/-- Its scalar in the core's selected fibre coordinate comes from the original transition. -/
theorem localFrame_eq (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    localFrame A i x = (A.transition i (A.indexAt x) x : ℂ) := by
  simpa only [localFrame, mul_one] using A.core_localTriv_fiber_symm i hx (1 : ℂ)

/-- These are genuine nonzero local frames of the actual line-bundle fibres. -/
theorem localFrame_ne_zero (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    localFrame A i x ≠ 0 := by
  rw [localFrame_eq A i hx]
  exact A.transition_ne_zero i (A.indexAt x) x

/-- Frame transition functions are inverse to the native coordinate transition functions. -/
def frameTransition (i j : ι) (x : M) : ℂˣ :=
  (A.transition i j x)⁻¹

/-- The convention is proved by equality of actual fibre vectors, not assigned as a label. -/
theorem localFrame_change (i j : ι) {x : M} (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    localFrame A j x = (frameTransition A i j x : ℂ) • localFrame A i x := by
  rw [localFrame_eq A j hx.2, localFrame_eq A i hx.1]
  simp only [frameTransition, Units.val_inv_eq_inv_val]
  change (A.transition j (A.indexAt x) x : ℂ) =
    (A.transition i j x : ℂ)⁻¹ * (A.transition i (A.indexAt x) x : ℂ)
  have h := congrArg (fun u : ℂˣ => (u : ℂ))
    (A.transition_comp i j (A.indexAt x) x ⟨hx, A.mem_baseSet_at x⟩)
  change (A.transition j (A.indexAt x) x : ℂ) * (A.transition i j x : ℂ) =
    (A.transition i (A.indexAt x) x : ℂ) at h
  rw [← h]
  field_simp [A.transition_ne_zero i j x]

theorem frameTransition_self (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    frameTransition A i i x = 1 := by
  rw [frameTransition, A.transition_self i x hx, inv_one]

/-- The actual frame transitions form their multiplicative Čech cocycle on the original cover. -/
theorem frameTransition_comp (i j k : ι) {x : M}
    (hx : x ∈ A.baseSet i ∩ A.baseSet j ∩ A.baseSet k) :
    frameTransition A i j x * frameTransition A j k x = frameTransition A i k x := by
  simpa only [frameTransition, mul_inv_rev] using
    congrArg Inv.inv (A.transition_comp i j k x hx)

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
