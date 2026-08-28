import Wikipedia.SmoothSixDPoincare.FlowStoppingTime
import Mathlib.Topology.Homotopy.Equiv

/-!
# Deformation retraction by the continuous first-entry time

For an absorbing closed subset of a forward-invariant region, the actual
flow gives a strong deformation retraction whenever every trajectory hits
the subset and the boundary is crossed strictly.
-/

noncomputable section

open Set ContinuousMap
open scoped Topology unitInterval

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) {A B : Set X}
  (hA : IsClosed A)
  (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
  (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
  (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A)

/-- The actual first-entry retraction onto the closed absorbing subset. -/
def entryRetraction : C(B, A) where
  toFun x := ⟨F (entryTime F A x.1) x.1, flow_entryTime_mem F hA (hhit x.1 x.2)⟩
  continuous_toFun := (F.continuous
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_entryTime F hA hforward hentry hhit))
    continuous_subtype_val).subtype_mk _

variable (hsub : A ⊆ B)
  (hregion : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B)

/-- The entry retraction is stationary on the absorbing subset. -/
theorem entryRetraction_inclusion (x : A) :
    entryRetraction F hA hforward hentry hhit (ContinuousMap.inclusion hsub x) = x := by
  apply Subtype.ext
  change F (entryTime F A x.1) x.1 = x.1
  rw [entryTime_eq_zero F x.2, F.map_zero_apply]

/-- The flow stopped at a continuously varying first-entry time is a strong deformation. -/
def entryDeformation :
    (ContinuousMap.id B).HomotopyRel
      ((ContinuousMap.inclusion hsub).comp (entryRetraction F hA hforward hentry hhit))
      {x : B | x.1 ∈ A} where
  toFun q := ⟨F (q.1.1 * entryTime F A q.2.1) q.2.1,
    hregion q.2.1 q.2.2 _ (mul_nonneg q.1.2.1 (entryTime_nonneg F (hhit q.2.1 q.2.2)))⟩
  continuous_toFun := (F.continuous
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuousOn_iff_continuous_domRestrict.mp
        (continuousOn_entryTime F hA hforward hentry hhit)).comp continuous_snd))
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change F ((0 : ℝ) * entryTime F A x.1) x.1 = x.1
    rw [zero_mul, F.map_zero_apply]
  map_one_left x := by
    apply Subtype.ext
    change F ((1 : ℝ) * entryTime F A x.1) x.1 = F (entryTime F A x.1) x.1
    rw [one_mul]
  prop' u x hx := by
    apply Subtype.ext
    change F (u.1 * entryTime F A x.1) x.1 = x.1
    rw [entryTime_eq_zero F (A := A) (show x.1 ∈ A from hx), mul_zero, F.map_zero_apply]

/-- The inclusion of the absorbing subset is a native homotopy equivalence. -/
def entryHomotopyEquiv : A ≃ₕ B where
  toFun := ContinuousMap.inclusion hsub
  invFun := entryRetraction F hA hforward hentry hhit
  left_inv := by
    have heq : (entryRetraction F hA hforward hentry hhit).comp (ContinuousMap.inclusion hsub) =
        ContinuousMap.id A := by
      apply ContinuousMap.ext
      intro x
      exact entryRetraction_inclusion F hA hforward hentry hhit hsub x
    rw [heq]
  right_inv := ⟨(entryDeformation F hA hforward hentry hhit hsub hregion).toHomotopy.symm⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
