import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLocalFrames
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore

/-!
# Unit-valued transitions of the native canonical bundle

The canonical atlas already supplies the genuine reverse-Jacobian transition
functions.  This file records these functions as units on their actual chart
overlaps and packages them as holomorphic transition data.  The coefficient
comparison below is an identity in the original canonical bundle's local
trivializations, not an identification with a newly chosen bundle.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.NativeTransitions

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (M : Type*) [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]

/-- On an actual overlap this is the determinant of the reversed tangent
coordinate change.  Its value outside the overlap is immaterial. -/
def transition (i j : atlas Model M) (x : M) : ℂˣ := by
  classical
  exact if hx : x ∈ i.val.source ∩ j.val.source then
    Units.mk0 (Atlas.jacobian M j i x) (Atlas.jacobian_ne_zero M j i hx.2 hx.1)
  else 1

theorem transition_val_eq (i j : atlas Model M) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source) :
    (transition M i j x : ℂ) = Atlas.jacobian M j i x := by
  simp only [transition, dif_pos hx, Units.val_mk0]

theorem transition_val_eq_fderiv (i j : atlas Model M) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source) :
    (transition M i j x : ℂ) =
      LinearMap.det (fderiv ℂ (i.val ∘ j.val.symm) (j.val x)).toLinearMap := by
  rw [transition_val_eq M i j hx, Atlas.jacobian_eq_fderiv]

theorem transition_val_eq_inverse_jacobian (i j : atlas Model M) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source) :
    (transition M i j x : ℂ) =
      (LinearMap.det (fderiv ℂ (j.val ∘ i.val.symm) (i.val x)).toLinearMap)⁻¹ := by
  rw [transition_val_eq M i j hx, Atlas.jacobian_reverse M i j hx.1 hx.2,
    Atlas.jacobian_eq_fderiv]

theorem transition_self (i : atlas Model M) (x : M) (hx : x ∈ i.val.source) :
    transition M i i x = 1 := by
  apply Units.ext
  change (transition M i i x : ℂ) = 1
  rw [transition_val_eq M i i ⟨hx, hx⟩, Atlas.jacobian_self M i hx]

theorem transition_comp (i j k : atlas Model M) (x : M)
    (hx : x ∈ i.val.source ∩ j.val.source ∩ k.val.source) :
    transition M j k x * transition M i j x = transition M i k x := by
  apply Units.ext
  change (transition M j k x : ℂ) * (transition M i j x : ℂ) =
    (transition M i k x : ℂ)
  rw [transition_val_eq M j k ⟨hx.1.2, hx.2⟩,
    transition_val_eq M i j hx.1, transition_val_eq M i k ⟨hx.1.1, hx.2⟩]
  exact (mul_comm _ _).trans
    (Atlas.jacobian_comp M k j i ⟨⟨hx.2, hx.1.2⟩, hx.1.1⟩)

theorem transition_continuousOn (i j : atlas Model M) :
    ContinuousOn (fun x => (transition M i j x : ℂ))
      (i.val.source ∩ j.val.source) := by
  have h : ContinuousOn (Atlas.jacobian M j i) (i.val.source ∩ j.val.source) := by
    simpa only [inter_comm] using Atlas.jacobian_continuousOn M j i
  exact h.congr (fun _ hx => transition_val_eq M i j hx)

theorem transition_holomorphicOn (i j : atlas Model M) :
    ContMDiffOn I I₁ ω (fun x => (transition M i j x : ℂ))
      (i.val.source ∩ j.val.source) := by
  have h : ContMDiffOn I I₁ ω (Atlas.jacobian M j i)
      (i.val.source ∩ j.val.source) := by
    simpa only [inter_comm] using Atlas.jacobian_holomorphicOn M j i
  exact h.congr (fun _ hx => transition_val_eq M i j hx)

/-- Holomorphic transition data on the original manifold atlas. -/
def data : HolomorphicCharacterBundle.TransitionData M (atlas Model M) where
  baseSet i := i.val.source
  isOpen_baseSet i := i.val.open_source
  indexAt := achart Model
  mem_baseSet_at := mem_chart_source Model
  transition := transition M
  transition_self := transition_self M
  transition_comp := transition_comp M
  continuousOn_transition := transition_continuousOn M

@[simp] theorem data_baseSet (i : atlas Model M) :
    (data M).baseSet i = i.val.source := rfl

@[simp] theorem data_indexAt (x : M) : (data M).indexAt x = achart Model x := rfl

@[simp] theorem data_transition (i j : atlas Model M) (x : M) :
    (data M).transition i j x = transition M i j x := rfl

instance data_isHolomorphic : (data M).IsHolomorphic I where
  contMDiffOn_transition := transition_holomorphicOn M

/-- The unit-valued transition acts on the actual scalar coefficients of
any vector in the original native canonical bundle. -/
theorem coefficient_change (i j : atlas Model M) {x : M}
    (hx : x ∈ i.val.source ∩ j.val.source) (v : (Atlas.core M).Fiber x) :
    (transition M i j x : ℂ) * ((Atlas.core M).localTriv i ⟨x, v⟩).2 =
      ((Atlas.core M).localTriv j ⟨x, v⟩).2 := by
  rw [transition_val_eq M i j hx]
  change (Atlas.core M).coordChange i j x
      ((Atlas.core M).coordChange ((Atlas.core M).indexAt x) i x v) =
    (Atlas.core M).coordChange ((Atlas.core M).indexAt x) j x v
  exact (Atlas.core M).coordChange_comp ((Atlas.core M).indexAt x) i j x
    ⟨⟨(Atlas.core M).mem_baseSet_at x, hx.1⟩, hx.2⟩ v

/-- The same coefficient identity in the transition-data interface. -/
theorem data_coefficient_change (i j : atlas Model M) {x : M}
    (hx : x ∈ (data M).baseSet i ∩ (data M).baseSet j)
    (v : (Atlas.core M).Fiber x) :
    ((data M).transition i j x : ℂ) * ((Atlas.core M).localTriv i ⟨x, v⟩).2 =
      ((Atlas.core M).localTriv j ⟨x, v⟩).2 :=
  coefficient_change M i j hx v

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.NativeTransitions
