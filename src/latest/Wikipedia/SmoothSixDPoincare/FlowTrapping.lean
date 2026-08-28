import Mathlib.Dynamics.Flow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# From local trapping to global forward invariance

Continuous induction upgrades a short-time trapping property of a closed
set to forward invariance for all times. The interior is then forward
invariant because each time map is a homeomorphism.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) {A : Set X}

/-- A closed set locally preserved in forward time is preserved for every nonnegative time. -/
theorem forwardInvariant_of_local (hA : IsClosed A)
    (hlocal : ∀ x ∈ A, ∃ ε > (0 : ℝ), ∀ t ∈ Icc 0 ε, F t x ∈ A) :
    ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A := by
  intro x hx T hT
  let S : Set ℝ := {t | F t x ∈ A}
  have hS : IsClosed S := hA.preimage (F.continuous continuous_id continuous_const)
  have hzero : (0 : ℝ) ∈ S := by simpa only [S, mem_ofPred_eq, F.map_zero_apply] using hx
  apply (hS.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt hzero hT
  intro s hs
  obtain ⟨ε, hε, hstay⟩ := hlocal (F s x) hs.1
  let δ := min ε (T - s) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (sub_pos.mpr hs.2.2))
  have hδε : δ ≤ ε := (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hs.2.2)))).trans
    (min_le_left _ _)
  have hδT : δ ≤ T - s := (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hs.2.2)))).trans
    (min_le_right _ _)
  refine ⟨s + δ, ?_, by linarith, by linarith⟩
  change F (s + δ) x ∈ A
  rw [add_comm s δ, F.map_add]
  exact hstay δ ⟨hδ.le, hδε⟩

/-- A forward-invariant set has forward-invariant interior. -/
theorem forwardInvariant_interior
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    {x : X} (hx : x ∈ interior A) {t : ℝ} (ht : 0 ≤ t) : F t x ∈ interior A := by
  apply mem_interior.mpr
  refine ⟨F t '' interior A, ?_, (F.toHomeomorph t).isOpenMap _ isOpen_interior, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hforward y (interior_subset hy) t ht
  · exact ⟨x, hx, rfl⟩

/-- Immediate local entry and forward invariance imply entry into the interior at all positive
times. This is the strict crossing property used for continuous stopping times. -/
theorem interior_entry_of_local
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hlocal : ∀ x ∈ A, ∃ ε > (0 : ℝ), ∀ t ∈ Ioc 0 ε, F t x ∈ interior A) :
    ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A := by
  intro x hx t ht
  obtain ⟨ε, hε, hentry⟩ := hlocal x hx
  let δ := min ε t / 2
  have hδ : 0 < δ := half_pos (lt_min hε ht)
  have hδε : δ ≤ ε := (half_le_self (le_of_lt (lt_min hε ht))).trans (min_le_left _ _)
  have hδt : δ ≤ t := (half_le_self (le_of_lt (lt_min hε ht))).trans (min_le_right _ _)
  have hi := forwardInvariant_interior F hforward (hentry δ ⟨hδ, hδε⟩) (sub_nonneg.mpr hδt)
  rw [← F.map_add, sub_add_cancel] at hi
  exact hi

end Wikipedia.SmoothSixDPoincare.FlowConstruction
