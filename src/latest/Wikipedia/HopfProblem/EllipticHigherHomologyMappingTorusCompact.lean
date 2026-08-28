import Wikipedia.HopfProblem.MappingTorusTopology
import Mathlib.Topology.Order.Compact

/-!
# Compactness of the actual mapping torus

Every point of the real-cylinder quotient has a representative with time
in the closed unit interval.  For compact fibre this gives compactness
of the literal mapping torus, with no bundle or manifold hypothesis.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.MappingTorus

variable {X : Type*} [TopologicalSpace X]

/-- Integer deck translation moves every representative into the closed
unit cylinder, retaining its actual quotient point. -/
theorem mk_unitCylinder_surjective (f : X ≃ₜ X) :
    mk f '' ((Icc (0 : ℝ) 1) ×ˢ (univ : Set X)) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective f q
  refine ⟨deck f (-⌊t⌋) (t, x), ?_, mk_deck f (-⌊t⌋) (t, x)⟩
  change (0 ≤ t + ((-⌊t⌋ : ℤ) : ℝ) ∧ t + ((-⌊t⌋ : ℤ) : ℝ) ≤ 1) ∧ True
  push_cast
  exact ⟨⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩, trivial⟩

/-- A compact fibre makes the actual quotient mapping torus compact. -/
instance compactSpace [CompactSpace X] (f : X ≃ₜ X) : CompactSpace (Torus f) where
  isCompact_univ := by
    rw [← mk_unitCylinder_surjective f]
    exact (isCompact_Icc.prod isCompact_univ).image (mk_continuous f)

end Wikipedia.HopfProblem.MappingTorus
