import StackExchange.Puzzling139335.DoubleCorner.HalfGerm.Closure

/-!
# Boundary rays of the two normalized forty-five-degree cones

A frontier point belongs to the closed cone and cannot satisfy both defining
inequalities strictly. Thus it lies on one of the two actual boundary rays.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.UnitRay

open AcuteCorner DoubleCorner

/-- Every boundary point of the lower cone is on its horizontal or diagonal ray. -/
theorem cone45_frontier_coordinates {p : Plane} (hp : p ∈ frontier cone45) :
    0 ≤ p 0 ∧ 0 ≤ p 1 ∧ (p 1 = 0 ∨ p 0 = p 1) := by
  have hclosed : IsClosed cone45 := closure_strictCone45 ▸ isClosed_closure
  have hpc : p ∈ cone45 := hclosed.closure_subset (frontier_subset_closure hp)
  refine ⟨le_trans hpc.1 hpc.2, hpc.1, ?_⟩
  by_cases hzero : p 1 = 0
  · exact Or.inl hzero
  by_cases heq : p 0 = p 1
  · exact Or.inr heq
  have hstrict : p ∈ strictCone45 :=
    ⟨lt_of_le_of_ne hpc.1 (Ne.symm hzero), lt_of_le_of_ne hpc.2 (Ne.symm heq)⟩
  have hsub : strictCone45 ⊆ cone45 := fun _ h => ⟨h.1.le, h.2.le⟩
  exact False.elim ((mem_frontier_iff_notMem_interior hpc).mp hp
    ((isOpen_strictCone45.subset_interior_iff.mpr hsub) hstrict))

/-- Every boundary point of the upper cone is on its vertical or diagonal ray. -/
theorem upperCone45_frontier_coordinates {p : Plane} (hp : p ∈ frontier upperCone45) :
    0 ≤ p 0 ∧ 0 ≤ p 1 ∧ (p 0 = 0 ∨ p 0 = p 1) := by
  have hclosed : IsClosed upperCone45 := closure_strictUpperCone45 ▸ isClosed_closure
  have hpc : p ∈ upperCone45 := hclosed.closure_subset (frontier_subset_closure hp)
  refine ⟨hpc.1, le_trans hpc.1 hpc.2, ?_⟩
  by_cases hzero : p 0 = 0
  · exact Or.inl hzero
  by_cases heq : p 0 = p 1
  · exact Or.inr heq
  have hstrict : p ∈ strictUpperCone45 :=
    ⟨lt_of_le_of_ne hpc.1 (Ne.symm hzero), lt_of_le_of_ne hpc.2 heq⟩
  have hsub : strictUpperCone45 ⊆ upperCone45 := fun _ h => ⟨h.1.le, h.2.le⟩
  exact False.elim ((mem_frontier_iff_notMem_interior hpc).mp hp
    ((isOpen_strictUpperCone45.subset_interior_iff.mpr hsub) hstrict))

end Puzzling139335.N6.TwoDouble.UnitRay
