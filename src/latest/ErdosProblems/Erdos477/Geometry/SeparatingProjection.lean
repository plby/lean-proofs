/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Choosing a linear projection separating finitely many points.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

variable {K : Type*} [Field K] [Infinite K]

/-- A shear can separate any finite set of plane points while avoiding any
prescribed finite set of slopes. -/
theorem exists_separating_slope (S : Finset (K × K)) (T : Finset K) :
    ∃ a : K, a ∉ T ∧ Set.InjOn (fun z : K × K => z.1 + a * z.2) (S : Set (K × K)) := by
  classical
  let pairs := (S ×ˢ S).filter (fun z => z.1.2 ≠ z.2.2)
  let bad := pairs.image (fun z => (z.2.1 - z.1.1) / (z.1.2 - z.2.2))
  obtain ⟨a, ha⟩ := (T ∪ bad).exists_notMem
  have hT : a ∉ T := fun h => ha (Finset.mem_union_left _ h)
  have hbad : a ∉ bad := fun h => ha (Finset.mem_union_right _ h)
  refine ⟨a, hT, ?_⟩
  intro z hz w hw heq
  change z.1 + a * z.2 = w.1 + a * w.2 at heq
  by_cases hy : z.2 = w.2
  · apply Prod.ext
    · rw [hy] at heq
      exact add_right_cancel heq
    · exact hy
  · have hslope : a = (w.1 - z.1) / (z.2 - w.2) := by
      apply (eq_div_iff (sub_ne_zero.mpr hy)).mpr
      linear_combination heq
    apply (hbad ?_).elim
    exact Finset.mem_image.mpr ⟨(z, w),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hw⟩, hy⟩, hslope.symm⟩

theorem exists_separating_second_slope (S : Finset (K × K)) :
    ∃ a : K, Set.InjOn (fun z : K × K => z.2 + a * z.1) (S : Set (K × K)) := by
  classical
  obtain ⟨a, _, ha⟩ := exists_separating_slope (S.image Prod.swap) ∅
  refine ⟨a, ?_⟩
  intro z hz w hw hzw
  have h := ha (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    (Finset.mem_image.mpr ⟨w, hw, rfl⟩) hzw
  exact Prod.swap_injective h

#print axioms exists_separating_slope
-- 'Erdos477.Geometry.exists_separating_slope' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
