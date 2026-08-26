/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Integer projection directions of bounded size separating a finite fiber.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SeparatingProjection

namespace Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K]

lemma exists_bounded_nat_not_mem (T : Finset K) :
    ∃ a : ℕ, a ≤ T.card ∧ (a : K) ∉ T := by
  classical
  by_contra! h
  let f : Fin (T.card + 1) → T := fun a => ⟨(a.val : K), h a.val (by omega)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    exact Fin.ext (Nat.cast_injective (congrArg Subtype.val hab))
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

/-- At most one slope is forbidden by each pair of distinct second
coordinates. The chosen slope is bounded independently of point heights. -/
theorem exists_bounded_separating_slope (S : Finset (K × K)) (T : Finset K) :
    ∃ a : ℕ, a ≤ T.card + S.card ^ 2 ∧ (a : K) ∉ T ∧
      Set.InjOn (fun z : K × K => z.1 + (a : K) * z.2) (S : Set (K × K)) := by
  classical
  let pairs := (S ×ˢ S).filter (fun z => z.1.2 ≠ z.2.2)
  let bad := pairs.image (fun z => (z.2.1 - z.1.1) / (z.1.2 - z.2.2))
  obtain ⟨a, habound, ha⟩ := exists_bounded_nat_not_mem (T ∪ bad)
  have hbadcard : bad.card ≤ S.card ^ 2 := by
    calc
      _ ≤ pairs.card := Finset.card_image_le
      _ ≤ (S ×ˢ S).card := Finset.card_filter_le _ _
      _ = _ := by rw [Finset.card_product, pow_two]
  have hbound : a ≤ T.card + S.card ^ 2 :=
    habound.trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hbadcard _))
  have hT : (a : K) ∉ T := fun h => ha (Finset.mem_union_left _ h)
  have hbad : (a : K) ∉ bad := fun h => ha (Finset.mem_union_right _ h)
  refine ⟨a, hbound, hT, ?_⟩
  intro z hz w hw heq
  change z.1 + (a : K) * z.2 = w.1 + (a : K) * w.2 at heq
  by_cases hy : z.2 = w.2
  · apply Prod.ext
    · rw [hy] at heq
      exact add_right_cancel heq
    · exact hy
  · have hslope : (a : K) = (w.1 - z.1) / (z.2 - w.2) := by
      apply (eq_div_iff (sub_ne_zero.mpr hy)).mpr
      linear_combination heq
    apply (hbad ?_).elim
    exact Finset.mem_image.mpr ⟨(z, w),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hw⟩, hy⟩, hslope.symm⟩

#print axioms exists_bounded_separating_slope
-- 'Erdos477.Geometry.exists_bounded_separating_slope' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
