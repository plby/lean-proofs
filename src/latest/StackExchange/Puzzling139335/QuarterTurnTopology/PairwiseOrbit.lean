import StackExchange.Puzzling139335.QuarterTurnTopology.Orbit

/-! # Pairwise disjointness of the four translates

For an order-four plane homeomorphism, disjointness from the first and second
translates propagates to every pair of distinct translates.
-/

open Set

namespace Puzzling139335.QuarterTurnTopology

/-- The four translates are pairwise disjoint once the original set misses
both its first and its second translate. -/
theorem pairwise_disjoint_iterate_images (e : Plane ≃ₜ Plane) {T : Set Plane}
    (hfour : ∀ x, e (e (e (e x))) = x)
    (h01 : Disjoint T (e '' T)) (h02 : Disjoint T (e '' (e '' T))) :
    Pairwise fun i j : Fin 4 =>
      Disjoint (((e : Plane → Plane)^[i.val]) '' T)
        (((e : Plane → Plane)^[j.val]) '' T) := by
  have h12 : Disjoint (e '' T) (e '' (e '' T)) :=
    (disjoint_image_iff e.injective).2 h01
  have h23 : Disjoint (e '' (e '' T)) (e '' (e '' (e '' T))) :=
    (disjoint_image_iff e.injective).2 h12
  have h13 : Disjoint (e '' T) (e '' (e '' (e '' T))) :=
    (disjoint_image_iff e.injective).2 h02
  have h30 : Disjoint (e '' (e '' (e '' T))) T := by
    simpa only [fourth_image e hfour] using (disjoint_image_iff e.injective).2 h23
  have h10 := h01.symm
  have h20 := h02.symm
  have h21 := h12.symm
  have h32 := h23.symm
  have h31 := h13.symm
  have h03 := h30.symm
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals
    simp only [Function.iterate_succ, Function.iterate_zero, image_comp, image_id]
    assumption

end Puzzling139335.QuarterTurnTopology
