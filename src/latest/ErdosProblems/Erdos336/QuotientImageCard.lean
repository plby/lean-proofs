import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

/-- Exact cardinality of saturation by an explicitly finite subgroup,
without requiring the ambient group itself to be finite. -/
theorem card_add_subgroup_eq_quotient_image_mul
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (K : AddSubgroup G) [DecidableEq (G ⧸ K)] (Kfin : Finset G)
    (hKfin : ∀ x, x ∈ Kfin ↔ x ∈ K) (A : Finset G) :
    (A + Kfin).card =
      (A.image (QuotientAddGroup.mk' K)).card * Kfin.card := by
  classical
  let q : G →+ (G ⧸ K) := QuotientAddGroup.mk' K
  let S := A + Kfin
  let C := A.image q
  have hmaps : (S : Set G).MapsTo q C := by
    intro x hx
    obtain ⟨a, ha, k, hk, rfl⟩ := Finset.mem_add.mp hx
    apply Finset.mem_image.mpr
    refine ⟨a, ha, ?_⟩
    rw [q.map_add, show q k = 0 from
      (QuotientAddGroup.eq_zero_iff k).mpr ((hKfin k).mp hk)]
    simp
  calc
    S.card = ∑ y ∈ C, (S.filter fun x => q x = y).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ _y ∈ C, Kfin.card := by
      apply Finset.sum_congr rfl
      intro y hy
      obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp hy
      have heq : S.filter (fun x => q x = y) = a +ᵥ Kfin := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_vadd_finset]
        constructor
        · rintro ⟨hxS, hqx⟩
          refine ⟨x - a, ?_, by simp [vadd_eq_add]⟩
          apply (hKfin (x - a)).mpr
          apply (QuotientAddGroup.eq_zero_iff (x - a)).mp
          change q (x - a) = 0
          rw [q.map_sub, hqx, hay, sub_self]
        · rintro ⟨k, hk, rfl⟩
          refine ⟨?_, ?_⟩
          · apply Finset.mem_add.mpr
            exact ⟨a, ha, k, hk, by simp [vadd_eq_add]⟩
          · change q (a + k) = y
            rw [q.map_add, show q k = 0 from
                (QuotientAddGroup.eq_zero_iff k).mpr ((hKfin k).mp hk),
              add_zero, hay]
      rw [heq, Finset.card_vadd_finset]
    _ = C.card * Kfin.card := by
      rw [Finset.sum_const_nat]
      intro y hy
      rfl

end Erdos336
