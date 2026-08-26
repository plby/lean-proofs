import Mathlib

/-! # A finite Cauchy–Schwarz inequality in terms of collisions -/

namespace Erdos941

def collisionPairs {α β : Type*} [DecidableEq β] (S : Finset α) (f : α → β) : Finset (α × α) :=
  (S.product S).filter fun p => f p.1 = f p.2

theorem card_sq_le_image_mul_collisions {α β : Type*} [DecidableEq β] (S : Finset α) (f : α → β) :
    S.card ^ 2 ≤ (S.image f).card * (collisionPairs S f).card := by
  classical
  have hfiber (b : β) :
      ((collisionPairs S f).filter (fun p => f p.1 = b)).card =
        (S.filter (fun x => f x = b)).card ^ 2 := by
    have he : (collisionPairs S f).filter (fun p => f p.1 = b) =
        (S.filter (fun x => f x = b)).product (S.filter (fun x => f x = b)) := by
      ext ⟨x, y⟩
      simp only [collisionPairs, Finset.mem_filter, Finset.mem_product]
      aesop
    rw [he]
    exact (Finset.card_product _ _).trans (pow_two _).symm
  have hmap : ((collisionPairs S f) : Set (α × α)).MapsTo (fun p => f p.1) (S.image f) := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p.1, (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1, rfl⟩
  have hsum : (collisionPairs S f).card =
      ∑ b ∈ S.image f, (S.filter (fun x => f x = b)).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    exact Finset.sum_congr rfl (fun b _ => hfiber b)
  rw [hsum, Finset.card_eq_sum_card_image f S]
  exact sq_sum_le_card_mul_sum_sq

end Erdos941
