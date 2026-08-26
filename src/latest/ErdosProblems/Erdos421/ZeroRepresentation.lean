import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! # Zero representations dominate translated representations

This is the finite counting inequality used as Proposition ZRD in Kevin
Ford, "Vinogradov's integral and bounds for the Riemann zeta function",
page 12, https://arxiv.org/pdf/1910.08209. The proof here uses finite sums
and the arithmetic-geometric mean inequality, with no analytic input.
-/

namespace Erdos421

open Function

theorem finsum_nat_correlation_le_square {G : Type*} [AddGroup G]
    (a : G → ℕ) (ha : HasFiniteSupport a) (w : G) :
    (∑ᶠ x, a x * a (x - w)) ≤ ∑ᶠ x, a x ^ 2 := by
  have hsq : HasFiniteSupport (fun x ↦ a x ^ 2) :=
    ha.fun_comp (g := fun n : ℕ ↦ n ^ 2) (by simp)
  have hshift : HasFiniteSupport (fun x ↦ a (x - w) ^ 2) :=
    hsq.fun_comp_of_injective (Equiv.subRight w).injective
  have hp : HasFiniteSupport (fun x ↦ a x * a (x - w)) := ha.mul_left _
  have hp2 : HasFiniteSupport (fun x ↦ 2 * (a x * a (x - w))) :=
    hp.fun_comp (g := fun n : ℕ ↦ 2 * n) (by simp)
  have hsum : HasFiniteSupport (fun x ↦ a x ^ 2 + a (x - w) ^ 2) := hsq.add hshift
  have hb := finsum_le_finsum' hp2 hsum (fun x ↦
    (by simpa only [mul_assoc] using two_mul_le_add_sq (a x) (a (x - w))))
  have he : (∑ᶠ x, a (x - w) ^ 2) = ∑ᶠ x, a x ^ 2 :=
    finsum_comp_equiv (Equiv.subRight w) (f := fun x ↦ a x ^ 2)
  rw [← mul_finsum' _ 2 hp, finsum_add_distrib hsq hshift, he] at hb
  omega

section Fibers

variable {X G : Type*} [DecidableEq G]

def fiberCount (S : Finset X) (f : X → G) (b : G) : ℕ :=
  (S.filter (fun x ↦ f x = b)).card

theorem fiberCount_support_subset (S : Finset X) (f : X → G) :
    support (fiberCount S f) ⊆ (S.image f : Set G) := by
  classical
  intro b hb
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hb)
  exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

theorem fiberCount_hasFiniteSupport (S : Finset X) (f : X → G) :
    HasFiniteSupport (fiberCount S f) :=
  (S.image f).finite_toSet.subset (fiberCount_support_subset S f)

variable [AddCommGroup G]

theorem card_difference_fiber_eq_finsum (S : Finset X) (f : X → G) (w : G) :
    ((S ×ˢ S).filter (fun p ↦ f p.1 - f p.2 = w)).card =
      ∑ᶠ b, fiberCount S f b * fiberCount S f (b - w) := by
  classical
  rw [finsum_eq_finsetSum_of_support_subset _ (s := S.image f)]
  · rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p : X × X ↦ f p.1) (t := S.image f) (by
        intro p hp
        exact Finset.mem_image.mpr ⟨p.1,
          (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1, rfl⟩)]
    apply Finset.sum_congr rfl
    intro b _
    have he : (((S ×ˢ S).filter (fun p ↦ f p.1 - f p.2 = w)).filter
        (fun p ↦ f p.1 = b)) =
        (S.filter (fun x ↦ f x = b)) ×ˢ (S.filter (fun y ↦ f y = b - w)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨hx, hy⟩, hd⟩, he⟩
        refine ⟨⟨hx, he⟩, hy, ?_⟩
        apply eq_sub_iff_add_eq.mpr
        calc
          f p.2 + w = w + f p.2 := add_comm _ _
          _ = f p.1 := (sub_eq_iff_eq_add.mp hd).symm
          _ = b := he
      · rintro ⟨⟨hx, he⟩, hy, hd⟩
        refine ⟨⟨⟨hx, hy⟩, ?_⟩, he⟩
        rw [he, hd]
        abel
    rw [he, Finset.card_product]
    rfl
  · intro b hb
    have ha : fiberCount S f b ≠ 0 := by
      intro he
      change fiberCount S f b * fiberCount S f (b - w) ≠ 0 at hb
      exact hb (by rw [he, zero_mul])
    exact fiberCount_support_subset S f ha

/-- For an arbitrary finite domain and arbitrary vector-valued function,
the number of pairs with prescribed difference is largest at zero. -/
theorem card_difference_fiber_le_zero (S : Finset X) (f : X → G) (w : G) :
    ((S ×ˢ S).filter (fun p ↦ f p.1 - f p.2 = w)).card ≤
      ((S ×ˢ S).filter (fun p ↦ f p.1 - f p.2 = 0)).card := by
  rw [card_difference_fiber_eq_finsum, card_difference_fiber_eq_finsum]
  simpa only [sub_zero, ← sq] using
    finsum_nat_correlation_le_square (fiberCount S f) (fiberCount_hasFiniteSupport S f) w

end Fibers

end Erdos421
