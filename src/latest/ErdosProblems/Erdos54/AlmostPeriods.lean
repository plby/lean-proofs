/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import Mathlib

/-!
# Almost periods of a finite subset of a finite abelian group

This file supplies the two elementary almost-period estimates used in the
Conlon--Fox--Pham construction.  If `A` is a finite subset of a finite
abelian group, its expansion under translation by `x` is

`|(A + x) \ A|`.

Thus `x` is a `d`-almost period precisely when this expansion is at most
`d`.  We prove both the counting estimate

`|G_d(A)| (|A| - d) <= |A|^2`

and the triangle inequality which implies that a sum of `k` `d`-almost
periods is a `k*d`-almost period.
-/

namespace Erdos54

open scoped BigOperators

section FiniteAdditiveGroup

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Translation of a finite set by an element on the right. -/
def translate (A : Finset G) (x : G) : Finset G :=
  A.image (fun a => a + x)

@[simp]
theorem card_translate (A : Finset G) (x : G) : (translate A x).card = A.card := by
  exact Finset.card_image_of_injective A (add_left_injective x)

@[simp]
theorem mem_translate {A : Finset G} {x y : G} :
    y ∈ translate A x ↔ y - x ∈ A := by
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨a, ha, hax⟩
    simpa [← hax]
  · intro hy
    refine Finset.mem_image.mpr ⟨y - x, hy, ?_⟩
    simp

@[simp]
theorem translate_zero (A : Finset G) : translate A 0 = A := by
  ext a
  simp

theorem translate_add (A : Finset G) (x y : G) :
    translate (translate A x) y = translate A (x + y) := by
  ext a
  simp [sub_sub, add_comm, add_left_comm, add_assoc]

/-- The number of points newly exposed by translating `A` by `x`. -/
def expansion (A : Finset G) (x : G) : ℕ :=
  (translate A x \ A).card

/-- The notation `e_A(x)` used in CFP for the expansion of `A` by `x`. -/
abbrev e_A (A : Finset G) (x : G) : ℕ := expansion A x

/-- The finite set of translations which expose at most `d` new points. -/
def almostPeriods (A : Finset G) (d : ℕ) : Finset G :=
  Finset.univ.filter (fun x => expansion A x ≤ d)

/-- The notation `G_d(A)` used in CFP for the set of `d`-almost periods. -/
abbrev G_d (A : Finset G) (d : ℕ) : Finset G := almostPeriods A d

@[simp]
theorem mem_almostPeriods {A : Finset G} {d : ℕ} {x : G} :
    x ∈ almostPeriods A d ↔ expansion A x ≤ d := by
  simp [almostPeriods]

@[simp]
theorem zero_mem_almostPeriods (A : Finset G) (d : ℕ) :
    0 ∈ almostPeriods A d := by
  simp [expansion]

theorem almostPeriods_mono {A : Finset G} {d e : ℕ} (hde : d ≤ e) :
    almostPeriods A d ⊆ almostPeriods A e := by
  intro x hx
  exact mem_almostPeriods.mpr ((mem_almostPeriods.mp hx).trans hde)

private def incidencePairs (A H : Finset G) : Finset (G × G) :=
  (H.product A).filter (fun p => p.2 ∈ translate A p.1)

private theorem card_incidencePairs (A H : Finset G) :
    (incidencePairs A H).card = ∑ x ∈ H, (A ∩ translate A x).card := by
  unfold incidencePairs
  rw [Finset.card_filter]
  calc
    (∑ p ∈ H.product A, if p.2 ∈ translate A p.1 then 1 else 0) =
        ∑ x ∈ H, ∑ y ∈ A, if y ∈ translate A x then 1 else 0 :=
      Finset.sum_product H A (fun p => if p.2 ∈ translate A p.1 then 1 else 0)
    _ = ∑ x ∈ H, (A ∩ translate A x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.card_filter]
      congr 1

private theorem card_inter_translate_add_expansion (A : Finset G) (x : G) :
    (A ∩ translate A x).card + expansion A x = A.card := by
  rw [Finset.inter_comm]
  simpa [expansion] using Finset.card_sdiff_add_card_inter (translate A x) A

/-- The boundary definition of expansion agrees with CFP's union definition. -/
theorem card_translate_union (A : Finset G) (x : G) :
    (translate A x ∪ A).card = A.card + expansion A x := by
  have hu := Finset.card_union_add_card_inter (translate A x) A
  have hi := card_inter_translate_add_expansion A x
  rw [card_translate, Finset.inter_comm] at hu
  omega

/-- Characterization of `G_d(A)` in the exact union-cardinality form used by CFP. -/
theorem mem_almostPeriods_iff_card_union_le {A : Finset G} {d : ℕ} {x : G} :
    x ∈ almostPeriods A d ↔ (translate A x ∪ A).card ≤ A.card + d := by
  rw [mem_almostPeriods, card_translate_union]
  omega

private theorem incidencePairs_card_le_square (A H : Finset G) :
    (incidencePairs A H).card ≤ A.card * A.card := by
  let f : G × G → G × G := fun p => (p.2 - p.1, p.2)
  have hf : Set.InjOn f (incidencePairs A H : Set (G × G)) := by
    intro p hp q hq hpq
    change (p.2 - p.1, p.2) = (q.2 - q.1, q.2) at hpq
    injection hpq with hfirst hsecond
    apply Prod.ext
    ·
      rw [hsecond] at hfirst
      exact sub_right_inj.mp hfirst
    · exact hsecond
  have himage : (incidencePairs A H).image f ⊆ A.product A := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    have hp' := Finset.mem_filter.mp hp
    have hpHA := Finset.mem_product.mp hp'.1
    apply Finset.mem_product.mpr
    constructor
    · exact mem_translate.mp hp'.2
    · exact hpHA.2
  calc
    (incidencePairs A H).card = ((incidencePairs A H).image f).card :=
      (Finset.card_image_of_injOn hf).symm
    _ ≤ (A.product A).card := Finset.card_le_card himage
    _ = A.card * A.card := Finset.card_product A A

/-- CFP Lemma 2.6, in a division-free form.

The proof double-counts pairs `(x,a)` with `x` an almost period and both
`a-x` and `a` in `A`. -/
theorem card_almostPeriods_mul_sub_le_square (A : Finset G) (d : ℕ) :
    (almostPeriods A d).card * (A.card - d) ≤ A.card * A.card := by
  calc
    (almostPeriods A d).card * (A.card - d) =
        ∑ _x ∈ almostPeriods A d, (A.card - d) := by
          simp
    _ ≤ ∑ x ∈ almostPeriods A d, (A ∩ translate A x).card := by
      gcongr with x hx
      have hexp := mem_almostPeriods.mp hx
      have hpartition := card_inter_translate_add_expansion A x
      omega
    _ = (incidencePairs A (almostPeriods A d)).card :=
      (card_incidencePairs A (almostPeriods A d)).symm
    _ ≤ A.card * A.card := incidencePairs_card_le_square A (almostPeriods A d)

private theorem boundary_add_subset (A : Finset G) (x y : G) :
    translate A (x + y) \ A ⊆
      translate (translate A x \ A) y ∪ (translate A y \ A) := by
  intro z hz
  have hzxy : z - (x + y) ∈ A := mem_translate.mp (Finset.mem_sdiff.mp hz).1
  have hzA : z ∉ A := (Finset.mem_sdiff.mp hz).2
  by_cases hmiddle : z - y ∈ A
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨mem_translate.mpr hmiddle, hzA⟩)
  · apply Finset.mem_union_left
    apply mem_translate.mpr
    apply Finset.mem_sdiff.mpr
    constructor
    · apply mem_translate.mpr
      simpa [sub_sub, add_comm, add_left_comm, add_assoc] using hzxy
    · simpa using hmiddle

/-- The expansion function satisfies a triangle inequality. -/
theorem expansion_add_le (A : Finset G) (x y : G) :
    expansion A (x + y) ≤ expansion A x + expansion A y := by
  calc
    expansion A (x + y) ≤
        (translate (translate A x \ A) y ∪ (translate A y \ A)).card :=
      Finset.card_le_card (boundary_add_subset A x y)
    _ ≤ (translate (translate A x \ A) y).card + (translate A y \ A).card :=
      Finset.card_union_le _ _
    _ = expansion A x + expansion A y := by
      simp [expansion]

/-- A sum of a list of `d`-almost periods is a `length * d`-almost period. -/
theorem expansion_list_sum_le {A : Finset G} {d : ℕ} (xs : List G)
    (hxs : ∀ x ∈ xs, x ∈ almostPeriods A d) :
    expansion A xs.sum ≤ xs.length * d := by
  induction xs with
  | nil => simp [expansion]
  | cons x xs ih =>
      rw [List.sum_cons]
      calc
        expansion A (x + xs.sum) ≤ expansion A x + expansion A xs.sum :=
          expansion_add_le A x xs.sum
        _ ≤ d + xs.length * d := by
          gcongr
          · exact mem_almostPeriods.mp (hxs x (by simp))
          · exact ih (fun y hy => hxs y (by simp [hy]))
        _ = (x :: xs).length * d := by simp [Nat.succ_mul, Nat.add_comm]

/-- Membership formulation of `expansion_list_sum_le`. -/
theorem list_sum_mem_almostPeriods {A : Finset G} {d : ℕ} (xs : List G)
    (hxs : ∀ x ∈ xs, x ∈ almostPeriods A d) :
    xs.sum ∈ almostPeriods A (xs.length * d) :=
  mem_almostPeriods.mpr (expansion_list_sum_le xs hxs)

/-- Finset-indexed version of CFP Lemma 2.7. -/
theorem finset_sum_mem_almostPeriods {ι : Type*} {A : Finset G} {d : ℕ}
    (s : Finset ι) (z : ι → G) (hz : ∀ i ∈ s, z i ∈ almostPeriods A d) :
    (∑ i ∈ s, z i) ∈ almostPeriods A (s.card * d) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expansion]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
      apply mem_almostPeriods.mpr
      calc
        expansion A (z i + ∑ j ∈ s, z j) ≤
            expansion A (z i) + expansion A (∑ j ∈ s, z j) :=
          expansion_add_le A (z i) (∑ j ∈ s, z j)
        _ ≤ d + s.card * d := by
          gcongr
          · exact mem_almostPeriods.mp (hz i (by simp))
          · exact mem_almostPeriods.mp (ih (fun j hj => hz j (by simp [hj])))
        _ = (s.card + 1) * d := by simp [Nat.add_mul, Nat.add_comm]

end FiniteAdditiveGroup

end Erdos54
