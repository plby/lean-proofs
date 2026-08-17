/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/
module

public import ErdosProblems.Erdos179.AddCombi.Mathlib.Data.Finset.Density
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Additive.Convolution

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Additive energy

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## Main declarations

* `Finset.addEnergy'`: The additive energy of two finsets in an additive group.
* `Finset.mulEnergy'`: The multiplicative energy of two finsets in a group.

## Notation

The following notations are defined in the `Combinatorics.Additive` scope:
* `E[s, t]` for `Finset.addEnergy' s t`.
* `Eₘ[s, t]` for `Finset.mulEnergy' s t`.
* `E[s]` for `E[s, s]`.
* `Eₘ[s]` for `Eₘ[s, s]`.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (fun x : (G × G) × G × G ↦ x.1.1 * x.2.1 = x.1.2 * x.2.2)`
(whose density in `G × G × G` is `mulEnergy' s t`) as a standalone definition.
-/

open scoped BigOperators Pointwise

public section

variable {G : Type*} [Fintype G] [DecidableEq G]

namespace Finset
section Group
variable [Group G] {s s₁ s₂ t t₁ t₂ : Finset G}

/-- The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of
quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`.

The notation `Eₘ[s, t]` is available in scope `Combinatorics.Additive`. -/
@[expose, to_additive
/-- The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`.

The notation `E[s, t]` is available in scope `Combinatorics.Additive`. -/]
def mulEnergy' (s t : Finset G) : ℚ≥0 :=
  #{x ∈ ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 * x.2.1 = x.1.2 * x.2.2} / Fintype.card G ^ 3

/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "Eₘ[" s ", " t "]" => Finset.mulEnergy' s t

/-- The additive energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "E[" s ", " t "]" => Finset.addEnergy' s t

/-- The multiplicative energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "Eₘ[" s "]" => Finset.mulEnergy' s s

/-- The additive energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "E[" s "]" => Finset.addEnergy' s s

open scoped Combinatorics.Additive'

@[to_additive (attr := gcongr)]
lemma mulEnergy'_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : Eₘ[s₁, t₁] ≤ Eₘ[s₂, t₂] := by
  unfold mulEnergy'; gcongr

@[to_additive] lemma mulEnergy'_mono_left (hs : s₁ ⊆ s₂) : Eₘ[s₁, t] ≤ Eₘ[s₂, t] :=
  mulEnergy'_mono hs Subset.rfl

@[to_additive] lemma mulEnergy'_mono_right (ht : t₁ ⊆ t₂) : Eₘ[s, t₁] ≤ Eₘ[s, t₂] :=
  mulEnergy'_mono Subset.rfl ht

@[to_additive] lemma dens_mul_dens_le_mulEnergy' : s.dens * t.dens / Fintype.card G ≤ Eₘ[s, t] := by
  rw [← dens_product]
  simp only [dens, ← Nat.cast_mul, Fintype.card_prod, div_div, mulEnergy', pow_succ, pow_zero,
    one_mul]
  gcongr
  exact card_le_card_of_injOn (fun x => ((x.1, x.1), x.2, x.2)) (by simp [Set.MapsTo]) (by simp)

@[to_additive] lemma dens_sq_le_mulEnergy'_self : s.dens ^ 2 / Fintype.card G ≤ Eₘ[s] :=
  sq s.dens ▸ dens_mul_dens_le_mulEnergy'

@[to_additive] lemma mulEnergy'_pos (hs : s.Nonempty) (ht : t.Nonempty) : 0 < Eₘ[s, t] := by
  grw [← dens_mul_dens_le_mulEnergy']; positivity

@[to_additive] lemma mulEnergy'_self_pos (hs : s.Nonempty) : 0 < Eₘ[s] :=
  mulEnergy'_pos hs hs

variable (s t)

@[to_additive (attr := simp)] lemma mulEnergy'_empty_left : Eₘ[∅, t] = 0 := by simp [mulEnergy']
@[to_additive (attr := simp)] lemma mulEnergy'_empty_right : Eₘ[s, ∅] = 0 := by simp [mulEnergy']

variable {s t}

@[to_additive (attr := simp)]
lemma mulEnergy'_pos_iff : 0 < Eₘ[s, t] ↔ s.Nonempty ∧ t.Nonempty where
  mp h := by by_contra! +distrib rfl | rfl <;> simp at h
  mpr h := mulEnergy'_pos h.1 h.2

@[to_additive (attr := simp)]
lemma mulEnergy'_eq_zero_iff : Eₘ[s, t] = 0 ↔ s = ∅ ∨ t = ∅ := by
  simp [← zero_le.not_lt_iff_eq', imp_iff_or_not, or_comm]

@[to_additive] lemma mulEnergy'_self_pos_iff : 0 < Eₘ[s] ↔ s.Nonempty := by
  simp

@[to_additive] lemma mulEnergy'_self_eq_zero_iff : Eₘ[s] = 0 ↔ s = ∅ := by
  simp

lemma addEnergy'_eq_card_filter {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]
    (s t : Finset G) :
    E[s, t] =
      #{x ∈ ((s ×ˢ t) ×ˢ s ×ˢ t) | x.1.1 + x.1.2 = x.2.1 + x.2.2} / Fintype.card G ^ 3 := by
  unfold addEnergy'
  congr 2
  exact card_equiv (.prodProdProdComm _ _ _ _) (by simp [and_and_and_comm])

-- TODO: Why does `to_additive` fail here?
@[to_additive existing] lemma mulEnergy'_eq_card_filter (s t : Finset G) :
    Eₘ[s, t] =
      #{x ∈ ((s ×ˢ t) ×ˢ s ×ˢ t) | x.1.1 * x.1.2 = x.2.1 * x.2.2} / Fintype.card G ^ 3 := by
  unfold mulEnergy'
  congr 2
  exact card_equiv (.prodProdProdComm _ _ _ _) (by simp [and_and_and_comm])

set_option backward.isDefEq.respectTransparency false in
lemma addEnergy'_eq_sum_sq' {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G] (s t : Finset G) :
    E[s, t] = (∑ a ∈ s + t, s.addConvolution t a ^ 2) / Fintype.card G ^ 3 := by
  simp_rw [addEnergy'_eq_card_filter, sq, addConvolution, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add unsafe add_mem_add)

set_option backward.isDefEq.respectTransparency false in
@[to_additive existing] lemma mulEnergy'_eq_sum_sq' (s t : Finset G) :
    Eₘ[s, t] = (∑ a ∈ s * t, s.convolution t a ^ 2) / Fintype.card G ^ 3 := by
  simp_rw [mulEnergy'_eq_card_filter, sq, convolution, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add unsafe mul_mem_mul)

lemma addEnergy'_eq_sum_sq {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G] (s t : Finset G) :
    E[s, t] = (∑ a, #{xy ∈ s ×ˢ t | xy.1 + xy.2 = a} ^ 2) / Fintype.card G ^ 3 := by
  rw [addEnergy'_eq_sum_sq']
  congr 2
  exact Fintype.sum_subset <| by simp

@[to_additive existing] lemma mulEnergy'_eq_sum_sq (s t : Finset G) :
    Eₘ[s, t] = (∑ a, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = a} ^ 2) / Fintype.card G ^ 3 := by
  rw [mulEnergy'_eq_sum_sq']
  congr 2
  exact Fintype.sum_subset <| by simp

@[to_additive card_sq_le_card_mul_addEnergy']
lemma card_sq_le_card_mul_mulEnergy' (s t u : Finset G) :
    {xy ∈ s ×ˢ t | xy.1 * xy.2 ∈ u}.dens ^ 2 ≤ u.dens * Eₘ[s, t] := by
  simp only [dens, Fintype.card_prod, Nat.cast_mul, mulEnergy'_eq_sum_sq', Nat.cast_sum,
    Nat.cast_pow]
  field_simp
  norm_cast
  calc
    _ = (∑ c ∈ u, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c}) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ ≤ #u * ∑ c ∈ u, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) _ 1 _
    _ ≤ #u * ∑ c ∈ s * t, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        refine mul_le_mul_right (sum_le_sum_of_ne_zero ?_) _
        aesop (add simp [filter_eq_empty_iff]) (add unsafe mul_mem_mul)

@[to_additive le_card_add_mul_addEnergy'] lemma le_card_mul_mul_mulEnergy' (s t : Finset G) :
    s.dens ^ 2 * t.dens ^ 2 ≤ (s * t).dens * Eₘ[s, t] := by
  grw [← card_sq_le_card_mul_mulEnergy']
  simp only [dens, Fintype.card_prod, Nat.cast_mul]
  field_simp
  norm_cast
  rw [filter_eq_self.2, card_product, mul_pow]; aesop (add unsafe mul_mem_mul)

end Group

open scoped Combinatorics.Additive'

section CommGroup
variable [CommGroup G]

@[to_additive] lemma mulEnergy'_comm (s t : Finset G) : Eₘ[s, t] = Eₘ[t, s] := by
  rw [mulEnergy', ← Finset.card_map (Equiv.prodComm _ _).toEmbedding, map_filter]
  simp [-Finset.card_map, mulEnergy', mul_comm, map_eq_image]

end CommGroup

section CommGroup
variable [CommGroup G] (s t : Finset G)

@[to_additive (attr := simp)]
lemma mulEnergy'_univ_left : Eₘ[univ, t] = t.dens ^ 2 := by
  simp only [mulEnergy', univ_product_univ, dens]
  field_simp
  norm_cast
  simp only [Fintype.card, sq, ← card_product]
  let f : G × G × G → (G × G) × G × G := fun x => ((x.1 * x.2.2, x.1 * x.2.1), x.2)
  have : (↑((univ : Finset G) ×ˢ t ×ˢ t) : Set (G × G × G)).InjOn f := by aesop
  rw [← card_image_of_injOn this]
  congr with a
  simp only [mem_filter, mem_product, mem_univ, true_and, mem_image,
    Prod.exists]
  refine ⟨fun h => ⟨a.1.1 * a.2.2⁻¹, _, _, h.1, by simp [f, mul_right_comm, h.2]⟩, ?_⟩
  grind

@[to_additive (attr := simp)]
lemma mulEnergy'_univ_right : Eₘ[s, univ] = s.dens ^ 2 := by
  rw [mulEnergy'_comm, mulEnergy'_univ_left]

end CommGroup
end Finset
