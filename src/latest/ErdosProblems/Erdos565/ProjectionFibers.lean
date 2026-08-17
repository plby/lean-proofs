/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-!
# Cardinal estimates for projections with small fibres

The auxiliary hypergraphs in the proof of Erdős problem 565 use a projection
from two labelled copies of a finite vertex set to the original vertex set.
Every fibre of that projection has at most two points.  This file isolates the
finite cardinal arithmetic needed for that construction.

All primary statements are local to a finite set `X`.  Thus they can also be
used when the ambient types are infinite.  The final section specializes them
to the canonical two-layer set
`(Y₀ × {0}) ∪ (Y₁ × {1})`.
-/

open scoped BigOperators

@[expose] public section

namespace Erdos565.ProjectionFibers

variable {V U : Type*}

section General

variable [DecidableEq U]

/-- The fibre of `π` in `X` over `u`. -/
def fiberIn (π : V → U) (X : Finset V) (u : U) : Finset V :=
  X.filter fun v ↦ π v = u

@[simp] theorem mem_fiberIn {π : V → U} {X : Finset V} {u : U} {v : V} :
    v ∈ fiberIn π X u ↔ v ∈ X ∧ π v = u := by
  simp [fiberIn]

/-- Every fibre of `π` which meets `X` has at most `k` points. -/
def FibersBoundedOn (π : V → U) (X : Finset V) (k : ℕ) : Prop :=
  ∀ u ∈ X.image π, (fiberIn π X u).card ≤ k

theorem fibersBoundedOn_iff (π : V → U) (X : Finset V) (k : ℕ) :
    FibersBoundedOn π X k ↔
      ∀ u ∈ X.image π, (X.filter fun v ↦ π v = u).card ≤ k := by
  rfl

/-- A finite set is the disjoint sum of the fibres of any map on that set. -/
theorem card_eq_sum_fibers (π : V → U) (X : Finset V) :
    X.card = ∑ u ∈ X.image π, (fiberIn π X u).card := by
  simpa [fiberIn] using (Finset.card_eq_sum_card_image π X)

/-- If every fibre meeting `X` has size at most `k`, then
`|X| ≤ k |π(X)|`. -/
theorem card_le_card_image_mul (π : V → U) (X : Finset V) (k : ℕ)
    (hπ : FibersBoundedOn π X k) :
    X.card ≤ (X.image π).card * k := by
  rw [card_eq_sum_fibers π X]
  calc
    (∑ u ∈ X.image π, (fiberIn π X u).card) ≤
        ∑ _u ∈ X.image π, k := by
      exact Finset.sum_le_sum fun u hu ↦ hπ u hu
    _ = (X.image π).card * k := by simp

/-- Symmetric multiplication-order version of `card_le_card_image_mul`. -/
theorem card_le_mul_card_image (π : V → U) (X : Finset V) (k : ℕ)
    (hπ : FibersBoundedOn π X k) :
    X.card ≤ k * (X.image π).card := by
  simpa [Nat.mul_comm] using card_le_card_image_mul π X k hπ

/-- The image of a set under a map with fibres of size at most two contains
at least half of the set (with natural-number division). -/
theorem half_card_le_card_image (π : V → U) (X : Finset V)
    (hπ : FibersBoundedOn π X 2) :
    X.card / 2 ≤ (X.image π).card := by
  have h := card_le_mul_card_image π X 2 hπ
  omega

/-- A global fibre bound on a finite ambient type. -/
def FibersBounded [Fintype V] (π : V → U) (k : ℕ) : Prop :=
  ∀ u, ((Finset.univ : Finset V).filter fun v ↦ π v = u).card ≤ k

/-- A global fibre bound restricts to every finite subset. -/
theorem FibersBounded.on_finset [Fintype V] {π : V → U} {k : ℕ}
    (hπ : FibersBounded π k) (X : Finset V) :
    FibersBoundedOn π X k := by
  intro u _hu
  exact (Finset.card_le_card (by
    intro v hv
    simp only [fiberIn, Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_univ v, hv.2⟩)).trans (hπ u)

/-- Global two-point fibres imply the half-image estimate for every finite
subset. -/
theorem half_card_le_card_image_of_global [Fintype V] (π : V → U)
    (hπ : FibersBounded π 2) (X : Finset V) :
    X.card / 2 ≤ (X.image π).card :=
  half_card_le_card_image π X (hπ.on_finset X)

/-- The points of `X` whose projections lie outside `C`. -/
def removedByProjectedContainer (π : V → U) (X : Finset V) (C : Finset U) :
    Finset V :=
  X.filter fun v ↦ π v ∉ C

@[simp] theorem mem_removedByProjectedContainer {π : V → U} {X : Finset V}
    {C : Finset U} {v : V} :
    v ∈ removedByProjectedContainer π X C ↔ v ∈ X ∧ π v ∉ C := by
  simp [removedByProjectedContainer]

/-- Projecting after deleting the inverse image of `C` is exactly deleting
`C` from the projected set. -/
theorem image_removedByProjectedContainer (π : V → U) (X : Finset V)
    (C : Finset U) :
    (removedByProjectedContainer π X C).image π = X.image π \ C := by
  ext u
  simp only [Finset.mem_image, mem_removedByProjectedContainer, Finset.mem_sdiff]
  constructor
  · rintro ⟨v, ⟨hvX, hvC⟩, hvu⟩
    exact ⟨⟨v, hvX, hvu⟩, hvu ▸ hvC⟩
  · rintro ⟨⟨v, hvX, hvu⟩, huC⟩
    exact ⟨v, ⟨hvX, hvu ▸ huC⟩, hvu⟩

/-- A fibre bound on `X` is inherited by the part of `X` which is removed
by a projected container. -/
theorem fibersBoundedOn_removed (π : V → U) (X : Finset V) (C : Finset U)
    (k : ℕ) (hπ : FibersBoundedOn π X k) :
    FibersBoundedOn π (removedByProjectedContainer π X C) k := by
  intro u hu
  apply (Finset.card_le_card ?_).trans
    (hπ u (by
      rw [image_removedByProjectedContainer] at hu
      exact (Finset.mem_sdiff.mp hu).1))
  intro v hv
  have hv' := mem_fiberIn.mp hv
  exact mem_fiberIn.mpr ⟨(mem_removedByProjectedContainer.mp hv'.1).1, hv'.2⟩

/-- Removing the inverse image of a projected set removes at most `k` source
points for every removed projected point. -/
theorem card_removed_le (π : V → U) (X : Finset V) (C : Finset U) (k : ℕ)
    (hπ : FibersBoundedOn π X k) :
    (removedByProjectedContainer π X C).card ≤
      k * (X.image π \ C).card := by
  have h := card_le_mul_card_image π (removedByProjectedContainer π X C) k
    (fibersBoundedOn_removed π X C k hπ)
  rwa [image_removedByProjectedContainer] at h

/-- The form used for the two-layer projection: inverse-image removal costs
at most twice the projected removal. -/
theorem card_removed_le_twice (π : V → U) (X : Finset V) (C : Finset U)
    (hπ : FibersBoundedOn π X 2) :
    (removedByProjectedContainer π X C).card ≤
      2 * (X.image π \ C).card :=
  card_removed_le π X C 2 hπ

end General

section TwoLayers

variable [DecidableEq V]

/-- Two labelled copies of `Y₀` and `Y₁`. -/
def twoLayer (Y₀ Y₁ : Finset V) : Finset (V × Fin 2) :=
  Y₀.product {0} ∪ Y₁.product {1}

@[simp] theorem mem_twoLayer {Y₀ Y₁ : Finset V} {v : V} {i : Fin 2} :
    (v, i) ∈ twoLayer Y₀ Y₁ ↔ (v ∈ Y₀ ∧ i = 0) ∨ (v ∈ Y₁ ∧ i = 1) := by
  simp [twoLayer, eq_comm]

/-- The projection of the two-layer set is the union of its two base sets. -/
theorem image_fst_twoLayer (Y₀ Y₁ : Finset V) :
    (twoLayer Y₀ Y₁).image Prod.fst = Y₀ ∪ Y₁ := by
  ext v
  simp [twoLayer]

/-- The canonical two-layer projection has at most two points in every fibre
of `twoLayer Y₀ Y₁`. -/
theorem fst_fibersBoundedOn_twoLayer (Y₀ Y₁ : Finset V) :
    FibersBoundedOn Prod.fst (twoLayer Y₀ Y₁) 2 := by
  intro v _hv
  apply (Finset.card_le_card ?_).trans
    (show ({(v, 0), (v, 1)} : Finset (V × Fin 2)).card ≤ 2 by simp)
  intro x hx
  have hx' := mem_fiberIn.mp hx
  rcases x with ⟨w, i⟩
  simp only at hx'
  have hwv : w = v := hx'.2
  subst w
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl <;> simp

/-- The overlap `W = Y₀ ∩ Y₁` is contained in the projection of the
two-layer set. -/
theorem inter_subset_image_fst_twoLayer (Y₀ Y₁ : Finset V) :
    Y₀ ∩ Y₁ ⊆ (twoLayer Y₀ Y₁).image Prod.fst := by
  rw [image_fst_twoLayer]
  exact Finset.inter_subset_left.trans Finset.subset_union_left

/-- Inclusion between two-layer sets is exactly coordinatewise inclusion
between their two base layers. -/
theorem twoLayer_subset_twoLayer {Y₀ Y₁ X₀ X₁ : Finset V} :
    twoLayer Y₀ Y₁ ⊆ twoLayer X₀ X₁ ↔ Y₀ ⊆ X₀ ∧ Y₁ ⊆ X₁ := by
  constructor
  · intro h
    constructor
    · intro v hv
      have hmem : (v, (0 : Fin 2)) ∈ twoLayer X₀ X₁ :=
        h (mem_twoLayer.mpr (Or.inl ⟨hv, rfl⟩))
      simpa using hmem
    · intro v hv
      have hmem : (v, (1 : Fin 2)) ∈ twoLayer X₀ X₁ :=
        h (mem_twoLayer.mpr (Or.inr ⟨hv, rfl⟩))
      simpa using hmem
  · rintro ⟨h₀, h₁⟩ x hx
    rcases x with ⟨v, i⟩
    rw [mem_twoLayer] at hx ⊢
    rcases hx with ⟨hv, hi⟩ | ⟨hv, hi⟩
    · exact Or.inl ⟨h₀ hv, hi⟩
    · exact Or.inr ⟨h₁ hv, hi⟩

/-- The two labelled layers are disjoint, so their cardinalities add. -/
theorem card_twoLayer (Y₀ Y₁ : Finset V) :
    (twoLayer Y₀ Y₁).card = Y₀.card + Y₁.card := by
  rw [twoLayer, Finset.card_union_of_disjoint]
  · simp
  · refine Finset.disjoint_left.mpr ?_
    intro x hx0 hx1
    rcases Finset.mem_product.mp hx0 with ⟨_hv0, hi0⟩
    rcases Finset.mem_product.mp hx1 with ⟨_hv1, hi1⟩
    simp only [Finset.mem_singleton] at hi0 hi1
    have : (0 : Fin 2) = 1 := hi0.symm.trans hi1
    norm_num at this

/-- Exact cardinal identity behind the factor two: the only extra source
point over the projection is one extra copy of each point in
`W = Y₀ ∩ Y₁`. -/
theorem card_twoLayer_eq_card_image_add_card_inter (Y₀ Y₁ : Finset V) :
    (twoLayer Y₀ Y₁).card =
      ((twoLayer Y₀ Y₁).image Prod.fst).card + (Y₀ ∩ Y₁).card := by
  rw [card_twoLayer, image_fst_twoLayer]
  exact (Finset.card_union_add_card_inter Y₀ Y₁).symm

/-- Consequently the projection of a two-layer set has at least half as
many points as the set itself. -/
theorem half_card_twoLayer_le_card_image (Y₀ Y₁ : Finset V) :
    (twoLayer Y₀ Y₁).card / 2 ≤
      ((twoLayer Y₀ Y₁).image Prod.fst).card :=
  half_card_le_card_image Prod.fst (twoLayer Y₀ Y₁)
    (fst_fibersBoundedOn_twoLayer Y₀ Y₁)

end TwoLayers

end Erdos565.ProjectionFibers
