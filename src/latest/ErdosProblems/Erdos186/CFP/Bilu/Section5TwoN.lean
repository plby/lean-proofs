/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section7FreimanMap
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bilu Section 5: Freiman's generalized `2n` theorem

This file develops the finite combinatorial core of Section 5.  The first
result is Bilu Proposition 5.3: a finite set with bounded doubling contains
a proportionally large subset symmetric about a point.  It is proved by
counting ordered pairs in the fibers of the addition map, exactly as in the
source.
-/

namespace Erdos186.CFP.Bilu.Section5TwoN

open Set Module Submodule
open Section7FreimanMap

noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Translation by one point embeds a nonempty finite set in its double
sumset.  This elementary lower bound is the base case of the generalized
`2n` argument. -/
theorem card_le_pairSumset (S : Finset G) (hS : S.Nonempty) :
    S.card ≤ (pairSumset S).card := by
  obtain ⟨x₀, hx₀⟩ := hS
  apply Finset.card_le_card_of_injOn (fun x ↦ x + x₀)
  · intro x hx
    exact mem_pairSumset S (x + x₀) |>.mpr
      ⟨x, hx, x₀, hx₀, rfl⟩
  · intro x _hx y _hy hxy
    exact add_right_cancel hxy

/-- Ordered pairs from `S` whose sum is the prescribed center. -/
def sumPairFiber (S : Finset G) (center : G) : Finset (G × G) :=
  (S.product S).filter fun p ↦ p.1 + p.2 = center

@[simp]
theorem mem_sumPairFiber (S : Finset G) (center : G) (p : G × G) :
    p ∈ sumPairFiber S center ↔
      p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 = center := by
  simp [sumPairFiber, and_assoc]

/-- The source's symmetric subset `S_b`: first coordinates of pairs with
sum equal to `center = 2b`. -/
def symmetricFiber (S : Finset G) (center : G) : Finset G :=
  (sumPairFiber S center).image Prod.fst

@[simp]
theorem mem_symmetricFiber (S : Finset G) (center x : G) :
    x ∈ symmetricFiber S center ↔ x ∈ S ∧ center - x ∈ S := by
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    have hp' := mem_sumPairFiber S center p |>.mp hp
    subst x
    constructor
    · exact hp'.1
    · have : center - p.1 = p.2 := by
        rw [← hp'.2.2]
        abel
      simpa [this] using hp'.2.1
  · rintro ⟨hx, hy⟩
    refine Finset.mem_image.mpr ⟨(x, center - x), ?_, rfl⟩
    apply mem_sumPairFiber S center _ |>.mpr
    refine ⟨hx, hy, ?_⟩
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The fiber is symmetric: reflecting `x` across the half-center gives
another point of the same fiber. -/
theorem symmetricFiber_reflection_mem (S : Finset G) (center : G)
    {x : G} (hx : x ∈ symmetricFiber S center) :
    center - x ∈ symmetricFiber S center := by
  have hx' := mem_symmetricFiber S center x |>.mp hx
  apply mem_symmetricFiber S center (center - x) |>.mpr
  refine ⟨hx'.2, ?_⟩
  convert hx'.1 using 1
  abel

/-- Projection to the first coordinate is injective on a fixed sum fiber. -/
theorem fst_injOn_sumPairFiber (S : Finset G) (center : G) :
    Set.InjOn Prod.fst (sumPairFiber S center : Set (G × G)) := by
  rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ hfst
  have hs₁ := (mem_sumPairFiber S center _ |>.mp h₁).2.2
  have hs₂ := (mem_sumPairFiber S center _ |>.mp h₂).2.2
  change x₁ + y₁ = center at hs₁
  change x₂ + y₂ = center at hs₂
  simp only at hfst
  subst x₂
  apply Prod.ext
  · rfl
  · exact add_left_cancel (hs₁.trans hs₂.symm)

/-- Passing from ordered-pair fibers to symmetric subsets loses no points. -/
@[simp]
theorem card_symmetricFiber (S : Finset G) (center : G) :
    (symmetricFiber S center).card = (sumPairFiber S center).card := by
  exact Finset.card_image_of_injOn (fst_injOn_sumPairFiber S center)

/-- The ordered-pair fibers partition `S × S`. -/
theorem sum_card_sumPairFiber (S : Finset G) :
    ∑ center ∈ pairSumset S, (sumPairFiber S center).card = S.card * S.card := by
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (f := fun p : G × G ↦ p.1 + p.2)
    (s := S.product S) (t := pairSumset S) (by
      intro p hp
      have hp' := Finset.mem_product.mp hp
      exact mem_pairSumset S _ |>.mpr
        ⟨p.1, hp'.1, p.2, hp'.2, rfl⟩)
  simpa [sumPairFiber, Finset.card_product] using hpartition.symm

/-- Maximum-fiber form of Bilu's double counting: some symmetric fiber
has size at least the average over the double sumset. -/
theorem exists_symmetricFiber_card_mul_pairSumset_ge
    (S : Finset G) (hS : S.Nonempty) :
    ∃ center ∈ pairSumset S,
      S.card * S.card ≤
        (pairSumset S).card * (symmetricFiber S center).card := by
  let values : Finset ℕ :=
    (pairSumset S).image fun center ↦ (sumPairFiber S center).card
  have hsumset : (pairSumset S).Nonempty := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨x + x, mem_pairSumset S _ |>.mpr ⟨x, hx, x, hx, rfl⟩⟩
  have hvalues : values.Nonempty := hsumset.image _
  let M : ℕ := values.max' hvalues
  have hMmem : M ∈ values := Finset.max'_mem values hvalues
  obtain ⟨center, hcenter, hcenterM⟩ := Finset.mem_image.mp hMmem
  refine ⟨center, hcenter, ?_⟩
  have hfiber_le : ∀ c ∈ pairSumset S,
      (sumPairFiber S c).card ≤ M := by
    intro c hc
    exact Finset.le_max' values _
      (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  have hsum_le := Finset.sum_le_card_nsmul
    (pairSumset S) (fun c ↦ (sumPairFiber S c).card) M hfiber_le
  rw [sum_card_sumPairFiber] at hsum_le
  rw [nsmul_eq_mul, ← hcenterM, ← card_symmetricFiber] at hsum_le
  exact hsum_le

/-- Bilu Proposition 5.3, in the division-free natural-number form used
later in the Cube Lemma.  Under `|S+S| ≤ tau |S|`, a symmetric subset has
`tau |T| ≥ |S|`. -/
theorem exists_large_symmetricFiber
    (S : Finset G) (hS : S.Nonempty) (tau : ℕ)
    (hdouble : (pairSumset S).card ≤ tau * S.card) :
    ∃ center : G, ∃ T : Finset G,
      T = symmetricFiber S center ∧
      T ⊆ S ∧
      (∀ x ∈ T, center - x ∈ T) ∧
      S.card ≤ tau * T.card := by
  obtain ⟨center, _hcenter, havg⟩ :=
    exists_symmetricFiber_card_mul_pairSumset_ge S hS
  refine ⟨center, symmetricFiber S center, rfl, ?_, ?_, ?_⟩
  · intro x hx
    exact (mem_symmetricFiber S center x |>.mp hx).1
  · intro x hx
    exact symmetricFiber_reflection_mem S center hx
  · have hupper :
        (pairSumset S).card * (symmetricFiber S center).card ≤
          (tau * (symmetricFiber S center).card) * S.card := by
      calc
        (pairSumset S).card * (symmetricFiber S center).card ≤
            (tau * S.card) * (symmetricFiber S center).card :=
          Nat.mul_le_mul_right _ hdouble
        _ = (tau * (symmetricFiber S center).card) * S.card := by ring
    have hmul : S.card * S.card ≤
        (tau * (symmetricFiber S center).card) * S.card := havg.trans hupper
    exact Nat.le_of_mul_le_mul_right hmul (Finset.card_pos.mpr hS)

/-! ## Affine-slice output of Theorem 5.6 -/

section AffineSlice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

/-- The division-free finite output of Bilu's Theorem 5.6.  The constant
`proportionConstant` is uniform in the ambient dimension and in `S`; the
inequality says that at least a `1 / proportionConstant` fraction of `S`
lies in an affine plane of dimension strictly below `rank` (equivalently,
of dimension at most `rank - 1`).  The
finite slice is stored explicitly, which is the form consumed by the
Section 7 residue-cell construction. -/
structure AffineSliceWitness (rank proportionConstant : ℕ)
    (S : Finset V) where
  plane : AffineSubspace ℝ V
  dimension_lt : finrank ℝ plane.direction < rank
  slice : Finset V
  slice_subset : slice ⊆ S
  slice_mem_plane : ∀ x ∈ slice, x ∈ plane
  card_le : S.card ≤ proportionConstant * slice.card

/-- If `S` already has affine dimension below `rank`, the whole set is
the required slice, with sharp proportion constant one. -/
def AffineSliceWitness.of_dimension_lt {rank : ℕ} (S : Finset V)
    (hdim : finrank ℝ (affineSpan ℝ (S : Set V)).direction < rank) :
    AffineSliceWitness rank 1 S where
  plane := affineSpan ℝ (S : Set V)
  dimension_lt := hdim
  slice := S
  slice_subset := Finset.Subset.rfl
  slice_mem_plane := fun _x hx ↦ subset_affineSpan ℝ (S : Set V) hx
  card_le := by simp

/-- A nonempty set of cardinality at most `rank` has affine dimension below
`rank`.  This is the bounded-cardinality base of the induction in
Theorem 5.6. -/
theorem finrank_direction_affineSpan_lt_of_card_le {rank : ℕ}
    (S : Finset V) (hS : S.Nonempty) (hcard : S.card ≤ rank) :
    finrank ℝ (affineSpan ℝ (S : Set V)).direction < rank := by
  let : Nonempty {x // x ∈ S} := hS.to_subtype
  have hrange :
      Set.range (fun x : {x // x ∈ S} ↦ (x : V)) = (S : Set V) := by
    ext x
    simp
  have hdim := finrank_vectorSpan_range_add_one_le ℝ
    (fun x : {x // x ∈ S} ↦ (x : V))
  rw [hrange] at hdim
  have hcard' :
      Fintype.card {x // x ∈ S} = S.card := Fintype.card_coe S
  rw [hcard'] at hdim
  rw [direction_affineSpan]
  omega

/-- The bounded-cardinality branch of Bilu's Theorem 5.6, with no
doubling hypothesis needed. -/
theorem exists_affineSlice_of_card_le {rank : ℕ}
    (S : Finset V) (hS : S.Nonempty) (hcard : S.card ≤ rank) :
    Nonempty (AffineSliceWitness rank 1 S) := by
  exact ⟨AffineSliceWitness.of_dimension_lt S
    (finrank_direction_affineSpan_lt_of_card_le S hS hcard)⟩

end AffineSlice

end

end Erdos186.CFP.Bilu.Section5TwoN

#print axioms Erdos186.CFP.Bilu.Section5TwoN.exists_large_symmetricFiber
#print axioms Erdos186.CFP.Bilu.Section5TwoN.exists_affineSlice_of_card_le
