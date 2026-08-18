/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5GenericProjection
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Pulling an affine slice through Bilu's generic projection

This file formalizes the second half of Bilu's Theorem 5.6.  The generic
quotient preserves the cardinalities of `S` and `S + S`.  More subtly, a
low-dimensional affine slice in the quotient pulls back to a subset whose
*source affine span* is already low-dimensional: simultaneous genericity
rules out dimension lost in the kernel.
-/

namespace Erdos186.CFP.Bilu.Section5ProjectionSlice

open Set Module Submodule
open Section7FreimanMap Section5TwoN Section5GenericProjection

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

local instance quotientDecidableEq (A : Submodule ℝ V) :
    DecidableEq (V ⧸ A) := Classical.decEq _

local instance finiteDimensionalSubmoduleIsClosed (A : Submodule ℝ V) :
    IsClosed (A : Set V) := A.closed_of_finiteDimensional

/-- The points of `S` whose quotient images belong to `T`. -/
def projectedSlice {S : Finset V} {rank : ℕ}
    (P : GenericProjection S rank)
    (T : Finset (V ⧸ P.kernel)) : Finset V :=
  S.filter fun x ↦ P.kernel.mkQ x ∈ T

@[simp]
theorem mem_projectedSlice {S : Finset V} {rank : ℕ}
    (P : GenericProjection S rank)
    (T : Finset (V ⧸ P.kernel)) (x : V) :
    x ∈ projectedSlice P T ↔ x ∈ S ∧ P.kernel.mkQ x ∈ T := by
  rw [projectedSlice, Finset.mem_filter]

/-- Pulling back a subset of the quotient image and mapping forward recovers
that subset exactly. -/
theorem image_projectedSlice_eq {S : Finset V} {rank : ℕ}
    (P : GenericProjection S rank)
    (T : Finset (V ⧸ P.kernel))
    (hT : T ⊆ S.image P.kernel.mkQ) :
    (projectedSlice P T).image P.kernel.mkQ = T := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_projectedSlice P T x |>.mp hx).2
  · intro hy
    obtain ⟨x, hxS, hxy⟩ := Finset.mem_image.mp (hT hy)
    subst y
    exact Finset.mem_image.mpr
      ⟨x, mem_projectedSlice P T x |>.mpr ⟨hxS, hy⟩, rfl⟩

/-- The generic quotient preserves the size of every pulled-back subset of
its image. -/
theorem card_projectedSlice_eq {S : Finset V} {rank : ℕ}
    (P : GenericProjection S rank) (hS : S.Nonempty) (hrank : 0 < rank)
    (T : Finset (V ⧸ P.kernel))
    (hT : T ⊆ S.image P.kernel.mkQ) :
    (projectedSlice P T).card = T.card := by
  have hinj := P.mkQ_injOn hS hrank
  calc
    (projectedSlice P T).card =
        ((projectedSlice P T).image P.kernel.mkQ).card :=
      (Finset.card_image_of_injOn
        (fun x hx y hy hxy ↦ hinj
          (mem_projectedSlice P T x |>.mp hx).1
          (mem_projectedSlice P T y |>.mp hy).1 hxy)).symm
    _ = T.card := congrArg Finset.card (image_projectedSlice_eq P T hT)

/-- The quotient map commutes with the finite double-sumset construction. -/
theorem pairSumset_image_mkQ {S : Finset V} {rank : ℕ}
    (P : GenericProjection S rank) :
    pairSumset (S.image P.kernel.mkQ) =
      (pairSumset S).image P.kernel.mkQ := by
  ext z
  rw [mem_pairSumset, Finset.mem_image]
  constructor
  · rintro ⟨qx, hqx, qy, hqy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hqx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hqy
    exact ⟨x + y, mem_pairSumset S (x + y) |>.mpr
      ⟨x, hx, y, hy, rfl⟩, by simp⟩
  · rintro ⟨xy, hxy, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_pairSumset S xy |>.mp hxy
    exact ⟨P.kernel.mkQ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      P.kernel.mkQ y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, by simp⟩

/-- The generic quotient preserves the cardinality of the double sumset. -/
theorem card_pairSumset_image_mkQ {S : Finset V} {rank : ℕ}
    (P : GenericProjection S rank) (hrank : 0 < rank) :
    (pairSumset (S.image P.kernel.mkQ)).card = (pairSumset S).card := by
  rw [pairSumset_image_mkQ P]
  exact Finset.card_image_of_injOn (P.mkQ_injOn_pairSumset hrank)

/-- If a finite source subset maps into an affine plane of dimension below
`rank`, then its own affine span has dimension below `rank`.  This is the
precise genericity argument in the last paragraph of Bilu's Theorem 5.6. -/
theorem finrank_direction_affineSpan_lt_of_image_mem
    {S : Finset V} {rank : ℕ} (P : GenericProjection S rank)
    (hS : S.Nonempty) (hrank : 0 < rank)
    (T : Finset V) (hTS : T ⊆ S)
    (plane : AffineSubspace ℝ (V ⧸ P.kernel))
    (hdim : finrank ℝ plane.direction < rank)
    (himage : ∀ x ∈ T, P.kernel.mkQ x ∈ plane) :
    finrank ℝ (affineSpan ℝ (T : Set V)).direction < rank := by
  by_cases hT : T.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hT
    let D : Finset V := (T.erase x₀).image fun x ↦ x - x₀
    have hdirection :
        (affineSpan ℝ (T : Set V)).direction =
          Submodule.span ℝ (D : Set V) := by
      rw [direction_affineSpan,
        vectorSpan_eq_span_vsub_finset_right_ne ℝ hx₀]
      rfl
    have hD : D ⊆ differenceFinset (pairSumset S) := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      have hxT : x ∈ T := Finset.mem_of_mem_erase hx
      obtain ⟨z, hz⟩ := hS
      apply mem_differenceFinset (pairSumset S) (x - x₀) |>.mpr
      refine ⟨x + z, mem_pairSumset S (x + z) |>.mpr
        ⟨x, hTS hxT, z, hz, rfl⟩,
        x₀ + z, mem_pairSumset S (x₀ + z) |>.mpr
        ⟨x₀, hTS hx₀, z, hz, rfl⟩, ?_⟩
      abel
    have haffine_le :
        affineSpan ℝ (P.kernel.mkQ '' (T : Set V)) ≤ plane := by
      rw [affineSpan_le]
      rintro y ⟨x, hx, rfl⟩
      exact himage x hx
    have hquotient_dim :
        finrank ℝ
            (affineSpan ℝ (P.kernel.mkQ '' (T : Set V))).direction < rank :=
      lt_of_le_of_lt
        (Submodule.finrank_mono (AffineSubspace.direction_le haffine_le)) hdim
    have hmap_direction :
        (affineSpan ℝ (T : Set V)).direction.map P.kernel.mkQ =
          (affineSpan ℝ (P.kernel.mkQ '' (T : Set V))).direction := by
      calc
        _ = ((affineSpan ℝ (T : Set V)).map
              P.kernel.mkQ.toAffineMap).direction :=
          (AffineSubspace.map_direction
            (f := P.kernel.mkQ.toAffineMap)
            (affineSpan ℝ (T : Set V))).symm
        _ = _ := congrArg AffineSubspace.direction
          (AffineSubspace.map_span P.kernel.mkQ.toAffineMap (T : Set V))
    have hmap :
        finrank ℝ ((Submodule.span ℝ (D : Set V)).map P.kernel.mkQ) < rank := by
      rw [← hdirection, hmap_direction]
      exact hquotient_dim
    have hsource := P.finrank_span_lt_of_map_lt D hD hmap
    rw [← hdirection] at hsource
    exact hsource
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    have hzero :
        (affineSpan ℝ (∅ : Set V)).direction = (⊥ : Submodule ℝ V) := by
      rw [direction_affineSpan, vectorSpan_def]
      simp
    rw [show (((∅ : Finset V) : Set V)) = ∅ by simp]
    rw [hzero, finrank_bot]
    exact hrank

/-- Pull a quotient affine-slice witness back to the source.  Cardinality
and the strict dimension bound are both preserved, although the witnessing
source plane is its affine span rather than the full inverse image plane. -/
def pullbackAffineSlice {S : Finset V} {rank proportionConstant : ℕ}
    (P : GenericProjection S rank) (hS : S.Nonempty) (hrank : 0 < rank)
    (W : AffineSliceWitness rank proportionConstant
      (S.image P.kernel.mkQ)) :
    AffineSliceWitness rank proportionConstant S where
  plane := affineSpan ℝ (projectedSlice P W.slice : Set V)
  dimension_lt :=
    finrank_direction_affineSpan_lt_of_image_mem P hS hrank
      (projectedSlice P W.slice)
      (fun _x hx ↦ (mem_projectedSlice P W.slice _x |>.mp hx).1)
      W.plane W.dimension_lt
      (fun x hx ↦ W.slice_mem_plane _
        (mem_projectedSlice P W.slice x |>.mp hx).2)
  slice := projectedSlice P W.slice
  slice_subset := fun _x hx ↦
    (mem_projectedSlice P W.slice _x |>.mp hx).1
  slice_mem_plane := fun _x hx ↦
    subset_affineSpan ℝ (projectedSlice P W.slice : Set V) hx
  card_le := by
    have hsourceCard : (S.image P.kernel.mkQ).card = S.card :=
      Finset.card_image_of_injOn (P.mkQ_injOn hS hrank)
    have hpullCard : (projectedSlice P W.slice).card = W.slice.card :=
      card_projectedSlice_eq P hS hrank W.slice W.slice_subset
    rw [← hsourceCard, hpullCard]
    exact W.card_le

/-- Nonempty/existential packaging of `pullbackAffineSlice`, ready to apply
after the rank-dimensional generalized `2n` theorem in the quotient. -/
theorem exists_affineSlice_of_quotient
    {S : Finset V} {rank proportionConstant : ℕ}
    (P : GenericProjection S rank) (hS : S.Nonempty) (hrank : 0 < rank)
    (hW : Nonempty (AffineSliceWitness rank proportionConstant
      (S.image P.kernel.mkQ))) :
    Nonempty (AffineSliceWitness rank proportionConstant S) := by
  exact ⟨pullbackAffineSlice P hS hrank hW.some⟩

end

end Erdos186.CFP.Bilu.Section5ProjectionSlice

#print axioms Erdos186.CFP.Bilu.Section5ProjectionSlice.card_pairSumset_image_mkQ
#print axioms Erdos186.CFP.Bilu.Section5ProjectionSlice.finrank_direction_affineSpan_lt_of_image_mem
#print axioms Erdos186.CFP.Bilu.Section5ProjectionSlice.pullbackAffineSlice
#print axioms Erdos186.CFP.Bilu.Section5ProjectionSlice.exists_affineSlice_of_quotient
