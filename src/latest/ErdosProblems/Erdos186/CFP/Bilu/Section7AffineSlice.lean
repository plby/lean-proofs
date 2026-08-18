/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5Theorem56
import ErdosProblems.Erdos186.CFP.Bilu.Section7PlaneSeed

/-!
# Passing Bilu's affine slice back through the Freiman map

The generalized `2n` theorem is applied to the real image of one residue
cell.  This file performs the exact finite pullback: injectivity preserves
the size of both the cell and the selected slice, while every selected
source point maps into the low-dimensional affine plane.  The resulting
object is the direct input to `Section7PlaneSeed` and Proposition 7.4.
-/

namespace Erdos186.CFP.Bilu.Section7AffineSlice

open Set Module Submodule
open Proposition75Data Proposition74Construction SubspaceLattice
open Section7FreimanMap Section7PlaneSeed Section5TwoN
  Section5Theorem56

noncomputable section

/-- The part of `S` whose image lies in `T`. -/
def pullbackFinset {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (S : Finset X) (T : Finset Y) : Finset X := by
  classical
  exact S.filter fun x ↦ f x ∈ T

@[simp]
theorem mem_pullbackFinset {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (S : Finset X) (T : Finset Y) (x : X) :
    x ∈ pullbackFinset f S T ↔ x ∈ S ∧ f x ∈ T := by
  classical
  simp [pullbackFinset]

/-- Pulling back a subset of an image and then mapping forward recovers
that subset exactly. -/
theorem image_pullbackFinset_eq {X Y : Type*}
    [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (S : Finset X) (T : Finset Y)
    (hT : T ⊆ S.image f) :
    (pullbackFinset f S T).image f = T := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_pullbackFinset f S T x |>.mp hx).2
  · intro hy
    obtain ⟨x, hxS, hxy⟩ := Finset.mem_image.mp (hT hy)
    subst y
    exact Finset.mem_image.mpr
      ⟨x, mem_pullbackFinset f S T x |>.mpr ⟨hxS, hy⟩, rfl⟩

/-- An injective map preserves the cardinality of the pulled-back slice. -/
theorem card_pullbackFinset_eq {X Y : Type*}
    [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f)
    (S : Finset X) (T : Finset Y) (hT : T ⊆ S.image f) :
    (pullbackFinset f S T).card = T.card := by
  classical
  calc
    (pullbackFinset f S T).card =
        ((pullbackFinset f S T).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ = T.card := congrArg Finset.card (image_pullbackFinset_eq f S T hT)

/-- An additive embedding carries a finite double sumset to the double
sumset of the image. -/
theorem pairSumset_image_eq_image_pairSumset
    {X Y : Type*} [Add X] [Add Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hfadd : ∀ x y, f (x + y) = f x + f y)
    (S : Finset X) :
    pairSumset (S.image f) = (pairSumset S).image f := by
  classical
  ext z
  rw [mem_pairSumset, Finset.mem_image]
  constructor
  · rintro ⟨fx, hfx, fy, hfy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hfx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hfy
    refine ⟨x + y, mem_pairSumset S (x + y) |>.mpr
      ⟨x, hx, y, hy, rfl⟩, ?_⟩
    exact hfadd x y
  · rintro ⟨xy, hxy, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_pairSumset S xy |>.mp hxy
    exact ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      f y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, (hfadd x y).symm⟩

/-- Consequently an injective additive embedding preserves double-sumset
cardinality. -/
theorem card_pairSumset_image_eq
    {X Y : Type*} [Add X] [Add Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f)
    (hfadd : ∀ x y, f (x + y) = f x + f y) (S : Finset X) :
    (pairSumset (S.image f)).card = (pairSumset S).card := by
  rw [pairSumset_image_eq_image_pairSumset f hfadd S]
  exact Finset.card_image_of_injective _ hf

/-- The real image of one residue cell has exactly the same double-sumset
cardinality as the original cell.  This combines equation (7.4) with the
injective additive embedding of the product lattice in the ambient real
space. -/
theorem card_pairSumset_realResidueCell {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m)) :
    (pairSumset
      ((residueCell a b alpha K).image (freimanRealMap a b))).card =
      (pairSumset (residueCell a b alpha K)).card := by
  have himage :
      (residueCell a b alpha K).image (freimanRealMap a b) =
        (mappedResidueCell a b alpha K).image integralProductReal := by
    classical
    rw [mappedResidueCell, Finset.image_image]
    rfl
  rw [himage,
    card_pairSumset_image_eq integralProductReal
      integralProductReal_injective integralProductReal_add]
  exact card_pairSumset_mappedResidueCell a b alpha K

/-- Source-coordinate version of the affine slice furnished by Theorem
5.6 after applying it to the real Freiman image. -/
structure SourceAffineSlice {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (proportionConstant : ℕ) (S : Finset (Mahler.IntegralPoint m)) where
  sourceSlice : Finset (Mahler.IntegralPoint m)
  sourceSlice_subset : sourceSlice ⊆ S
  plane : AffineSubspace ℝ (Ambient m r)
  dimension_lt : finrank ℝ plane.direction < r
  image_mem_plane : ∀ x ∈ sourceSlice, freimanRealMap a b x ∈ plane
  card_le : S.card ≤ proportionConstant * sourceSlice.card

/-- Exact pullback of an affine-slice witness through the injective real
Freiman map. -/
def sourceAffineSliceOfWitness {m r proportionConstant : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m))
    (W : AffineSliceWitness r proportionConstant
      (S.image (freimanRealMap a b))) :
    SourceAffineSlice a b proportionConstant S where
  sourceSlice := pullbackFinset (freimanRealMap a b) S W.slice
  sourceSlice_subset := by
    intro x hx
    exact (mem_pullbackFinset (freimanRealMap a b) S W.slice x |>.mp hx).1
  plane := W.plane
  dimension_lt := W.dimension_lt
  image_mem_plane := by
    intro x hx
    exact W.slice_mem_plane _
      (mem_pullbackFinset (freimanRealMap a b) S W.slice x |>.mp hx).2
  card_le := by
    have himage : (S.image (freimanRealMap a b)).card = S.card :=
      Finset.card_image_of_injective S (freimanRealMap_injective a b)
    have hpull :
        (pullbackFinset (freimanRealMap a b) S W.slice).card = W.slice.card :=
      card_pullbackFinset_eq (freimanRealMap a b)
        (freimanRealMap_injective a b) S W.slice W.slice_subset
    rw [← himage, hpull]
    exact W.card_le

/-- A pulled-back slice satisfying the cardinal inequality for a nonempty
cell is itself nonempty. -/
theorem SourceAffineSlice.sourceSlice_nonempty {m r proportionConstant : ℕ}
    {a : Fin r → EuclideanSpace ℝ (Fin m)} {b : Fin r → ℝ}
    {S : Finset (Mahler.IntegralPoint m)}
    (W : SourceAffineSlice a b proportionConstant S)
    (hS : S.Nonempty) :
    W.sourceSlice.Nonempty := by
  rw [← Finset.card_pos]
  by_contra hzero
  have hzero' : W.sourceSlice.card = 0 := Nat.eq_zero_of_not_pos hzero
  have hcard := W.card_le
  rw [hzero', mul_zero] at hcard
  have hpos := Finset.card_pos.mpr hS
  omega

/-- The pulled-back slice supplies Proposition 7.4's plane seed directly. -/
theorem SourceAffineSlice.exists_planeSeed {m r proportionConstant : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    {a : Fin r → EuclideanSpace ℝ (Fin m)} {b : Fin r → ℝ}
    {S : Finset (Mahler.IntegralPoint m)}
    (W : SourceAffineSlice a b proportionConstant S)
    (hS : ∀ x ∈ S, integralReal x ∈ B) :
    ∃ planeSeed : Finset (Ambient m r),
      (∀ z ∈ planeSeed, z ∈ distortionBody B a) ∧
      (∀ z ∈ planeSeed, z ∈ ambientProductIntegralPoints m r) ∧
      planeSeed.card + m < m + r ∧
      Submodule.span ℝ (planeSeed : Set (Ambient m r)) =
        vectorSpan ℝ
          (freimanRealMap a b ''
            (W.sourceSlice : Set (Mahler.IntegralPoint m))) := by
  apply Section7PlaneSeed.exists_planeSeed_of_affineSlice
    hbalanced hconvex a b W.sourceSlice W.plane
  · intro x hx
    exact hS x (W.sourceSlice_subset hx)
  · exact W.image_mem_plane
  · exact W.dimension_lt

/-- The exact Section 5.6-to-Section 7 handoff.  A residue cell satisfying
the source doubling threshold acquires a large low-dimensional source slice;
both finite cardinalities are transported through the Freiman real map
without loss. -/
theorem exists_sourceAffineSlice_of_rankTwoN
    {m r proportionConstant : ℕ}
    (hTwoN : RankTwoNStatement.{0} r proportionConstant)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m))
    (hcell : (residueCell a b alpha K).Nonempty)
    (hrank : 0 < r)
    (hdouble :
      (pairSumset (residueCell a b alpha K)).card <
        (2 * r - 1) * (residueCell a b alpha K).card) :
    Nonempty (SourceAffineSlice a b proportionConstant
      (residueCell a b alpha K)) := by
  let S := residueCell a b alpha K
  have hrealNonempty : (S.image (freimanRealMap a b)).Nonempty :=
    hcell.image _
  have hrealCard : (S.image (freimanRealMap a b)).card = S.card :=
    Finset.card_image_of_injective S (freimanRealMap_injective a b)
  have hrealDouble :
      (pairSumset (S.image (freimanRealMap a b))).card <
        (2 * r - 1) * (S.image (freimanRealMap a b)).card := by
    change
      (pairSumset
        ((residueCell a b alpha K).image (freimanRealMap a b))).card < _
    rw [card_pairSumset_realResidueCell, hrealCard]
    exact hdouble
  have hrank_le : r ≤ finrank ℝ (Ambient m r) := by
    rw [finrank_ambient]
    omega
  obtain ⟨W⟩ := exists_affineSlice_of_rankTwoN hTwoN
    (S.image (freimanRealMap a b)) hrealNonempty hrank hrank_le hrealDouble
  exact ⟨sourceAffineSliceOfWitness a b S W⟩

end

end Erdos186.CFP.Bilu.Section7AffineSlice

#print axioms Erdos186.CFP.Bilu.Section7AffineSlice.sourceAffineSliceOfWitness
#print axioms Erdos186.CFP.Bilu.Section7AffineSlice.SourceAffineSlice.exists_planeSeed
#print axioms Erdos186.CFP.Bilu.Section7AffineSlice.exists_sourceAffineSlice_of_rankTwoN
