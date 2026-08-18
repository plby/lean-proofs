/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Small generalized arithmetic progressions

This file supplies the elementary rank-zero and rank-one progressions used
in the base cases of the Conlon--Fox--Pham argument.  In particular it gives

* the unique shape of a rank-zero GAP;
* a rank-one interval with coefficients `0, ..., length`;
* a homogeneous singleton GAP containing an arbitrary lattice point; and
* the homogeneous segment from `0` to a point, including exact descriptions
  of all of its dilates.

The statements about carriers do not assume properness.  The segment
presentation is proper precisely in the nondegenerate direction needed by
the applications (the forward implication is recorded separately).
-/

namespace Erdos186.CFP.GAPBuilders

open scoped BigOperators

variable {d : ℕ}

/-! ## Rank zero -/

/-- The rank-zero GAP supported at `offset`. -/
def rankZero (offset : LatticePoint d) : GAP d 0 where
  offset := offset
  steps := Fin.elim0
  widths := Fin.elim0
  width_pos := fun i ↦ Fin.elim0 i

@[simp]
theorem rankZero_offset (offset : LatticePoint d) :
    (rankZero offset).offset = offset := rfl

/-- Every rank-zero coordinate evaluates to the offset.  This is phrased for
an arbitrary rank-zero GAP, since its step and width fields have empty
domains. -/
@[simp]
theorem rankZero_coordPoint (P : GAP d 0) (n : P.Coord) :
    P.coordPoint n = P.offset := by
  funext j
  simp [GAP.coordPoint]

/-- Every rank-zero GAP has a singleton carrier. -/
@[simp]
theorem rankZero_carrier (P : GAP d 0) :
    P.carrier = {P.offset} := by
  ext x
  simp [GAP.mem_carrier_iff, eq_comm]

/-- Rank-zero presentations are automatically proper. -/
theorem rankZero_proper (P : GAP d 0) : P.Proper := by
  intro n m _
  funext i
  exact Fin.elim0 i

/-- The displayed volume of a rank-zero GAP is one. -/
@[simp]
theorem rankZero_volume (P : GAP d 0) : P.volume = 1 := by
  simp [GAP.volume]

/-- A rank-zero GAP is homogeneous exactly when its offset is zero. -/
theorem rankZero_homogeneous_iff (P : GAP d 0) :
    P.Homogeneous ↔ P.offset = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    rw [hz]
    funext j
    simp
  · intro hP
    refine ⟨Fin.elim0, ?_⟩
    rw [hP]
    funext j
    simp

/-- The homogeneous rank-zero GAP. -/
def zeroGAP (d : ℕ) : GAP d 0 := rankZero 0

@[simp]
theorem zeroGAP_carrier : (zeroGAP d).carrier = {0} :=
  rankZero_carrier _

theorem zeroGAP_proper : (zeroGAP d).Proper :=
  rankZero_proper _

theorem zeroGAP_homogeneous : (zeroGAP d).Homogeneous :=
  (rankZero_homogeneous_iff _).2 rfl

/-- Dilation of a rank-zero GAP only scales its unique point. -/
@[simp]
theorem rankZero_dilate_carrier (P : GAP d 0) (k : ℕ) :
    (P.dilate k).carrier = {fun j ↦ (k : ℤ) * P.offset j} := by
  exact rankZero_carrier (P.dilate k)

/-! ## Rank one -/

/-- The point with coefficient `n` on a one-dimensional progression. -/
def rankOnePoint (offset step : LatticePoint d) (n : ℕ) : LatticePoint d :=
  fun j ↦ offset j + (n : ℤ) * step j

@[simp]
theorem rankOnePoint_zero (offset step : LatticePoint d) :
    rankOnePoint offset step 0 = offset := by
  funext j
  simp [rankOnePoint]

@[simp]
theorem rankOnePoint_zero_offset (step : LatticePoint d) (n : ℕ) :
    rankOnePoint 0 step n = fun j ↦ (n : ℤ) * step j := by
  funext j
  simp [rankOnePoint]

@[simp]
theorem rankOnePoint_zero_offset_one (step : LatticePoint d) :
    rankOnePoint 0 step 1 = step := by
  funext j
  simp [rankOnePoint]

/-- The rank-one GAP
`{offset + n * step | 0 ≤ n ≤ length}`.

Using the maximum coefficient rather than the width makes dilation formulas
literal: the `k`-fold dilation has maximum coefficient `k * length`.
-/
def rankOne (offset step : LatticePoint d) (length : ℕ) : GAP d 1 where
  offset := offset
  steps := fun _ ↦ step
  widths := fun _ ↦ length + 1
  width_pos := fun _ ↦ Nat.zero_lt_succ length

@[simp]
theorem rankOne_offset (offset step : LatticePoint d) (length : ℕ) :
    (rankOne offset step length).offset = offset := rfl

@[simp]
theorem rankOne_steps (offset step : LatticePoint d) (length : ℕ)
    (i : Fin 1) :
    (rankOne offset step length).steps i = step := rfl

@[simp]
theorem rankOne_widths (offset step : LatticePoint d) (length : ℕ)
    (i : Fin 1) :
    (rankOne offset step length).widths i = length + 1 := rfl

@[simp]
theorem rankOne_coordPoint (offset step : LatticePoint d) (length : ℕ)
    (n : (rankOne offset step length).Coord) :
    (rankOne offset step length).coordPoint n =
      rankOnePoint offset step (n 0) := by
  funext j
  simp [GAP.coordPoint, rankOnePoint]

/-- Membership in a rank-one carrier in bounded-coefficient form. -/
theorem mem_rankOne_carrier_iff {offset step : LatticePoint d} {length : ℕ}
    {x : LatticePoint d} :
    x ∈ (rankOne offset step length).carrier ↔
      ∃ n ≤ length, rankOnePoint offset step n = x := by
  rw [GAP.mem_carrier_iff]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n 0, Nat.le_of_lt_succ (n 0).isLt, (rankOne_coordPoint _ _ _ _).symm⟩
  · rintro ⟨n, hn, rfl⟩
    let c : (rankOne offset step length).Coord :=
      fun _ ↦ ⟨n, Nat.lt_succ_of_le hn⟩
    refine ⟨c, ?_⟩
    rw [rankOne_coordPoint]

/-- Exact finite carrier of a rank-one GAP. -/
theorem rankOne_carrier (offset step : LatticePoint d) (length : ℕ) :
    (rankOne offset step length).carrier =
      (Finset.range (length + 1)).image (rankOnePoint offset step) := by
  classical
  ext x
  rw [mem_rankOne_carrier_iff]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, Nat.lt_succ_of_le hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, Nat.le_of_lt_succ hn, rfl⟩

/-- A nonzero step makes every bounded rank-one presentation proper. -/
theorem rankOne_proper {offset step : LatticePoint d} (length : ℕ)
    (hstep : step ≠ 0) :
    (rankOne offset step length).Proper := by
  intro n m hnm
  rw [rankOne_coordPoint, rankOne_coordPoint] at hnm
  obtain ⟨j, hj⟩ : ∃ j, step j ≠ 0 := by
    by_contra h
    push Not at h
    apply hstep
    funext i
    exact h i
  have hcomponent := congrFun hnm j
  simp only [rankOnePoint] at hcomponent
  have hmul : (n 0 : ℤ) * step j = (m 0 : ℤ) * step j :=
    add_left_cancel hcomponent
  have hcoeff : (n 0 : ℤ) = (m 0 : ℤ) :=
    mul_right_cancel₀ hj hmul
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact Fin.ext (Int.ofNat_inj.mp hcoeff)

/-- A rank-one GAP of maximum coefficient zero is proper even if its step
vanishes, because its coordinate box is a singleton. -/
theorem rankOne_zero_proper (offset step : LatticePoint d) :
    (rankOne offset step 0).Proper := by
  intro n m _
  funext i
  apply Fin.ext
  have hn := (n i).isLt
  have hm := (m i).isLt
  simp only [rankOne_widths] at hn hm
  omega

/-- Homogeneity criterion for the rank-one builder. -/
theorem rankOne_homogeneous_iff (offset step : LatticePoint d) (length : ℕ) :
    (rankOne offset step length).Homogeneous ↔
      ∃ z : ℤ, offset = fun j ↦ z * step j := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z 0, ?_⟩
    simpa [rankOne] using hz
  · rintro ⟨z, hz⟩
    refine ⟨fun _ ↦ z, ?_⟩
    simpa [rankOne] using hz

/-- Dilation of the rank-one builder, as another rank-one builder. -/
theorem dilate_rankOne (k : ℕ) (offset step : LatticePoint d) (length : ℕ) :
    (rankOne offset step length).dilate k =
      rankOne (fun j ↦ (k : ℤ) * offset j) step (k * length) := by
  rw [GAP.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext i
  simp [GAP.dilate, rankOne]

/-- A dilation of a rank-one progression with nonzero step is proper. -/
theorem dilate_rankOne_proper {offset step : LatticePoint d} (length k : ℕ)
    (hstep : step ≠ 0) :
    ((rankOne offset step length).dilate k).Proper := by
  rw [dilate_rankOne]
  exact rankOne_proper _ hstep

/-- Exact carrier of a dilated rank-one progression. -/
theorem dilate_rankOne_carrier (k : ℕ) (offset step : LatticePoint d)
    (length : ℕ) :
    ((rankOne offset step length).dilate k).carrier =
      (Finset.range (k * length + 1)).image
        (rankOnePoint (fun j ↦ (k : ℤ) * offset j) step) := by
  rw [dilate_rankOne, rankOne_carrier]

/-! ## Homogeneous progressions containing a prescribed point -/

/-- A homogeneous proper rank-one GAP whose carrier is exactly `{x}`.  This
works without a nonzero assumption on `x`. -/
def pointGAP (x : LatticePoint d) : GAP d 1 :=
  rankOne x x 0

@[simp]
theorem pointGAP_carrier (x : LatticePoint d) :
    (pointGAP x).carrier = {x} := by
  change (rankOne x x 0).carrier = {x}
  ext y
  rw [mem_rankOne_carrier_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    simp
  · intro hy
    have hyx : y = x := by simpa using hy
    subst y
    exact ⟨0, Nat.zero_le _, by simp⟩

@[simp]
theorem mem_pointGAP_carrier {x y : LatticePoint d} :
    y ∈ (pointGAP x).carrier ↔ y = x := by
  rw [pointGAP_carrier]
  simp

theorem point_mem_pointGAP (x : LatticePoint d) :
    x ∈ (pointGAP x).carrier := by simp

theorem pointGAP_proper (x : LatticePoint d) :
    (pointGAP x).Proper :=
  rankOne_zero_proper _ _

theorem pointGAP_homogeneous (x : LatticePoint d) :
    (pointGAP x).Homogeneous := by
  change (rankOne x x 0).Homogeneous
  rw [rankOne_homogeneous_iff]
  exact ⟨1, by simp⟩

/-- Every dilation of the singleton point GAP is still a singleton, at the
correspondingly scaled point. -/
@[simp]
theorem pointGAP_dilate_carrier (x : LatticePoint d) (k : ℕ) :
    ((pointGAP x).dilate k).carrier =
      {fun j ↦ (k : ℤ) * x j} := by
  rw [pointGAP, dilate_rankOne]
  change (rankOne (fun j ↦ (k : ℤ) * x j) x 0).carrier = _
  ext y
  rw [mem_rankOne_carrier_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    simp
  · intro hy
    have hyx : y = (fun j ↦ (k : ℤ) * x j) := by simpa using hy
    subst y
    exact ⟨0, Nat.zero_le _, by simp⟩

theorem pointGAP_dilate_proper (x : LatticePoint d) (k : ℕ) :
    ((pointGAP x).dilate k).Proper := by
  rw [pointGAP, dilate_rankOne]
  exact rankOne_zero_proper _ _

/-- The homogeneous rank-one segment from zero to `x`. -/
def pointSegment (x : LatticePoint d) : GAP d 1 :=
  rankOne 0 x 1

theorem pointSegment_homogeneous (x : LatticePoint d) :
    (pointSegment x).Homogeneous := by
  change (rankOne 0 x 1).Homogeneous
  rw [rankOne_homogeneous_iff]
  refine ⟨0, ?_⟩
  funext j
  simp

@[simp]
theorem pointSegment_carrier (x : LatticePoint d) :
    (pointSegment x).carrier = {0, x} := by
  change (rankOne 0 x 1).carrier = {0, x}
  ext y
  rw [mem_rankOne_carrier_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨n, hn, rfl⟩
    interval_cases n
    · exact Or.inl (rankOnePoint_zero _ _)
    · exact Or.inr (rankOnePoint_zero_offset_one x)
  · intro hy
    rcases hy with rfl | rfl
    · exact ⟨0, by omega, rankOnePoint_zero _ _⟩
    · exact ⟨1, by omega, rankOnePoint_zero_offset_one _⟩

@[simp]
theorem zero_mem_pointSegment (x : LatticePoint d) :
    0 ∈ (pointSegment x).carrier := by simp

@[simp]
theorem point_mem_pointSegment (x : LatticePoint d) :
    x ∈ (pointSegment x).carrier := by simp

theorem pointSegment_proper {x : LatticePoint d} (hx : x ≠ 0) :
    (pointSegment x).Proper :=
  rankOne_proper 1 hx

/-- Exact membership in the `k`-fold dilation of `{0,x}`. -/
theorem mem_pointSegment_dilate_iff {x y : LatticePoint d} (k : ℕ) :
    y ∈ ((pointSegment x).dilate k).carrier ↔
      ∃ n ≤ k, (fun j ↦ (n : ℤ) * x j) = y := by
  rw [pointSegment, dilate_rankOne, mem_rankOne_carrier_iff]
  simp only [Nat.mul_one]
  have hpoint (n : ℕ) :
      rankOnePoint (fun _ : Fin d ↦ (0 : ℤ)) x n =
        (fun j ↦ (n : ℤ) * x j) := by
    funext j
    simp [rankOnePoint]
  constructor
  · rintro ⟨n, hn, hny⟩
    refine ⟨n, hn, ?_⟩
    exact (hpoint n) ▸ hny
  · rintro ⟨n, hn, hny⟩
    refine ⟨n, hn, ?_⟩
    exact (hpoint n).symm ▸ hny

/-- Exact finite carrier of the `k`-fold dilation of `{0,x}`. -/
theorem pointSegment_dilate_carrier (x : LatticePoint d) (k : ℕ) :
    ((pointSegment x).dilate k).carrier =
      (Finset.range (k + 1)).image
        (fun (n : ℕ) j ↦ (n : ℤ) * x j) := by
  classical
  ext y
  rw [mem_pointSegment_dilate_iff]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, Nat.lt_succ_of_le hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, Nat.le_of_lt_succ hn, rfl⟩

theorem pointSegment_dilate_proper {x : LatticePoint d} (k : ℕ)
    (hx : x ≠ 0) :
    ((pointSegment x).dilate k).Proper :=
  dilate_rankOne_proper 1 k hx

end Erdos186.CFP.GAPBuilders
