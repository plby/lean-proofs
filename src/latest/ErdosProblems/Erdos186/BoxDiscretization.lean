/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Axis-parallel discretization for Erdős problem 186

This file supplies the finite lattice-box bookkeeping used after the
convex-density step in the Pham--Zakharov iteration.  It deliberately keeps
the analytic input abstract: a set is assumed to lie in a real
axis-parallel box.  Rounding the lower endpoints down and the upper
endpoints up then gives an integer box which

* contains every lattice point of the real box;
* has exactly the product of its integral side lengths many points; and
* has real cardinality at most the product of the original side lengths
  enlarged by `3`.

The final section also records the corresponding facts for occupied unit
cells, represented by coordinatewise flooring.  No convexity is needed for
these discretization facts; convexity enters only in producing the real box
and its side-length estimate.
-/

open scoped BigOperators

namespace Erdos186
namespace BoxDiscretization

noncomputable section

/-- The integer lattice in dimension `d`, kept local to this standalone
discretization interface. -/
abbrev LatticePoint (d : ℕ) := Fin d → ℤ

/-- Euclidean `d`-space in its coordinate representation. -/
abbrev RealPoint (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The `i`th coordinate of a Euclidean point. -/
abbrev coordinate (x : RealPoint d) (i : Fin d) : ℝ := x.ofLp i

/-- The canonical coordinatewise embedding of the integer lattice in
Euclidean space. -/
def latticeEmbed (z : LatticePoint d) : RealPoint d :=
  WithLp.toLp 2 fun i ↦ (z i : ℝ)

@[simp]
theorem latticeEmbed_coordinate (z : LatticePoint d) (i : Fin d) :
    coordinate (latticeEmbed z) i = (z i : ℝ) := rfl

/-- The canonical lattice embedding loses no points. -/
theorem latticeEmbed_injective : Function.Injective (latticeEmbed (d := d)) := by
  intro z w hzw
  funext i
  have hi := congrArg (fun x : RealPoint d ↦ coordinate x i) hzw
  change (z i : ℝ) = (w i : ℝ) at hi
  exact_mod_cast hi

/-- A closed axis-parallel box in the integer lattice.  It is empty if one
of its lower endpoints is greater than its corresponding upper endpoint. -/
structure IntegerBox (d : ℕ) where
  lower : LatticePoint d
  upper : LatticePoint d

namespace IntegerBox

/-- The finite set of lattice points in an integer box. -/
def carrier (B : IntegerBox d) : Finset (LatticePoint d) :=
  Fintype.piFinset fun i ↦ Finset.Icc (B.lower i) (B.upper i)

@[simp]
theorem mem_carrier_iff {B : IntegerBox d} {z : LatticePoint d} :
    z ∈ B.carrier ↔ ∀ i, B.lower i ≤ z i ∧ z i ≤ B.upper i := by
  simp [carrier]

/-- The integral side length in coordinate `i`. -/
def sideLength (B : IntegerBox d) (i : Fin d) : ℕ :=
  (B.upper i + 1 - B.lower i).toNat

/-- Exact cardinality of the lattice carrier. -/
theorem card_carrier (B : IntegerBox d) :
    B.carrier.card = ∏ i, B.sideLength i := by
  simp [carrier, sideLength, Int.card_Icc]

/-- The embedded copy of the lattice carrier in Euclidean space. -/
def realCarrier (B : IntegerBox d) : Finset (RealPoint d) :=
  B.carrier.image latticeEmbed

/-- Embedding a box into Euclidean space preserves its cardinality. -/
@[simp]
theorem card_realCarrier (B : IntegerBox d) :
    B.realCarrier.card = B.carrier.card :=
  Finset.card_image_of_injective _ latticeEmbed_injective

/-- The continuous real box with the same integral endpoints. -/
def realization (B : IntegerBox d) : Set (RealPoint d) :=
  {x | ∀ i, (B.lower i : ℝ) ≤ coordinate x i ∧
    coordinate x i ≤ (B.upper i : ℝ)}

@[simp]
theorem mem_realization_iff {B : IntegerBox d} {x : RealPoint d} :
    x ∈ B.realization ↔ ∀ i, (B.lower i : ℝ) ≤ coordinate x i ∧
      coordinate x i ≤ (B.upper i : ℝ) := Iff.rfl

/-- On lattice points, membership in the continuous realization is exactly
membership in the finite carrier. -/
theorem latticeEmbed_mem_realization_iff {B : IntegerBox d}
    {z : LatticePoint d} :
    latticeEmbed z ∈ B.realization ↔ z ∈ B.carrier := by
  rw [mem_carrier_iff, mem_realization_iff]
  constructor
  · intro hz i
    have hi := hz i
    change (B.lower i : ℝ) ≤ (z i : ℝ) ∧
      (z i : ℝ) ≤ (B.upper i : ℝ) at hi
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2
  · intro hz i
    have hi := hz i
    change (B.lower i : ℝ) ≤ (z i : ℝ) ∧
      (z i : ℝ) ≤ (B.upper i : ℝ)
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2

/-- The embedded finite carrier is contained in the continuous box. -/
theorem realCarrier_subset_realization (B : IntegerBox d) :
    (↑B.realCarrier : Set (RealPoint d)) ⊆ B.realization := by
  intro x hx
  simp only [realCarrier, Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  exact latticeEmbed_mem_realization_iff.mpr hz

end IntegerBox

/-- A closed real axis-parallel box with coordinatewise endpoints. -/
def realBox (lower upper : Fin d → ℝ) : Set (RealPoint d) :=
  {x | ∀ i, lower i ≤ coordinate x i ∧ coordinate x i ≤ upper i}

@[simp]
theorem mem_realBox_iff {lower upper : Fin d → ℝ} {x : RealPoint d} :
    x ∈ realBox lower upper ↔
      ∀ i, lower i ≤ coordinate x i ∧ coordinate x i ≤ upper i := Iff.rfl

/-- Round a real box outwards to an integer box. -/
def roundedBox (lower upper : Fin d → ℝ) : IntegerBox d where
  lower i := ⌊lower i⌋
  upper i := ⌈upper i⌉

@[simp]
theorem roundedBox_lower (lower upper : Fin d → ℝ) (i : Fin d) :
    (roundedBox lower upper).lower i = ⌊lower i⌋ := rfl

@[simp]
theorem roundedBox_upper (lower upper : Fin d → ℝ) (i : Fin d) :
    (roundedBox lower upper).upper i = ⌈upper i⌉ := rfl

/-- The rounded integer box realizes a continuous box containing the
original real box. -/
theorem realBox_subset_roundedBox_realization
    (lower upper : Fin d → ℝ) :
    realBox lower upper ⊆ (roundedBox lower upper).realization := by
  intro x hx i
  exact ⟨(Int.floor_le (lower i)).trans (hx i).1,
    (hx i).2.trans (Int.le_ceil (upper i))⟩

/-- Every lattice point of a real box belongs to its outward-rounded
integer box. -/
theorem lattice_mem_roundedBox_of_mem_realBox
    {lower upper : Fin d → ℝ} {z : LatticePoint d}
    (hz : latticeEmbed z ∈ realBox lower upper) :
    z ∈ (roundedBox lower upper).carrier := by
  rw [← IntegerBox.latticeEmbed_mem_realization_iff]
  exact realBox_subset_roundedBox_realization lower upper hz

/-- A finite lattice subset of a real box is contained in the rounded
integer carrier. -/
theorem finset_subset_roundedBox
    {lower upper : Fin d → ℝ} {S : Finset (LatticePoint d)}
    (hS : ∀ z ∈ S, latticeEmbed z ∈ realBox lower upper) :
    S ⊆ (roundedBox lower upper).carrier := by
  intro z hz
  exact lattice_mem_roundedBox_of_mem_realBox (hS z hz)

/-- Hence a finite lattice subset has at most as many points as the rounded
integer box. -/
theorem card_le_roundedBox
    {lower upper : Fin d → ℝ} {S : Finset (LatticePoint d)}
    (hS : ∀ z ∈ S, latticeEmbed z ∈ realBox lower upper) :
    S.card ≤ (roundedBox lower upper).carrier.card :=
  Finset.card_le_card (finset_subset_roundedBox hS)

/-- Coordinatewise ordered endpoints remain ordered after outward
rounding. -/
theorem roundedBox_lower_le_upper {lower upper : Fin d → ℝ}
    (hlu : ∀ i, lower i ≤ upper i) (i : Fin d) :
    (roundedBox lower upper).lower i ≤ (roundedBox lower upper).upper i := by
  exact (Int.floor_mono (hlu i)).trans (Int.floor_le_ceil (upper i))

/-- The integer expression defining a rounded side length is nonnegative. -/
theorem roundedBox_side_nonneg {lower upper : Fin d → ℝ}
    (hlu : ∀ i, lower i ≤ upper i) (i : Fin d) :
    0 ≤ (roundedBox lower upper).upper i + 1 -
      (roundedBox lower upper).lower i := by
  have := roundedBox_lower_le_upper hlu i
  omega

/-- After coercion to the reals, the rounded side length is the expected
integer endpoint difference. -/
theorem roundedBox_sideLength_cast {lower upper : Fin d → ℝ}
    (hlu : ∀ i, lower i ≤ upper i) (i : Fin d) :
    ((roundedBox lower upper).sideLength i : ℝ) =
      (⌈upper i⌉ : ℝ) + 1 - (⌊lower i⌋ : ℝ) := by
  change ((((⌈upper i⌉ : ℤ) + 1 - ⌊lower i⌋).toNat : ℕ) : ℝ) = _
  norm_cast
  exact Int.toNat_of_nonneg (by simpa using roundedBox_side_nonneg hlu i)

/-- Outward rounding enlarges each real side length by less than `3`.
The harmless constant `3` accommodates both endpoint roundings and the
inclusive lattice cardinality. -/
theorem roundedBox_sideLength_lt {lower upper : Fin d → ℝ}
    (hlu : ∀ i, lower i ≤ upper i) (i : Fin d) :
    ((roundedBox lower upper).sideLength i : ℝ) <
      upper i - lower i + 3 := by
  rw [roundedBox_sideLength_cast hlu i]
  have hu := Int.ceil_lt_add_one (upper i)
  have hl := Int.sub_one_lt_floor (lower i)
  linarith

/-- Weak form of the rounded side-length estimate, convenient for finite
products. -/
theorem roundedBox_sideLength_le {lower upper : Fin d → ℝ}
    (hlu : ∀ i, lower i ≤ upper i) (i : Fin d) :
    ((roundedBox lower upper).sideLength i : ℝ) ≤
      upper i - lower i + 3 :=
  (roundedBox_sideLength_lt hlu i).le

/-- The exact lattice cardinality of an outward-rounded real box. -/
theorem card_roundedBox (lower upper : Fin d → ℝ) :
    (roundedBox lower upper).carrier.card =
      ∏ i, (⌈upper i⌉ + 1 - ⌊lower i⌋).toNat := by
  simpa [IntegerBox.sideLength] using
    IntegerBox.card_carrier (roundedBox lower upper)

/-- The real cardinality of the rounded lattice box is controlled by the
product of the original real side lengths, each enlarged by `3`. -/
theorem card_roundedBox_cast_le {lower upper : Fin d → ℝ}
    (hlu : ∀ i, lower i ≤ upper i) :
    ((roundedBox lower upper).carrier.card : ℝ) ≤
      ∏ i, (upper i - lower i + 3) := by
  rw [IntegerBox.card_carrier, Nat.cast_prod]
  exact Finset.prod_le_prod (fun i _ ↦ Nat.cast_nonneg _)
    (fun i _ ↦ roundedBox_sideLength_le hlu i)

/-- Direct cardinality comparison for any finite lattice set enclosed by a
real box. -/
theorem card_cast_le_product_of_subset_realBox
    {lower upper : Fin d → ℝ} {S : Finset (LatticePoint d)}
    (hlu : ∀ i, lower i ≤ upper i)
    (hS : ∀ z ∈ S, latticeEmbed z ∈ realBox lower upper) :
    (S.card : ℝ) ≤ ∏ i, (upper i - lower i + 3) := by
  have hcard : (S.card : ℝ) ≤ ((roundedBox lower upper).carrier.card : ℝ) := by
    exact_mod_cast card_le_roundedBox hS
  exact hcard.trans (card_roundedBox_cast_le hlu)

/-- Coordinatewise floor, identifying the unit lattice cell occupied by a
real point. -/
def floorPoint (x : RealPoint d) : LatticePoint d :=
  fun i ↦ ⌊coordinate x i⌋

/-- The finite set of occupied unit cells of a finite real point set. -/
def floorCells (X : Finset (RealPoint d)) : Finset (LatticePoint d) :=
  X.image floorPoint

@[simp]
theorem mem_floorCells_iff {X : Finset (RealPoint d)} {z : LatticePoint d} :
    z ∈ floorCells X ↔ ∃ x ∈ X, floorPoint x = z := by
  simp [floorCells]

/-- Passing to occupied cells cannot increase cardinality. -/
theorem card_floorCells_le (X : Finset (RealPoint d)) :
    (floorCells X).card ≤ X.card := by
  exact Finset.card_image_le

/-- If the chosen real points occupy distinct unit cells, discretization
preserves cardinality. -/
theorem card_floorCells_eq_of_injOn {X : Finset (RealPoint d)}
    (hX : Set.InjOn floorPoint (↑X : Set (RealPoint d))) :
    (floorCells X).card = X.card := by
  exact Finset.card_image_iff.mpr hX

/-- Flooring a point in a real box produces a cell in its rounded integer
box. -/
theorem floorPoint_mem_roundedBox {lower upper : Fin d → ℝ}
    {x : RealPoint d} (hx : x ∈ realBox lower upper) :
    floorPoint x ∈ (roundedBox lower upper).carrier := by
  rw [IntegerBox.mem_carrier_iff]
  intro i
  constructor
  · exact Int.floor_mono (hx i).1
  · exact (Int.floor_mono (hx i).2).trans (Int.floor_le_ceil (upper i))

/-- All cells occupied by points of a real box lie in the rounded carrier. -/
theorem floorCells_subset_roundedBox {lower upper : Fin d → ℝ}
    {X : Finset (RealPoint d)} (hX : ∀ x ∈ X, x ∈ realBox lower upper) :
    floorCells X ⊆ (roundedBox lower upper).carrier := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_floorCells_iff.mp hz
  exact floorPoint_mem_roundedBox (hX x hx)

/-- The number of occupied cells is bounded by the number of lattice points
in the rounded box. -/
theorem card_floorCells_le_roundedBox {lower upper : Fin d → ℝ}
    {X : Finset (RealPoint d)} (hX : ∀ x ∈ X, x ∈ realBox lower upper) :
    (floorCells X).card ≤ (roundedBox lower upper).carrier.card :=
  Finset.card_le_card (floorCells_subset_roundedBox hX)

/-- A finite family of points in distinct unit cells has cardinality at
most the rounded-box cardinality. -/
theorem card_le_roundedBox_of_floorPoint_injOn
    {lower upper : Fin d → ℝ} {X : Finset (RealPoint d)}
    (hX : ∀ x ∈ X, x ∈ realBox lower upper)
    (hinj : Set.InjOn floorPoint (↑X : Set (RealPoint d))) :
    X.card ≤ (roundedBox lower upper).carrier.card := by
  rw [← card_floorCells_eq_of_injOn hinj]
  exact card_floorCells_le_roundedBox hX

/-- Product-form bound for a finite family occupying distinct unit cells. -/
theorem card_cast_le_product_of_floorPoint_injOn
    {lower upper : Fin d → ℝ} {X : Finset (RealPoint d)}
    (hlu : ∀ i, lower i ≤ upper i)
    (hX : ∀ x ∈ X, x ∈ realBox lower upper)
    (hinj : Set.InjOn floorPoint (↑X : Set (RealPoint d))) :
    (X.card : ℝ) ≤ ∏ i, (upper i - lower i + 3) := by
  have hcard : (X.card : ℝ) ≤ ((roundedBox lower upper).carrier.card : ℝ) := by
    exact_mod_cast card_le_roundedBox_of_floorPoint_injOn hX hinj
  exact hcard.trans (card_roundedBox_cast_le hlu)

end
end BoxDiscretization
end Erdos186
