/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Symmetric generalized arithmetic progressions

The basic `GAP` interface uses the one-sided coefficient box
`0 ≤ n i < P.widths i`.  A progression represented in this way is centered
at zero when there are radii `ρ i` for which

* `P.widths i = 2 * ρ i + 1`, and
* `P.offset = -∑ i, ρ i • P.steps i`.

Thus its displayed coefficients relative to the origin range from `-ρ i`
through `ρ i`.  This file packages that condition as `GAP.Centered` and its
existential version as `GAP.Symmetric`.  In particular, symmetry is a property
of the displayed GAP presentation, not merely an assertion that its finite
carrier happens to be closed under negation.

Width-one coordinates are allowed by `GAP`.  They have radius zero in a
centered presentation and contribute no actual freedom.  The predicate
`GAP.Nondegenerate` records that all displayed coordinates are active; for a
centered GAP it is equivalent to positivity of every radius.
-/

namespace Erdos186

open scoped BigOperators

namespace GAP

variable {d r : ℕ}

/-- A one-sided GAP presentation is centered at zero with radii `radii` when
its coefficient interval in coordinate `i` is `0, ..., 2 * radii i` and its
offset is the negative of the radius vector. -/
def Centered (P : GAP d r) (radii : Fin r → ℕ) : Prop :=
  P.widths = (fun i ↦ 2 * radii i + 1) ∧
    P.offset = fun j ↦ -∑ i, (radii i : ℤ) * P.steps i j

/-- A GAP presentation is symmetric when it is centered for some tuple of
natural-number radii. -/
def Symmetric (P : GAP d r) : Prop :=
  ∃ radii : Fin r → ℕ, P.Centered radii

/-- A GAP presentation is nondegenerate when no displayed coordinate has
width one.  Since widths are positive, this says exactly that every width is
at least two. -/
def Nondegenerate (P : GAP d r) : Prop :=
  ∀ i, 2 ≤ P.widths i

namespace Centered

variable {P : GAP d r} {radii : Fin r → ℕ}

theorem widths_eq (hP : P.Centered radii) :
    P.widths = fun i ↦ 2 * radii i + 1 :=
  hP.1

theorem width_eq (hP : P.Centered radii) (i : Fin r) :
    P.widths i = 2 * radii i + 1 := by
  exact congrFun hP.1 i

theorem offset_eq (hP : P.Centered radii) :
    P.offset = fun j ↦ -∑ i, (radii i : ℤ) * P.steps i j :=
  hP.2

/-- The centered radii are uniquely determined by the widths. -/
theorem radii_unique (hP : P.Centered radii) {radii' : Fin r → ℕ}
    (hP' : P.Centered radii') : radii = radii' := by
  funext i
  have hi := hP.width_eq i
  have hi' := hP'.width_eq i
  omega

/-- Every centered width is odd. -/
theorem odd_width (hP : P.Centered radii) (i : Fin r) :
    Odd (P.widths i) := by
  rw [hP.width_eq i]
  exact ⟨radii i, by omega⟩

theorem width_sub_one (hP : P.Centered radii) (i : Fin r) :
    P.widths i - 1 = 2 * radii i := by
  rw [hP.width_eq i]
  omega

theorem radius_le_width (hP : P.Centered radii) (i : Fin r) :
    radii i < P.widths i := by
  rw [hP.width_eq i]
  omega

/-- In centered coordinates the GAP map is the expected integral linear
combination with coefficients `n i - radii i`. -/
theorem coordPoint_eq (hP : P.Centered radii) (n : P.Coord) :
    P.coordPoint n =
      fun j ↦ ∑ i, (((n i : ℕ) : ℤ) - (radii i : ℤ)) * P.steps i j := by
  funext j
  simp only [coordPoint]
  rw [hP.offset_eq]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  abel

/-- The coordinate tuple at the center of a centered GAP. -/
def centerCoord (hP : P.Centered radii) : P.Coord :=
  fun i ↦ ⟨radii i, hP.radius_le_width i⟩

@[simp]
theorem coordPoint_centerCoord (hP : P.Centered radii) :
    P.coordPoint hP.centerCoord = 0 := by
  rw [hP.coordPoint_eq]
  funext j
  simp [centerCoord]

/-- A centered GAP contains the origin. -/
theorem zero_mem_carrier (hP : P.Centered radii) :
    0 ∈ P.carrier := by
  exact mem_carrier_iff.mpr ⟨hP.centerCoord, hP.coordPoint_centerCoord⟩

/-- Reflection in the center of the one-sided coefficient box. -/
def reflectCoord (hP : P.Centered radii) (n : P.Coord) : P.Coord :=
  fun i ↦ ⟨2 * radii i - (n i : ℕ), by
    have hn := (n i).isLt
    have hw := hP.width_eq i
    omega⟩

@[simp]
theorem reflectCoord_apply (hP : P.Centered radii) (n : P.Coord) (i : Fin r) :
    (hP.reflectCoord n i : ℕ) = 2 * radii i - (n i : ℕ) :=
  rfl

@[simp]
theorem reflectCoord_reflectCoord (hP : P.Centered radii) (n : P.Coord) :
    hP.reflectCoord (hP.reflectCoord n) = n := by
  funext i
  apply Fin.ext
  simp only [reflectCoord_apply]
  have hn := (n i).isLt
  have hw := hP.width_eq i
  omega

/-- Reflection of a coefficient tuple negates the displayed lattice point. -/
@[simp]
theorem coordPoint_reflectCoord (hP : P.Centered radii) (n : P.Coord) :
    P.coordPoint (hP.reflectCoord n) = -P.coordPoint n := by
  rw [hP.coordPoint_eq, hP.coordPoint_eq]
  funext j
  have hcoeff (i : Fin r) :
      (((hP.reflectCoord n i : ℕ) : ℤ) - (radii i : ℤ)) =
        -(((n i : ℕ) : ℤ) - (radii i : ℤ)) := by
    have hn : (n i : ℕ) ≤ 2 * radii i := by
      have hn' := (n i).isLt
      have hw := hP.width_eq i
      omega
    rw [show (hP.reflectCoord n i : ℕ) = 2 * radii i - (n i : ℕ) by rfl]
    rw [Int.ofNat_sub hn]
    push_cast
    ring
  simp_rw [hcoeff]
  simp only [neg_mul, Finset.sum_neg_distrib, Pi.neg_apply]

/-- Membership in the carrier of a centered GAP is closed under negation. -/
theorem neg_mem_carrier_of_mem (hP : P.Centered radii)
    {x : LatticePoint d} (hx : x ∈ P.carrier) :
    -x ∈ P.carrier := by
  obtain ⟨n, rfl⟩ := mem_carrier_iff.mp hx
  exact mem_carrier_iff.mpr ⟨hP.reflectCoord n, hP.coordPoint_reflectCoord n⟩

/-- Exact carrier symmetry under negation. -/
theorem neg_mem_carrier_iff (hP : P.Centered radii) (x : LatticePoint d) :
    -x ∈ P.carrier ↔ x ∈ P.carrier := by
  constructor
  · intro hx
    have := hP.neg_mem_carrier_of_mem hx
    simpa using this
  · exact hP.neg_mem_carrier_of_mem

/-- Negating every point of the carrier gives back the same finite set. -/
theorem image_neg_carrier (hP : P.Centered radii) :
    P.carrier.image (fun x ↦ -x) = P.carrier := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hP.neg_mem_carrier_of_mem hy
  · intro hx
    refine Finset.mem_image.mpr ⟨-x, hP.neg_mem_carrier_of_mem hx, ?_⟩
    simp

/-- A centered presentation is homogeneous: its offset is an integer
combination of its displayed steps. -/
theorem homogeneous (hP : P.Centered radii) : P.Homogeneous := by
  refine ⟨fun i ↦ -(radii i : ℤ), ?_⟩
  rw [hP.offset_eq]
  funext j
  simp

/-- Dilation preserves centeredness and multiplies every radius by the
dilation parameter. -/
theorem dilate (hP : P.Centered radii) (k : ℕ) :
    (P.dilate k).Centered (fun i ↦ k * radii i) := by
  constructor
  · funext i
    rw [dilate_widths, hP.width_sub_one i]
    ring
  · rw [dilate_offset, dilate_steps, hP.offset_eq]
    funext j
    rw [mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring

theorem dilate_width_eq (hP : P.Centered radii) (k : ℕ) (i : Fin r) :
    (P.dilate k).widths i = 2 * (k * radii i) + 1 := by
  exact (hP.dilate k).width_eq i

theorem volume_eq (hP : P.Centered radii) :
    P.volume = ∏ i, (2 * radii i + 1) := by
  simp only [volume, hP.width_eq]

theorem volume_dilate_eq (hP : P.Centered radii) (k : ℕ) :
    (P.dilate k).volume = ∏ i, (2 * (k * radii i) + 1) := by
  exact (hP.dilate k).volume_eq

/-- For a centered presentation, absence of width-one coordinates is exactly
positivity of every radius. -/
theorem nondegenerate_iff (hP : P.Centered radii) :
    P.Nondegenerate ↔ ∀ i, 0 < radii i := by
  constructor
  · intro h i
    have := h i
    rw [hP.width_eq i] at this
    omega
  · intro h i
    rw [hP.width_eq i]
    have := h i
    omega

theorem width_one_iff_radius_zero (hP : P.Centered radii) (i : Fin r) :
    P.widths i = 1 ↔ radii i = 0 := by
  rw [hP.width_eq i]
  omega

end Centered

namespace Symmetric

variable {P : GAP d r}

/-- Eliminate the existential wrapper around symmetry. -/
theorem exists_centered (hP : P.Symmetric) :
    ∃ radii : Fin r → ℕ, P.Centered radii :=
  hP

theorem homogeneous (hP : P.Symmetric) : P.Homogeneous := by
  obtain ⟨radii, hradii⟩ := hP
  exact hradii.homogeneous

theorem zero_mem_carrier (hP : P.Symmetric) : 0 ∈ P.carrier := by
  obtain ⟨radii, hradii⟩ := hP
  exact hradii.zero_mem_carrier

theorem neg_mem_carrier_iff (hP : P.Symmetric) (x : LatticePoint d) :
    -x ∈ P.carrier ↔ x ∈ P.carrier := by
  obtain ⟨radii, hradii⟩ := hP
  exact hradii.neg_mem_carrier_iff x

theorem neg_mem_carrier_of_mem (hP : P.Symmetric)
    {x : LatticePoint d} (hx : x ∈ P.carrier) :
    -x ∈ P.carrier := by
  exact (hP.neg_mem_carrier_iff x).2 hx

theorem image_neg_carrier (hP : P.Symmetric) :
    P.carrier.image (fun x ↦ -x) = P.carrier := by
  obtain ⟨radii, hradii⟩ := hP
  exact hradii.image_neg_carrier

theorem dilate (hP : P.Symmetric) (k : ℕ) : (P.dilate k).Symmetric := by
  obtain ⟨radii, hradii⟩ := hP
  exact ⟨fun i ↦ k * radii i, hradii.dilate k⟩

theorem odd_width (hP : P.Symmetric) (i : Fin r) : Odd (P.widths i) := by
  obtain ⟨radii, hradii⟩ := hP
  exact hradii.odd_width i

end Symmetric

namespace Nondegenerate

variable {P : GAP d r}

theorem width_pos (hP : P.Nondegenerate) (i : Fin r) : 0 < P.widths i :=
  lt_of_lt_of_le (by omega) (hP i)

theorem width_ne_one (hP : P.Nondegenerate) (i : Fin r) :
    P.widths i ≠ 1 := by
  have := hP i
  omega

/-- Positive dilation cannot create width-one coordinates from an active
coordinate. -/
theorem dilate (hP : P.Nondegenerate) {k : ℕ} (hk : 0 < k) :
    (P.dilate k).Nondegenerate := by
  intro i
  rw [dilate_widths]
  have hi := hP i
  have hsub : 1 ≤ P.widths i - 1 := by omega
  calc
    2 ≤ k * 1 + 1 := by omega
    _ ≤ k * (P.widths i - 1) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left k hsub) 1

end Nondegenerate

end GAP
end Erdos186
