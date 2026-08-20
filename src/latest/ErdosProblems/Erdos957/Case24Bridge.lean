import Mathlib
import ErdosProblems.Erdos957.Cases24
import ErdosProblems.Erdos957.Angle

/-!
# Local transfer packages for Cases 2 and 4 of Erdős 957

`Erdos957Cases24` proves the coordinate identities used in the two
triangular-lattice cases.  This file turns those identities into the exact
local obligations needed by the doubled-charge construction: a finite set of
recipients, an explicit number of doubled tokens at each recipient, the row
sum, exclusion from the supporting hull, the degree-capacity inequality, and
the common locality rectangle.

The low-level constructors expose their degree inputs, while the final
constructors discharge them from one-separation, strict support, angular
packing, and regular-hexagon completion.  In Case 4 the transfer is indexed
by its source, so every source row emits exactly two doubled tokens.
-/

open Metric

noncomputable section

namespace Erdos957Case24Bridge

open Erdos957Cases24

abbrev Point := Erdos957Cases24.Point

/-- Concrete degree in the unit-distance graph of a finite configuration. -/
def unitDegree (A : Finset Point) (p : Point) : ℕ :=
  (unitNeighbors A p).card

/-- In the normalized coordinates, all hull points lie on or above the
supporting line.  Every Case 2/4 recipient has negative second coordinate. -/
def HullAboveSupport (H : Finset Point) : Prop :=
  ∀ p ∈ H, 0 ≤ p 1

lemma not_mem_hull_of_belowSupport {H : Finset Point} {p : Point}
    (hH : HullAboveSupport H) (hp : BelowSupport p) : p ∉ H := by
  intro hpH
  exact (not_lt_of_ge (hH p hpH)) hp

/-! ## Isometric bridge to the checked angular-packing development -/

/-- Coordinatewise identification of the `EuclideanSpace` plane with `ℂ`. -/
def toComplex (p : Point) : ℂ := ⟨p 0, p 1⟩

@[simp] lemma toComplex_re (p : Point) : (toComplex p).re = p 0 := rfl
@[simp] lemma toComplex_im (p : Point) : (toComplex p).im = p 1 := rfl

lemma toComplex_injective : Function.Injective toComplex := by
  intro p q hpq
  ext i
  fin_cases i
  · simpa using congrArg Complex.re hpq
  · simpa using congrArg Complex.im hpq

@[simp] lemma toComplex_add (p q : Point) :
    toComplex (p + q) = toComplex p + toComplex q := by
  apply Complex.ext <;> simp [toComplex]

@[simp] lemma toComplex_sub (p q : Point) :
    toComplex (p - q) = toComplex p - toComplex q := by
  apply Complex.ext <;> simp [toComplex]

lemma dist_toComplex (p q : Point) :
    dist (toComplex p) (toComplex q) = dist p q := by
  have hsq : dist (toComplex p) (toComplex q) ^ 2 = dist p q ^ 2 := by
    rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, dist_sq_eq_coordinates]
    simp only [toComplex, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  nlinarith [dist_nonneg (x := toComplex p) (y := toComplex q),
    dist_nonneg (x := p) (y := q)]

/-- The coordinate image of a finite Euclidean-plane configuration. -/
def complexImage (A : Finset Point) : Finset ℂ := A.image toComplex

lemma complexImage_oneSeparated {A : Finset Point} (hA : IsOneSeparated A) :
    Erdos957Angle.IsOneSeparated (complexImage A) := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨p, hpA, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨q, hqA, rfl⟩
  rw [dist_toComplex]
  exact hA p hpA q hqA (fun hpq ↦ hxy (congrArg toComplex hpq))

lemma image_unitNeighbors_subset_angle (A : Finset Point) (p : Point) :
    (unitNeighbors A p).image toComplex ⊆
      Erdos957Angle.unitNeighbors (complexImage A) (toComplex p) := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
  have hq' := mem_unitNeighbors.mp hq
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_image.mpr ⟨q, hq'.1, rfl⟩, by
    rw [dist_toComplex]
    simpa [dist_comm] using hq'.2⟩

/-- The global degree-six bound, transported from the checked angular
packing theorem. -/
theorem unitDegree_le_six {A : Finset Point} (hA : IsOneSeparated A) (p : Point) :
    unitDegree A p ≤ 6 := by
  have hcardImage : ((unitNeighbors A p).image toComplex).card =
      (unitNeighbors A p).card := by
    exact Finset.card_image_iff.mpr fun _ _ _ _ h ↦ toComplex_injective h
  rw [unitDegree, ← hcardImage]
  exact (Finset.card_le_card (image_unitNeighbors_subset_angle A p)).trans
    (Erdos957Angle.card_unitNeighbors_le_six (complexImage_oneSeparated hA) (toComplex p))

/-! ## The missing arbitrary-chord consequence of regular-hexagon rigidity -/

/-- In an indexed regular unit hexagon, a unit chord joins cyclically
consecutive vertices.  This finite classifier is the bridge needed to use
the six checked completion identities with an arbitrary known adjacent pair. -/
lemma regular_hexagon_unit_chord_cases (v : Fin 6 → ℂ)
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hids : v 0 - v 1 = v 5 ∧
      v 1 - v 2 = v 0 ∧
      v 2 - v 3 = v 1 ∧
      v 3 - v 4 = v 2 ∧
      v 4 - v 5 = v 3 ∧
      v 5 - v 0 = v 4)
    {i j : Fin 6} (hunit : ‖v i - v j‖ = 1) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
    (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
    (i = 5 ∧ j = 0) ∨ (i = 0 ∧ j = 5) := by
  have h2 : v 2 = v 1 - v 0 := by
    rw [← hids.2.1]
    abel
  have h3 : v 3 = -v 0 := by
    calc
      v 3 = v 2 - v 1 := by rw [← hids.2.2.1]; abel
      _ = -v 0 := by rw [h2]; abel
  have h4 : v 4 = -v 1 := by
    calc
      v 4 = v 3 - v 2 := by rw [← hids.2.2.2.1]; abel
      _ = -v 1 := by rw [h3, h2]; abel
  have h5 : v 5 = v 0 - v 1 := hids.1.symm
  have hxSq : (v 0).re ^ 2 + (v 0).im ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 2) (hnorm 0)
    rw [← Complex.normSq_eq_norm_sq] at h
    simpa [Complex.normSq_apply, pow_two] using h
  have hySq : (v 1).re ^ 2 + (v 1).im ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 2) (hnorm 1)
    rw [← Complex.normSq_eq_norm_sq] at h
    simpa [Complex.normSq_apply, pow_two] using h
  have hxyNorm : ‖v 0 - v 1‖ = 1 := by rw [hids.1, hnorm]
  have hxySq : ((v 0).re - (v 1).re) ^ 2 +
      ((v 0).im - (v 1).im) ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 2) hxyNorm
    rw [← Complex.normSq_eq_norm_sq] at h
    simpa [Complex.normSq_apply, pow_two] using h
  fin_cases i <;> fin_cases j <;> simp
  all_goals
    have hs := congrArg (fun t : ℝ ↦ t ^ 2) hunit
    rw [← Complex.normSq_eq_norm_sq] at hs
    simp [h2, h3, h4, h5, Complex.normSq_apply] at hs
    try nlinarith [hxSq, hySq, hxySq]

/-- Oriented completion form of `regular_hexagon_unit_chord_cases`. -/
lemma regular_hexagon_completion_of_unit_chord (v : Fin 6 → ℂ)
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hids : v 0 - v 1 = v 5 ∧
      v 1 - v 2 = v 0 ∧
      v 2 - v 3 = v 1 ∧
      v 3 - v 4 = v 2 ∧
      v 4 - v 5 = v 3 ∧
      v 5 - v 0 = v 4)
    {i j : Fin 6} (hunit : ‖v i - v j‖ = 1) :
    ∃ k, v i - v j = v k := by
  have h2 : v 2 = v 1 - v 0 := by rw [← hids.2.1]; abel
  have h3 : v 3 = -v 0 := by
    calc
      v 3 = v 2 - v 1 := by rw [← hids.2.2.1]; abel
      _ = -v 0 := by rw [h2]; abel
  have h4 : v 4 = -v 1 := by
    calc
      v 4 = v 3 - v 2 := by rw [← hids.2.2.2.1]; abel
      _ = -v 1 := by rw [h3, h2]; abel
  have h5 : v 5 = v 0 - v 1 := hids.1.symm
  rcases regular_hexagon_unit_chord_cases v hnorm hids hunit with
    h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨5, hids.1⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨2, h2.symm⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨0, hids.2.1⟩
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨3, ?_⟩
    rw [h2, h3]
    abel
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨1, hids.2.2.1⟩
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨4, ?_⟩
    rw [h2, h3, h4]
    abel
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨2, hids.2.2.2.1⟩
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨5, ?_⟩
    rw [h3, h4, h5]
    abel
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨3, hids.2.2.2.2.1⟩
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨0, ?_⟩
    rw [h4, h5]
    abel
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨4, hids.2.2.2.2.2⟩
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨1, ?_⟩
    rw [h5]
    abel

/-- A degree-six point with two adjacent known unit neighbors contains the
oriented regular-hexagon completion. -/
theorem hexagon_completion_mem {A : Finset Point} (hA : IsOneSeparated A)
    {p x y : Point} (hxA : x ∈ A) (hyA : y ∈ A)
    (hpx : dist p x = 1) (hpy : dist p y = 1)
    (hxy : dist x y = 1) (hdegree : unitDegree A p = 6) :
    p + x - y ∈ A := by
  let B := complexImage A
  let P := toComplex p
  let N := Erdos957Angle.unitNeighbors B P
  have hxN0 : x ∈ unitNeighbors A p := mem_unitNeighbors.mpr ⟨hxA, hpx⟩
  have hyN0 : y ∈ unitNeighbors A p := mem_unitNeighbors.mpr ⟨hyA, hpy⟩
  have hxN : toComplex x ∈ N := image_unitNeighbors_subset_angle A p
    (Finset.mem_image.mpr ⟨x, hxN0, rfl⟩)
  have hyN : toComplex y ∈ N := image_unitNeighbors_subset_angle A p
    (Finset.mem_image.mpr ⟨y, hyN0, rfl⟩)
  have himageCard : ((unitNeighbors A p).image toComplex).card = 6 := by
    rw [Finset.card_image_iff.mpr fun _ _ _ _ h ↦ toComplex_injective h]
    exact hdegree
  have hsixLe : 6 ≤ N.card := by
    rw [← himageCard]
    exact Finset.card_le_card (image_unitNeighbors_subset_angle A p)
  have hNcard : N.card = 6 := by
    apply le_antisymm
    · exact Erdos957Angle.card_unitNeighbors_le_six
        (complexImage_oneSeparated hA) P
    · exact hsixLe
  obtain ⟨e, hbin, hids⟩ :=
    Erdos957Angle.exists_unitNeighborEquiv_with_regular_hexagon_identities
      (complexImage_oneSeparated hA) P hNcard
  let vec : Fin 6 → ℂ := fun i ↦ ((e i : N) : ℂ) - P
  have hnorm : ∀ i, ‖vec i‖ = 1 := by
    intro i
    rw [← dist_eq_norm]
    simpa [dist_comm] using (Finset.mem_filter.mp (e i).prop).2
  let X : N := ⟨toComplex x, hxN⟩
  let Y : N := ⟨toComplex y, hyN⟩
  obtain ⟨i, hi⟩ := e.surjective X
  obtain ⟨j, hj⟩ := e.surjective Y
  have hvi : vec i = toComplex x - P := by
    exact congrArg (fun z : N ↦ (z : ℂ) - P) hi
  have hvj : vec j = toComplex y - P := by
    exact congrArg (fun z : N ↦ (z : ℂ) - P) hj
  have hvunit : ‖vec i - vec j‖ = 1 := by
    rw [hvi, hvj, sub_sub_sub_cancel_right, ← dist_eq_norm,
      dist_toComplex, hxy]
  obtain ⟨k, hk⟩ := regular_hexagon_completion_of_unit_chord vec hnorm hids hvunit
  have htarget : P + toComplex x - toComplex y = ((e k : N) : ℂ) := by
    calc
      P + toComplex x - toComplex y =
          (toComplex x - P) - (toComplex y - P) + P := by ring
      _ = vec i - vec j + P := by rw [hvi, hvj]
      _ = vec k + P := by rw [hk]
      _ = ((e k : N) : ℂ) := by simp [vec]
  have hekB : ((e k : N) : ℂ) ∈ B := (Finset.mem_filter.mp (e k).prop).1
  rcases Finset.mem_image.mp hekB with ⟨q, hqA, hq⟩
  have hpq : p + x - y = q := by
    apply toComplex_injective
    simpa [P, hq] using htarget
  exact hpq.symm ▸ hqA

/-! ## Strict support-line exclusions -/

/-- All configuration points other than a specified boundary set lie
strictly below the normalized support line. -/
def StrictlyBelowOutside (A boundary : Finset Point) : Prop :=
  ∀ p ∈ A, p ∉ boundary → p 1 < 0

lemma not_mem_of_zero_height {A boundary : Finset Point} {p : Point}
    (hstrict : StrictlyBelowOutside A boundary)
    (hpBoundary : p ∉ boundary) (hpHeight : p 1 = 0) :
    p ∉ A := by
  intro hpA
  have := hstrict p hpA hpBoundary
  linarith

lemma case2_uNext_not_mem_of_strict_support {A : Finset Point}
    (hstrict : StrictlyBelowOutside A {Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.u}) :
    Erdos957Cases24.Case2.uNext ∉ A := by
  apply not_mem_of_zero_height hstrict
  · norm_num [Erdos957Cases24.Case2.uNext, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.u, point_inj]
  · simp [Erdos957Cases24.Case2.uNext]

lemma case2_eNorthEast_not_mem_of_strict_support {A : Finset Point}
    (hstrict : StrictlyBelowOutside A {Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.u}) :
    Erdos957Cases24.Case2.eNorthEast ∉ A := by
  apply not_mem_of_zero_height hstrict
  · norm_num [Erdos957Cases24.Case2.eNorthEast, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.u, point_inj]
  · simp [Erdos957Cases24.Case2.eNorthEast]

/-- A checked local row of the global doubled-token transfer. -/
structure LocalTransfer (A H : Finset Point) (source : Point)
    (emitted : ℕ) where
  recipients : Finset Point
  tokens : Point → ℕ
  positive_iff_mem : ∀ p, 0 < tokens p ↔ p ∈ recipients
  recipients_subset_configuration : recipients ⊆ A
  row_sum : ∑ p ∈ A, tokens p = emitted
  target_not_hull : ∀ p ∈ recipients, p ∉ H
  target_capacity : ∀ p ∈ recipients,
    2 * unitDegree A p + tokens p ≤ 12
  target_horizontal_le_three_halves : ∀ p ∈ recipients,
    |p 0| ≤ 3 / 2
  target_in_rectangle : ∀ p ∈ recipients, InTransferRectangle p
  target_below_support : ∀ p ∈ recipients, BelowSupport p
  target_within_two : ∀ p ∈ recipients, WithinTwoUnitEdges source p

namespace Case2

open Erdos957Cases24.Case2

/-! ### The final-sector bound at `e` -/

/-- Rotation through `-pi/3`.  It sends the closed angular sector from
`wNext - e` to the open ray `eNorthEast - e` onto the lower half-plane. -/
def sectorRotation : ℂ :=
  ⟨1 / 2, -(sqrtThree / 2)⟩

lemma norm_sectorRotation : ‖sectorRotation‖ = 1 := by
  have hsq : ‖sectorRotation‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [sectorRotation, Complex.normSq_apply]
    nlinarith [sqrtThree_sq]
  nlinarith [norm_nonneg sectorRotation]

lemma sectorRotation_ne_zero : sectorRotation ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [sectorRotation] at this

/-- Relative unit vectors at `e`, rotated so that the admissible final
sector becomes the lower half-plane. -/
def rotatedAtE (q : Point) : ℂ :=
  (toComplex q - toComplex e) * sectorRotation

lemma rotatedAtE_injective : Function.Injective rotatedAtE := by
  intro p q hpq
  have hsub : toComplex p - toComplex e = toComplex q - toComplex e := by
    exact mul_right_cancel₀ sectorRotation_ne_zero hpq
  apply toComplex_injective
  calc
    toComplex p = (toComplex p - toComplex e) + toComplex e := by ring
    _ = (toComplex q - toComplex e) + toComplex e := by rw [hsub]
    _ = toComplex q := by ring

lemma norm_rotatedAtE_of_unit {q : Point} (hq : dist e q = 1) :
    ‖rotatedAtE q‖ = 1 := by
  rw [rotatedAtE, norm_mul, norm_sectorRotation, mul_one,
    ← dist_eq_norm, dist_toComplex]
  simpa [dist_comm] using hq

lemma norm_sub_rotatedAtE (p q : Point) :
    ‖rotatedAtE p - rotatedAtE q‖ = dist p q := by
  calc
    ‖rotatedAtE p - rotatedAtE q‖ =
        ‖(toComplex p - toComplex q) * sectorRotation‖ := by
      congr 1
      simp only [rotatedAtE]
      ring
    _ = ‖toComplex p - toComplex q‖ := by
      rw [norm_mul, norm_sectorRotation, mul_one]
    _ = dist p q := by
      rw [← dist_eq_norm, dist_toComplex]

/-- Elementary circle/half-plane algebra underlying the final sector. -/
lemma final_sector_linear_bound {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1)
    (hx : -(1 / 2 : ℝ) ≤ x)
    (hy : y < sqrtThree / 2) :
    y ≤ sqrtThree * x := by
  by_cases hy0 : 0 ≤ y
  · have hySq : y ^ 2 < (3 / 4 : ℝ) := by
      nlinarith [sqrtThree_sq, sqrtThree_pos]
    have hxSq : (1 / 4 : ℝ) < x ^ 2 := by
      nlinarith
    have hxHalf : (1 / 2 : ℝ) < x := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    nlinarith [sqrtThree_pos]
  · have hyNeg : y < 0 := lt_of_not_ge hy0
    by_contra hlin
    have hlin' : sqrtThree * x < y := lt_of_not_ge hlin
    have hxNeg : x < 0 := by
      by_contra hx0
      have : 0 ≤ x := le_of_not_gt hx0
      nlinarith [sqrtThree_pos]
    have hxSq : x ^ 2 ≤ (1 / 4 : ℝ) := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    have hySq : (3 / 4 : ℝ) ≤ y ^ 2 := by
      nlinarith
    have hyUpper : y ≤ -(sqrtThree / 2) := by
      nlinarith [sqrtThree_sq, sqrtThree_pos]
    have hsxLower : -(sqrtThree / 2) ≤ sqrtThree * x := by
      nlinarith [sqrtThree_pos]
    linarith

lemma phaseBin_neg_one_val_lt_three :
    (Erdos957Angle.phaseBin (-1)).val < 3 := by
  norm_num [Erdos957Angle.phaseBin, Erdos957Angle.principalPhase,
    Complex.arg_neg_one, Real.pi_pos]

/-- Every neighbor of `e` other than `b` lies in the three admissible
rotated phase bins.  Separation from `b` supplies the oblique side of the
sector, while strict support excludes its upper boundary. -/
lemma phaseBin_rotatedAtE_val_lt_three {A : Finset Point}
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A {uPrev, u})
    (hbA : b ∈ A) {q : Point}
    (hqNeighbor : q ∈ unitNeighbors A e) (hqb : q ≠ b) :
    (Erdos957Angle.phaseBin (rotatedAtE q)).val < 3 := by
  have hqA : q ∈ A := (mem_unitNeighbors.mp hqNeighbor).1
  have hqe : dist e q = 1 := (mem_unitNeighbors.mp hqNeighbor).2
  have hunitSq := congrArg (fun t : ℝ ↦ t ^ 2) hqe
  rw [dist_sq_eq_coordinates] at hunitSq
  simp only [e, point_apply_zero, point_apply_one, one_pow] at hunitSq
  have hunit : (q 0 - 3 / 2) ^ 2 +
      (q 1 + sqrtThree / 2) ^ 2 = 1 := by
    nlinarith
  have hqBoundary : q ∉ ({uPrev, u} : Finset Point) := by
    intro hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · norm_num [uPrev, e, point_apply_zero, point_apply_one,
        sqrtThree_sq] at hunitSq
      nlinarith [sqrtThree_sq]
    · norm_num [u, e, point_apply_zero, point_apply_one,
        sqrtThree_sq] at hunitSq
      nlinarith [sqrtThree_sq]
  have hqBelow : q 1 < 0 := hstrict q hqA hqBoundary
  have hsepQB : 1 ≤ dist q b := hsep q hqA b hbA hqb
  have hsepQBSq : 1 ≤ dist q b ^ 2 := by
    nlinarith [dist_nonneg (x := q) (y := b)]
  rw [dist_sq_eq_coordinates] at hsepQBSq
  simp only [b, point_apply_zero, point_apply_one] at hsepQBSq
  have hx : -(1 / 2 : ℝ) ≤ q 0 - 3 / 2 := by
    nlinarith
  have hy : q 1 + sqrtThree / 2 < sqrtThree / 2 := by
    linarith
  have hlinear : q 1 + sqrtThree / 2 ≤
      sqrtThree * (q 0 - 3 / 2) :=
    final_sector_linear_bound hunit hx hy
  have him : (rotatedAtE q).im ≤ 0 := by
    simp only [rotatedAtE, sectorRotation, toComplex, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, e, point_apply_zero, point_apply_one]
    nlinarith
  rcases him.eq_or_lt with himZero | himNeg
  · have hlineEq : q 1 + sqrtThree / 2 =
        sqrtThree * (q 0 - 3 / 2) := by
      simp only [rotatedAtE, sectorRotation, toComplex, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, e, point_apply_zero, point_apply_one] at himZero
      nlinarith
    have hxBoundary : q 0 - 3 / 2 = -(1 / 2 : ℝ) := by
      have hlineSq := congrArg (fun t : ℝ ↦ t ^ 2) hlineEq
      have hxSq : 4 * (q 0 - 3 / 2) ^ 2 = 1 := by
        nlinarith [hunit, hlineSq, sqrtThree_sq]
      have hfactor : (2 * (q 0 - 3 / 2) - 1) *
          (2 * (q 0 - 3 / 2) + 1) = 0 := by
        nlinarith [hxSq]
      rcases mul_eq_zero.mp hfactor with hplus | hminus
      · have hupper : q 0 - 3 / 2 = (1 / 2 : ℝ) := by linarith
        have : sqrtThree / 2 < sqrtThree / 2 := by
          calc
            sqrtThree / 2 = sqrtThree * (q 0 - 3 / 2) := by rw [hupper]; ring
            _ = q 1 + sqrtThree / 2 := hlineEq.symm
            _ < sqrtThree / 2 := hy
        exact False.elim (lt_irrefl _ this)
      · linarith
    have hyBoundary : q 1 + sqrtThree / 2 = -(sqrtThree / 2) := by
      rw [hlineEq, hxBoundary]
      ring
    have hrot : rotatedAtE q = -1 := by
      apply Complex.ext
      · simp only [rotatedAtE, sectorRotation, toComplex, Complex.mul_re,
          Complex.sub_re, Complex.sub_im, e, point_apply_zero, point_apply_one,
          Complex.neg_re, Complex.one_re]
        nlinarith [sqrtThree_sq]
      · simp only [rotatedAtE, sectorRotation, toComplex, Complex.mul_im,
          Complex.sub_re, Complex.sub_im, e, point_apply_zero, point_apply_one,
          Complex.neg_im, Complex.one_im]
        nlinarith
    rw [hrot]
    exact phaseBin_neg_one_val_lt_three
  · exact Erdos957Angle.phaseBin_val_lt_three_of_im_neg himNeg

/-- The final-sector estimate used in Case 2, with no degree hypothesis:
strict support and one-separation leave at most three unit neighbors of `e`
besides the displayed neighbor `b`. -/
theorem unitDegree_e_le_four_of_strict_support {A : Finset Point}
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A {uPrev, u})
    (hbA : b ∈ A) :
    unitDegree A e ≤ 4 := by
  let S : Finset Point := (unitNeighbors A e).erase b
  let T : Finset ℂ := S.image rotatedAtE
  have hbNeighbor : b ∈ unitNeighbors A e := by
    exact mem_unitNeighbors.mpr ⟨hbA, by simpa [dist_comm] using dist_b_e⟩
  have hnorm : ∀ z ∈ T, ‖z‖ = 1 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨q, hqS, rfl⟩
    exact norm_rotatedAtE_of_unit (mem_unitNeighbors.mp
      (Finset.mem_of_mem_erase hqS)).2
  have hsepT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨p, hpS, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨q, hqS, rfl⟩
    rw [norm_sub_rotatedAtE]
    have hpN := Finset.mem_of_mem_erase hpS
    have hqN := Finset.mem_of_mem_erase hqS
    exact hsep p (mem_unitNeighbors.mp hpN).1 q (mem_unitNeighbors.mp hqN).1
      (fun hpq ↦ hxy (congrArg rotatedAtE hpq))
  have hbinInj := Erdos957Angle.phaseBin_injOn_of_unit_oneSeparated T hnorm hsepT
  have hbinSmall : ∀ z ∈ T, (Erdos957Angle.phaseBin z).val < 3 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨q, hqS, rfl⟩
    exact phaseBin_rotatedAtE_val_lt_three hsep hstrict hbA
      (Finset.mem_of_mem_erase hqS) (Finset.ne_of_mem_erase hqS)
  let f : T → Fin 3 := fun z ↦
    ⟨(Erdos957Angle.phaseBin z).val, hbinSmall z z.prop⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hbinInj x.prop y.prop
    apply Fin.ext
    simpa [f] using congrArg Fin.val hxy
  have hTcard : T.card ≤ 3 := by
    simpa [f] using Fintype.card_le_of_injective f hf
  have hSTcard : S.card = T.card := by
    exact (Finset.card_image_iff.mpr fun _ _ _ _ h ↦ rotatedAtE_injective h).symm
  have hScard : S.card ≤ 3 := by
    rw [hSTcard]
    exact hTcard
  have herase := Finset.card_erase_add_one hbNeighbor
  change (unitNeighbors A e).card ≤ 4
  change S.card + 1 = (unitNeighbors A e).card at herase
  omega

/-- One doubled half-token goes to `b` and one to the degree-selected
secondary recipient. -/
def tokens (A : Finset Point) (p : Point) : ℕ :=
  (if p = b then 1 else 0) +
    (if p = secondaryRecipient (unitDegree A w) (unitDegree A wNext) then 1 else 0)

lemma b_ne_secondaryRecipient (degreeW degreeWNext : ℕ) :
    b ≠ secondaryRecipient degreeW degreeWNext := by
  simp only [secondaryRecipient]
  split_ifs
  · intro h
    have h0 := congrArg (fun p : Point ↦ p 0) h
    norm_num [b, w] at h0
  · intro h
    have h0 := congrArg (fun p : Point ↦ p 0) h
    norm_num [b, wNext] at h0
  · intro h
    have h0 := congrArg (fun p : Point ↦ p 0) h
    norm_num [b, e] at h0

lemma tokens_positive_iff_mem (A : Finset Point) (p : Point) :
    0 < tokens A p ↔
      p ∈ recipientSet (unitDegree A w) (unitDegree A wNext) := by
  have hbne := b_ne_secondaryRecipient (unitDegree A w) (unitDegree A wNext)
  simp only [tokens, recipientSet, Finset.mem_insert, Finset.mem_singleton]
  by_cases hpb : p = b
  · subst p
    simp [hbne]
  · by_cases hps : p = secondaryRecipient (unitDegree A w) (unitDegree A wNext)
    · simp [hps]
    · simp [hpb, hps]

lemma row_sum (A : Finset Point)
    (hbA : b ∈ A)
    (hsA : secondaryRecipient (unitDegree A w) (unitDegree A wNext) ∈ A) :
    ∑ p ∈ A, tokens A p = 2 := by
  simp only [tokens, Finset.sum_add_distrib]
  simp [hbA, hsA]

lemma secondary_degree_le_five (A : Finset Point)
    (he : unitDegree A e ≤ 4) :
    unitDegree A (secondaryRecipient (unitDegree A w) (unitDegree A wNext)) ≤ 5 := by
  simp only [secondaryRecipient]
  split_ifs with hw hwNext
  · exact hw
  · exact hwNext
  · exact he.trans (by omega)

/-- The existing coordinate completion theorem turns a hypothetical sixth
neighbor of `b` into the forbidden straight continuation through the source.
This is the exact bridge from regular-hexagon rigidity to the degree bound
used by the Case 2 transfer. -/
lemma b_degree_le_five_of_no_straight_continuation (A : Finset Point)
    (hsep : IsOneSeparated A)
    (hdisplay : displayedFiveAtB ⊆ A)
    (hleSix : unitDegree A b ≤ 6)
    (hnoStraight : uNext ∉ A) :
    unitDegree A b ≤ 5 := by
  have hneSix : unitDegree A b ≠ 6 := by
    intro hsix
    apply hnoStraight
    exact uNext_mem_of_card_unitNeighbors_b_eq_six hsep hdisplay hsix
  omega

lemma tokens_eq_one_of_mem (A : Finset Point) {p : Point}
    (hp : p ∈ recipientSet (unitDegree A w) (unitDegree A wNext)) :
    tokens A p = 1 := by
  have hbne := b_ne_secondaryRecipient (unitDegree A w) (unitDegree A wNext)
  simp only [recipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · simp [tokens, hbne]
  · simp [tokens, hbne.symm]

/-- The sharp horizontal locality bound for every canonical Case 2
recipient. -/
lemma recipient_horizontal_le_three_halves {degreeW degreeWNext : ℕ} {p : Point}
    (hp : p ∈ recipientSet degreeW degreeWNext) :
    |p 0| ≤ 3 / 2 := by
  simp only [recipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | hp
  · norm_num [b]
  · simp only [secondaryRecipient] at hp
    split_ifs at hp
    · subst p
      norm_num [w]
    · subst p
      norm_num [wNext]
    · subst p
      norm_num [e]

/-- Complete local transfer with the genuine hull-exclusion input kept
explicit.  This is the constructor used in an actual cyclic hull: remote
hull vertices need not lie on the opposite side of the source support line. -/
theorem localTransfer_of_target_exclusion (A H : Finset Point)
    (hnotHull : ∀ p ∈ recipientSet (unitDegree A w) (unitDegree A wNext), p ∉ H)
    (hrec : recipientSet (unitDegree A w) (unitDegree A wNext) ⊆ A)
    (hb : unitDegree A b ≤ 5)
    (he : unitDegree A e ≤ 4) :
    Nonempty (LocalTransfer A H u 2) := by
  let s := secondaryRecipient (unitDegree A w) (unitDegree A wNext)
  have hsdeg : unitDegree A s ≤ 5 := by
    exact secondary_degree_le_five A he
  have hbmem : b ∈ recipientSet (unitDegree A w) (unitDegree A wNext) := by
    simp [recipientSet]
  have hsmem : s ∈ recipientSet (unitDegree A w) (unitDegree A wNext) := by
    simp [recipientSet, s]
  refine ⟨
    { recipients := recipientSet (unitDegree A w) (unitDegree A wNext)
      tokens := tokens A
      positive_iff_mem := tokens_positive_iff_mem A
      recipients_subset_configuration := hrec
      row_sum := row_sum A (hrec hbmem) (hrec hsmem)
      target_not_hull := ?_
      target_capacity := ?_
      target_horizontal_le_three_halves := ?_
      target_in_rectangle := ?_
      target_below_support := ?_
      target_within_two := ?_ }⟩
  · exact hnotHull
  · intro p hp
    have ht : tokens A p = 1 := tokens_eq_one_of_mem A hp
    simp only [recipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp only [ht]
      omega
    · simp only [ht]
      change 2 * unitDegree A s + 1 ≤ 12
      omega
  · intro p hp
    exact recipient_horizontal_le_three_halves hp
  · intro p hp
    exact (mem_recipientSet_geometry hp).1
  · intro p hp
    exact (mem_recipientSet_geometry hp).2.1
  · intro p hp
    exact (mem_recipientSet_geometry hp).2.2

/-- Canonical-coordinate wrapper for a hull set lying on the opposite side
of the support line.  Actual cyclic-hull integrations should use
`localTransfer_of_target_exclusion` instead. -/
theorem localTransfer (A H : Finset Point)
    (hH : HullAboveSupport H)
    (hrec : recipientSet (unitDegree A w) (unitDegree A wNext) ⊆ A)
    (hb : unitDegree A b ≤ 5)
    (he : unitDegree A e ≤ 4) :
    Nonempty (LocalTransfer A H u 2) := by
  apply localTransfer_of_target_exclusion A H
  · intro p hp
    exact not_mem_hull_of_belowSupport hH (mem_recipientSet_geometry hp).2.1
  · exact hrec
  · exact hb
  · exact he

/-- Case 2 constructor with the outer-target degree bound discharged by the
checked regular-hexagon completion at `b`.  The only degree input left is the
paper's final-sector estimate `deg(e) ≤ 4`. -/
theorem localTransfer_of_no_straight_continuation (A H : Finset Point)
    (hH : HullAboveSupport H)
    (hsep : IsOneSeparated A)
    (hbA : b ∈ A)
    (hdisplay : displayedFiveAtB ⊆ A)
    (hbLeSix : unitDegree A b ≤ 6)
    (hnoStraight : uNext ∉ A)
    (he : unitDegree A e ≤ 4) :
    Nonempty (LocalTransfer A H u 2) := by
  have hrec : recipientSet (unitDegree A w) (unitDegree A wNext) ⊆ A := by
    intro p hp
    simp only [recipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | hp
    · exact hbA
    · simp only [secondaryRecipient] at hp
      split_ifs at hp
      · subst p
        exact hdisplay (by simp [displayedFiveAtB])
      · subst p
        exact hdisplay (by simp [displayedFiveAtB])
      · subst p
        exact hdisplay (by simp [displayedFiveAtB])
  exact localTransfer A H hH hrec
    (b_degree_le_five_of_no_straight_continuation
      A hsep hdisplay hbLeSix hnoStraight) he

/-- Fully geometric Case 2 constructor.  The global degree-six bound, the
straight-continuation exclusion at `b`, and the final-sector bound at `e`
are all derived from one-separation and strict support. -/
theorem localTransfer_of_strict_support (A H : Finset Point)
    (hH : HullAboveSupport H)
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A {uPrev, u})
    (hbA : b ∈ A)
    (hdisplay : displayedFiveAtB ⊆ A) :
    Nonempty (LocalTransfer A H u 2) := by
  exact localTransfer_of_no_straight_continuation A H hH hsep hbA hdisplay
    (unitDegree_le_six hsep b)
    (case2_uNext_not_mem_of_strict_support hstrict)
    (unitDegree_e_le_four_of_strict_support hsep hstrict hbA)

/-- Actual-hull Case 2 constructor.  It makes no global half-plane claim
about the hull; the caller supplies the local extreme-neighbor conclusion
that the selected recipients are not hull vertices. -/
theorem localTransfer_of_strict_support_and_target_exclusion (A H : Finset Point)
    (hnotHull : ∀ p ∈ recipientSet (unitDegree A w) (unitDegree A wNext), p ∉ H)
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A {uPrev, u})
    (hbA : b ∈ A)
    (hdisplay : displayedFiveAtB ⊆ A) :
    Nonempty (LocalTransfer A H u 2) := by
  have hrec : recipientSet (unitDegree A w) (unitDegree A wNext) ⊆ A := by
    intro p hp
    simp only [recipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | hp
    · exact hbA
    · simp only [secondaryRecipient] at hp
      split_ifs at hp
      · subst p
        exact hdisplay (by simp [displayedFiveAtB])
      · subst p
        exact hdisplay (by simp [displayedFiveAtB])
      · subst p
        exact hdisplay (by simp [displayedFiveAtB])
  exact localTransfer_of_target_exclusion A H hnotHull hrec
    (b_degree_le_five_of_no_straight_continuation A hsep hdisplay
      (unitDegree_le_six hsep b)
      (case2_uNext_not_mem_of_strict_support hstrict))
    (unitDegree_e_le_four_of_strict_support hsep hstrict hbA)

end Case2

namespace Case4

open Erdos957Cases24.Case4

/-! ### The arbitrary-angle farthest-below neighbour

The displayed triangular-lattice picture below is only a specialization of
the paper's Case 4.  In the genuine construction the middle point is fixed
by the two adjacent hull sources, but its remaining three unit neighbours
need not have the displayed lattice coordinates.  Dumitrescu first chooses
among those three a point farthest below the common supporting line.  The
following definitions retain that choice before any regular-hexagon
rigidity is invoked.
-/

/-- Unit neighbours of the normalized Case-4 middle other than the two
adjacent hull sources. -/
def residualNeighbors (A : Finset Point) : Finset Point :=
  ((unitNeighbors A v).erase Erdos957Cases24.Case2.uPrev).erase
    Erdos957Cases24.Case2.u

@[simp] lemma mem_residualNeighbors {A : Finset Point} {q : Point} :
    q ∈ residualNeighbors A ↔
      q ∈ A ∧ dist v q = 1 ∧
        q ≠ Erdos957Cases24.Case2.uPrev ∧
        q ≠ Erdos957Cases24.Case2.u := by
  simp only [residualNeighbors, Finset.mem_erase,
    Erdos957Cases24.mem_unitNeighbors]
  tauto

/-- The coordinate key used to make the paper's farthest-below choice
deterministic.  Smaller height is farther from the support line; the first
coordinate only breaks ties. -/
def residualOrderKey (q : Point) : ℝ ×ₗ ℝ :=
  toLex (q 1, q 0)

/-- Euclidean dot product of the two rays based at `center`, written in
coordinates so the Case-4 phase inequalities remain transparent. -/
def directionDot (center x y : Point) : ℝ :=
  (x 0 - center 0) * (y 0 - center 0) +
    (x 1 - center 1) * (y 1 - center 1)

/-- Formula-retaining form of the farthest-below residual neighbour.  The
lexicographic minimum records both the genuine height extremum and a stable
left-to-right tie break, which later collision arguments may inspect. -/
structure FarthestBelowData (A : Finset Point) where
  point : Point
  point_mem : point ∈ residualNeighbors A
  order_min : ∀ q ∈ residualNeighbors A,
    residualOrderKey point ≤ residualOrderKey q

lemma FarthestBelowData.height_le {A : Finset Point}
    (D : FarthestBelowData A) {q : Point} (hq : q ∈ residualNeighbors A) :
    D.point 1 ≤ q 1 := by
  exact Prod.Lex.monotone_fst _ _ (D.order_min q hq)

/-- The two source-specific recipients in the high-farthest branch of
Du19 Case 4.  They are actual residual neighbours of the middle and the two
unit contacts adjacent to the farthest point in its regular hexagon.  Their
left-to-right order is retained for the collision analysis. -/
structure HighFarthestRecipients (A : Finset Point)
    (D : FarthestBelowData A) where
  left : Point
  right : Point
  left_mem : left ∈ residualNeighbors A
  right_mem : right ∈ residualNeighbors A
  left_contact : dist D.point left = 1
  right_contact : dist D.point right = 1
  distinct : left ≠ right
  left_x_le_point : left 0 ≤ D.point 0
  point_x_le_right : D.point 0 ≤ right 0
  /-- The paper reflects the common-edge chart when necessary before
  assuming its displayed angle inequalities.  We retain both honest
  alternatives instead of silently fixing the favorable orientation. -/
  orientation : Bool
  orientation_roles :
    if orientation then
      directionDot v left Erdos957Cases24.Case2.uPrev ≤ 0 ∧
        0 ≤ directionDot v right Erdos957Cases24.Case2.u
    else
      0 ≤ directionDot v left Erdos957Cases24.Case2.uPrev ∧
        directionDot v right Erdos957Cases24.Case2.u ≤ 0
  left_degree_le_five : unitDegree A left ≤ 5
  right_degree_le_five : unitDegree A right ≤ 5

/-- The recipient assigned to one of the two sources.  `false` selects the
left contact and `true` the right contact.  The orientation flag is kept as
separate evidence: it records which of the two symmetric phase alternatives
holds, but never silently relabels the actual recipient vertices. -/
def HighFarthestRecipients.sourceRecipient {A : Finset Point}
    {D : FarthestBelowData A} (R : HighFarthestRecipients A D)
    (rightSource : Bool) : Point :=
  if rightSource then R.right else R.left

@[simp] lemma HighFarthestRecipients.sourceRecipient_false
    {A : Finset Point} {D : FarthestBelowData A}
    (R : HighFarthestRecipients A D) :
    R.sourceRecipient false = R.left := rfl

@[simp] lemma HighFarthestRecipients.sourceRecipient_true
    {A : Finset Point} {D : FarthestBelowData A}
    (R : HighFarthestRecipients A D) :
    R.sourceRecipient true = R.right := rfl

lemma HighFarthestRecipients.sourceRecipient_mem
    {A : Finset Point} {D : FarthestBelowData A}
    (R : HighFarthestRecipients A D) (rightSource : Bool) :
    R.sourceRecipient rightSource ∈ residualNeighbors A := by
  cases rightSource
  · exact R.left_mem
  · exact R.right_mem

lemma HighFarthestRecipients.sourceRecipient_contact
    {A : Finset Point} {D : FarthestBelowData A}
    (R : HighFarthestRecipients A D) (rightSource : Bool) :
    dist D.point (R.sourceRecipient rightSource) = 1 := by
  cases rightSource
  · exact R.left_contact
  · exact R.right_contact

lemma HighFarthestRecipients.sourceRecipient_degree_le_five
    {A : Finset Point} {D : FarthestBelowData A}
    (R : HighFarthestRecipients A D) (rightSource : Bool) :
    unitDegree A (R.sourceRecipient rightSource) ≤ 5 := by
  cases rightSource
  · exact R.left_degree_le_five
  · exact R.right_degree_le_five

lemma HighFarthestRecipients.orientation_roles_of_eq_true
    {A : Finset Point} {D : FarthestBelowData A}
    (R : HighFarthestRecipients A D) (h : R.orientation = true) :
    directionDot v R.left Erdos957Cases24.Case2.uPrev ≤ 0 ∧
      0 ≤ directionDot v R.right Erdos957Cases24.Case2.u := by
  simpa [h] using R.orientation_roles

lemma HighFarthestRecipients.orientation_roles_of_eq_false
    {A : Finset Point} {D : FarthestBelowData A}
    (R : HighFarthestRecipients A D) (h : R.orientation = false) :
    0 ≤ directionDot v R.left Erdos957Cases24.Case2.uPrev ∧
      directionDot v R.right Erdos957Cases24.Case2.u ≤ 0 := by
  simpa [h] using R.orientation_roles

/-- The exact two Du19 subbranches once the middle has degree five: either
the farthest-below residual itself has degree at most five, or its degree is
six and the two ordered side recipients are available. -/
inductive FarthestBranchData (A : Finset Point)
    (D : FarthestBelowData A) : Type
  | low (point_degree_le_five : unitDegree A D.point ≤ 5)
  | high (point_degree_six : unitDegree A D.point = 6)
      (recipients : HighFarthestRecipients A D)

/-- The non-middle recipient used by one source in the selected Du19
degree-five subbranch.  In the low branch it is the farthest-below point
itself; in the high branch it is the source's ordered common contact. -/
def FarthestBranchData.sourceRecipient {A : Finset Point}
    {D : FarthestBelowData A} (B : FarthestBranchData A D)
    (rightSource : Bool) : Point :=
  match B with
  | .low _ => D.point
  | .high _ R => R.sourceRecipient rightSource

@[simp] lemma FarthestBranchData.sourceRecipient_low
    {A : Finset Point} {D : FarthestBelowData A}
    (hdegree : unitDegree A D.point ≤ 5) (rightSource : Bool) :
    (FarthestBranchData.low hdegree).sourceRecipient rightSource = D.point := rfl

@[simp] lemma FarthestBranchData.sourceRecipient_high
    {A : Finset Point} {D : FarthestBelowData A}
    (hdegree : unitDegree A D.point = 6)
    (R : HighFarthestRecipients A D) (rightSource : Bool) :
    (FarthestBranchData.high hdegree R).sourceRecipient rightSource =
      R.sourceRecipient rightSource := rfl

lemma FarthestBranchData.sourceRecipient_mem
    {A : Finset Point} {D : FarthestBelowData A}
    (B : FarthestBranchData A D) (rightSource : Bool) :
    B.sourceRecipient rightSource ∈ residualNeighbors A := by
  cases B with
  | low _ => exact D.point_mem
  | high _ R => exact R.sourceRecipient_mem rightSource

lemma FarthestBranchData.sourceRecipient_degree_le_five
    {A : Finset Point} {D : FarthestBelowData A}
    (B : FarthestBranchData A D) (rightSource : Bool) :
    unitDegree A (B.sourceRecipient rightSource) ≤ 5 := by
  cases B with
  | low hdegree => exact hdegree
  | high _ R => exact R.sourceRecipient_degree_le_five rightSource

lemma FarthestBranchData.sourceRecipient_ne_v
    {A : Finset Point} {D : FarthestBelowData A}
    (B : FarthestBranchData A D) (rightSource : Bool) :
    B.sourceRecipient rightSource ≠ v := by
  intro h
  have hdist :=
    (mem_residualNeighbors.mp (B.sourceRecipient_mem rightSource)).2.1
  rw [h, dist_self] at hdist
  norm_num at hdist

/-- The exact two targets of one source row in either farthest-below
subbranch.  This definition is formula-retaining and is the canonical API
used by the actual cyclic-hull classification. -/
def branchRecipientSet {A : Finset Point} {D : FarthestBelowData A}
    (B : FarthestBranchData A D) (rightSource : Bool) : Finset Point :=
  {v, B.sourceRecipient rightSource}

/-- Each source sends one doubled token to the middle and one to its
branch-specific secondary recipient. -/
def branchTokens {A : Finset Point} {D : FarthestBelowData A}
    (B : FarthestBranchData A D) (rightSource : Bool) (p : Point) : ℕ :=
  (if p = v then 1 else 0) +
    (if p = B.sourceRecipient rightSource then 1 else 0)

lemma branchTokens_positive_iff_mem
    {A : Finset Point} {D : FarthestBelowData A}
    (B : FarthestBranchData A D) (rightSource : Bool) (p : Point) :
    0 < branchTokens B rightSource p ↔
      p ∈ branchRecipientSet B rightSource := by
  by_cases hpv : p = v <;>
    by_cases hpt : p = B.sourceRecipient rightSource <;>
      simp [branchTokens, branchRecipientSet, hpv, hpt]

lemma branchTokens_eq_one_of_mem
    {A : Finset Point} {D : FarthestBelowData A}
    (B : FarthestBranchData A D) (rightSource : Bool) {p : Point}
    (hp : p ∈ branchRecipientSet B rightSource) :
    branchTokens B rightSource p = 1 := by
  have hne := B.sourceRecipient_ne_v rightSource
  simp only [branchRecipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · simp [branchTokens, hne.symm]
  · simp [branchTokens, hne]

lemma branchRecipientSet_subset {A : Finset Point}
    {D : FarthestBelowData A} (B : FarthestBranchData A D)
    (rightSource : Bool) (hvA : v ∈ A) :
    branchRecipientSet B rightSource ⊆ A := by
  intro p hp
  simp only [branchRecipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact hvA
  · exact (mem_residualNeighbors.mp (B.sourceRecipient_mem rightSource)).1

lemma branchRowSum {A : Finset Point} {D : FarthestBelowData A}
    (B : FarthestBranchData A D) (rightSource : Bool) (hvA : v ∈ A) :
    ∑ p ∈ A, branchTokens B rightSource p = 2 := by
  have htA := (mem_residualNeighbors.mp
    (B.sourceRecipient_mem rightSource)).1
  simp only [branchTokens, Finset.sum_add_distrib]
  simp [hvA, htA]

/-- At middle degree five, deleting the two adjacent source neighbours
leaves exactly the three residual neighbours appearing in Case 4. -/
lemma card_residualNeighbors_eq_three {A : Finset Point}
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ A)
    (hu : Erdos957Cases24.Case2.u ∈ A)
    (hdegree : unitDegree A v = 5) :
    (residualNeighbors A).card = 3 := by
  have huPrevN : Erdos957Cases24.Case2.uPrev ∈ unitNeighbors A v := by
    exact Erdos957Cases24.mem_unitNeighbors.mpr ⟨huPrev, by
      simpa [v, dist_comm] using Erdos957Cases24.Case2.dist_uPrev_v⟩
  have huN : Erdos957Cases24.Case2.u ∈ unitNeighbors A v := by
    exact Erdos957Cases24.mem_unitNeighbors.mpr ⟨hu, by
      simpa [v, dist_comm] using Erdos957Cases24.Case2.dist_u_v⟩
  have hne : Erdos957Cases24.Case2.u ≠
      Erdos957Cases24.Case2.uPrev := by
    intro h
    have hudist := Erdos957Cases24.Case2.dist_uPrev_u
    rw [← h, dist_self] at hudist
    norm_num at hudist
  have huErase : Erdos957Cases24.Case2.u ∈
      (unitNeighbors A v).erase Erdos957Cases24.Case2.uPrev :=
    Finset.mem_erase.mpr ⟨hne, huN⟩
  rw [residualNeighbors, Finset.card_erase_of_mem huErase,
    Finset.card_erase_of_mem huPrevN]
  change (unitNeighbors A v).card - 1 - 1 = 3
  change (unitNeighbors A v).card = 5 at hdegree
  omega

/-- The farthest-below residual neighbour used by Du19 exists without any
lattice-rigidity assumption. -/
theorem exists_farthestBelowData {A : Finset Point}
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ A)
    (hu : Erdos957Cases24.Case2.u ∈ A)
    (hdegree : unitDegree A v = 5) :
    Nonempty (FarthestBelowData A) := by
  have hcard := card_residualNeighbors_eq_three huPrev hu hdegree
  have hnonempty : (residualNeighbors A).Nonempty := by
    exact Finset.card_pos.mp (by omega)
  obtain ⟨w, hw, hmin⟩ :=
    (residualNeighbors A).exists_min_image residualOrderKey hnonempty
  exact ⟨⟨w, hw, hmin⟩⟩

lemma residual_below_support {A : Finset Point}
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    {q : Point} (hq : q ∈ residualNeighbors A) : BelowSupport q := by
  have hdata := mem_residualNeighbors.mp hq
  exact hstrict q hdata.1 (by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      ⟨hdata.2.2.1, hdata.2.2.2⟩)

/-- Every arbitrary residual neighbour is horizontally within `3/2` of
the normalized left endpoint.  This is the sharp chart-transport bound
needed for the original `7/4` source rectangle. -/
lemma residual_horizontal_le_three_halves {A : Finset Point} {q : Point}
    (hq : q ∈ residualNeighbors A) : |q 0| ≤ 3 / 2 := by
  have hdist := (mem_residualNeighbors.mp hq).2.1
  have hsq := congrArg (fun t : ℝ ↦ t ^ 2) hdist
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hsq
  simp only [v, Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one] at hsq
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (-(Erdos957Cases24.sqrtThree / 2) - q 1)]

lemma residual_in_transferRectangle {A : Finset Point}
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    {q : Point} (hq : q ∈ residualNeighbors A) :
    InTransferRectangle q := by
  have hhorizontal := residual_horizontal_le_three_halves hq
  have hbelow := residual_below_support hstrict hq
  have hdist := (mem_residualNeighbors.mp hq).2.1
  have hsq := congrArg (fun t : ℝ ↦ t ^ 2) hdist
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hsq
  simp only [v, Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one] at hsq
  have hsqrtLe := Erdos957Cases24.sqrtThree_le_two
  rw [abs_le] at hhorizontal
  rw [InTransferRectangle]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg (-(1 / 2 : ℝ) - q 0)]
  · exact hbelow.le

/-- The doubled-token version of the three Case 4 degree branches. -/
def tokens (A : Finset Point) (p : Point) : ℕ :=
  if unitDegree A v ≤ 4 then
    if p = v then 4 else 0
  else if unitDegree A w ≤ 5 then
    (if p = v then 2 else 0) + (if p = w then 2 else 0)
  else
    (if p = v then 2 else 0) +
      (if p = a then 1 else 0) + (if p = b then 1 else 0)

lemma v_ne_w : v ≠ w := by
  intro h
  have h0 := congrArg (fun p : Point ↦ p 0) h
  norm_num [v, w, Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.w] at h0

lemma v_ne_a : v ≠ a := by
  intro h
  have h0 := congrArg (fun p : Point ↦ p 0) h
  norm_num [v, Erdos957Cases24.Case2.v, a] at h0

lemma v_ne_b : v ≠ b := by
  intro h
  have h0 := congrArg (fun p : Point ↦ p 0) h
  norm_num [v, Erdos957Cases24.Case2.v, b, Erdos957Cases24.Case2.b] at h0

lemma a_ne_b : a ≠ b := by
  intro h
  have h0 := congrArg (fun p : Point ↦ p 0) h
  norm_num [a, b, Erdos957Cases24.Case2.b] at h0

lemma a_add_v_sub_w_eq_vMissing : a + v - w = vMissing := by
  ext i
  fin_cases i
  · change (-1 : ℝ) + (-(1 / 2)) - 0 = -(3 / 2)
    norm_num
  · change -sqrtThree + (-(sqrtThree / 2)) - (-sqrtThree) = -(sqrtThree / 2)
    ring

lemma b_add_u_sub_v_eq_uNext :
    b + Erdos957Cases24.Case2.u - v = Erdos957Cases24.Case2.uNext := by
  ext i
  fin_cases i
  · change (1 / 2 : ℝ) + 0 - (-(1 / 2)) = 1
    norm_num
  · change -(sqrtThree / 2) + 0 - (-(sqrtThree / 2)) = 0
    ring

/-- The left Case 4 degree-six implication, now derived from the arbitrary
unit-chord completion theorem. -/
lemma a_six_forces_vMissing_mem {A : Finset Point}
    (hsep : IsOneSeparated A) (hvA : v ∈ A) (hwA : w ∈ A)
    (haSix : unitDegree A a = 6) : vMissing ∈ A := by
  rw [← a_add_v_sub_w_eq_vMissing]
  exact hexagon_completion_mem hsep hvA hwA
    (by simpa [dist_comm] using dist_v_a)
    (by simpa [dist_comm] using dist_w_a)
    (by simpa [v, w] using Erdos957Cases24.Case2.dist_v_w) haSix

/-- The right Case 4 degree-six implication: completion of the adjacent
neighbors `u,v` at `b` is the forbidden straight continuation `uNext`. -/
lemma b_six_forces_uNext_mem {A : Finset Point}
    (hsep : IsOneSeparated A)
    (huA : Erdos957Cases24.Case2.u ∈ A) (hvA : v ∈ A)
    (hbSix : unitDegree A b = 6) : Erdos957Cases24.Case2.uNext ∈ A := by
  rw [← b_add_u_sub_v_eq_uNext]
  exact hexagon_completion_mem hsep huA hvA
    (by simpa [b, dist_comm] using Erdos957Cases24.Case2.dist_u_b)
    (by simpa [v, b, dist_comm] using Erdos957Cases24.Case2.dist_v_b)
    (by simpa [v] using Erdos957Cases24.Case2.dist_u_v) hbSix

/-! ### Source-indexed Case 4 rows -/

/-- `false` is the left source and `true` the right source. -/
def sideSource (right : Bool) : Point :=
  if right then Erdos957Cases24.Case2.u else Erdos957Cases24.Case2.uPrev

/-- In the final branch each source uses its own common neighbor. -/
def sideTarget (right : Bool) : Point := if right then b else a

def sideRecipientSet (A : Finset Point) (right : Bool) : Finset Point :=
  if unitDegree A v ≤ 4 then {v}
  else if unitDegree A w ≤ 5 then {v, w}
  else {v, sideTarget right}

/-- Each source emits exactly two doubled tokens. -/
def sideTokens (A : Finset Point) (right : Bool) (p : Point) : ℕ :=
  if unitDegree A v ≤ 4 then
    if p = v then 2 else 0
  else if unitDegree A w ≤ 5 then
    (if p = v then 1 else 0) + (if p = w then 1 else 0)
  else
    (if p = v then 1 else 0) + (if p = sideTarget right then 1 else 0)

lemma sideTarget_ne_v (right : Bool) : sideTarget right ≠ v := by
  cases right
  · simpa [sideTarget] using v_ne_a.symm
  · simpa [sideTarget] using v_ne_b.symm

lemma sideTokens_positive_iff_mem (A : Finset Point) (right : Bool) (p : Point) :
    0 < sideTokens A right p ↔ p ∈ sideRecipientSet A right := by
  by_cases hv4 : unitDegree A v ≤ 4
  · by_cases hpv : p = v <;>
      simp [sideTokens, sideRecipientSet, hv4, hpv]
  · by_cases hw5 : unitDegree A w ≤ 5
    · by_cases hpv : p = v
      · simp [sideTokens, sideRecipientSet, hv4, hw5, hpv]
      · by_cases hpw : p = w <;>
          simp [sideTokens, sideRecipientSet, hv4, hw5, hpv, hpw]
    · by_cases hpv : p = v
      · simp [sideTokens, sideRecipientSet, hv4, hw5, hpv]
      · by_cases hps : p = sideTarget right <;>
          simp [sideTokens, sideRecipientSet, hv4, hw5, hpv, hps]

lemma sideRowSum (A : Finset Point) (right : Bool)
    (hrec : sideRecipientSet A right ⊆ A) :
    ∑ p ∈ A, sideTokens A right p = 2 := by
  have hvMem : v ∈ sideRecipientSet A right := by
    simp only [sideRecipientSet]
    split_ifs <;> simp
  by_cases hv4 : unitDegree A v ≤ 4
  · simp [sideTokens, hv4, hrec hvMem]
  · by_cases hw5 : unitDegree A w ≤ 5
    · have hwMem : w ∈ sideRecipientSet A right := by
        simp [sideRecipientSet, hv4, hw5]
      simp only [sideTokens, hv4, if_false, hw5, if_true,
        Finset.sum_add_distrib]
      simp [hrec hvMem, hrec hwMem]
    · have hsMem : sideTarget right ∈ sideRecipientSet A right := by
        simp [sideRecipientSet, hv4, hw5]
      simp only [sideTokens, hv4, if_false, hw5, Finset.sum_add_distrib]
      simp [hrec hvMem, hrec hsMem]

lemma uPrev_within_two_v :
    WithinTwoUnitEdges Erdos957Cases24.Case2.uPrev v := by
  exact Or.inl (by simpa [UnitAdjacent, v] using Erdos957Cases24.Case2.dist_uPrev_v)

lemma sideSource_within_two_branchRecipient {A : Finset Point}
    {D : FarthestBelowData A} (B : FarthestBranchData A D)
    (rightSource : Bool) :
    WithinTwoUnitEdges (sideSource rightSource)
      (B.sourceRecipient rightSource) := by
  have htarget :=
    (mem_residualNeighbors.mp (B.sourceRecipient_mem rightSource)).2.1
  cases rightSource
  · exact Or.inr ⟨v,
      by simpa [sideSource, UnitAdjacent, v] using
        Erdos957Cases24.Case2.dist_uPrev_v,
      by simpa [UnitAdjacent] using htarget⟩
  · exact Or.inr ⟨v,
      by simpa [sideSource, UnitAdjacent, v] using
        Erdos957Cases24.Case2.dist_u_v,
      by simpa [UnitAdjacent] using htarget⟩

lemma branchRecipient_degree_le_five {A : Finset Point}
    {D : FarthestBelowData A} (B : FarthestBranchData A D)
    (rightSource : Bool) (hvDegree : unitDegree A v = 5) {p : Point}
    (hp : p ∈ branchRecipientSet B rightSource) :
    unitDegree A p ≤ 5 := by
  simp only [branchRecipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · omega
  · exact B.sourceRecipient_degree_le_five rightSource

lemma branchRecipient_horizontal_le_three_halves {A : Finset Point}
    {D : FarthestBelowData A} (B : FarthestBranchData A D)
    (rightSource : Bool) {p : Point}
    (hp : p ∈ branchRecipientSet B rightSource) :
    |p 0| ≤ 3 / 2 := by
  simp only [branchRecipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · norm_num [v, Erdos957Cases24.Case2.v]
  · exact residual_horizontal_le_three_halves
      (B.sourceRecipient_mem rightSource)

lemma branchRecipient_in_rectangle {A : Finset Point}
    {D : FarthestBelowData A} (B : FarthestBranchData A D)
    (rightSource : Bool)
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    {p : Point} (hp : p ∈ branchRecipientSet B rightSource) :
    InTransferRectangle p := by
  simp only [branchRecipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact Erdos957Cases24.Case4.v_in_rectangle
  · exact residual_in_transferRectangle hstrict
      (B.sourceRecipient_mem rightSource)

lemma branchRecipient_below_support {A : Finset Point}
    {D : FarthestBelowData A} (B : FarthestBranchData A D)
    (rightSource : Bool)
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    {p : Point} (hp : p ∈ branchRecipientSet B rightSource) :
    BelowSupport p := by
  simp only [branchRecipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact Erdos957Cases24.Case4.v_below_support
  · exact residual_below_support hstrict
      (B.sourceRecipient_mem rightSource)

lemma branchRecipient_within_two {A : Finset Point}
    {D : FarthestBelowData A} (B : FarthestBranchData A D)
    (rightSource : Bool) {p : Point}
    (hp : p ∈ branchRecipientSet B rightSource) :
    WithinTwoUnitEdges (sideSource rightSource) p := by
  simp only [branchRecipientSet, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · cases rightSource
    · simpa [sideSource] using uPrev_within_two_v
    · simpa [sideSource] using Erdos957Cases24.Case4.u_within_two_v
  · exact sideSource_within_two_branchRecipient B rightSource

/-- Honest arbitrary-angle Case-4 source row after the farthest-below
branch has been selected.  It emits one token to the actual middle and one
to the exact low/contact recipient retained by `FarthestBranchData`.
No triangular-lattice rigidity or capacity assumption remains. -/
theorem sourceLocalTransfer_of_farthestBranch_and_target_exclusion
    (A H : Finset Point) (rightSource : Bool)
    (D : FarthestBelowData A) (B : FarthestBranchData A D)
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    (hvA : v ∈ A) (hvDegree : unitDegree A v = 5)
    (hnotHull : ∀ p ∈ branchRecipientSet B rightSource, p ∉ H) :
    Nonempty (LocalTransfer A H (sideSource rightSource) 2) := by
  refine ⟨
    { recipients := branchRecipientSet B rightSource
      tokens := branchTokens B rightSource
      positive_iff_mem := branchTokens_positive_iff_mem B rightSource
      recipients_subset_configuration :=
        branchRecipientSet_subset B rightSource hvA
      row_sum := branchRowSum B rightSource hvA
      target_not_hull := hnotHull
      target_capacity := ?_
      target_horizontal_le_three_halves := ?_
      target_in_rectangle := ?_
      target_below_support := ?_
      target_within_two := ?_ }⟩
  · intro p hp
    have hdegree := branchRecipient_degree_le_five B rightSource hvDegree hp
    rw [branchTokens_eq_one_of_mem B rightSource hp]
    omega
  · intro p hp
    exact branchRecipient_horizontal_le_three_halves B rightSource hp
  · intro p hp
    exact branchRecipient_in_rectangle B rightSource hstrict hp
  · intro p hp
    exact branchRecipient_below_support B rightSource hstrict hp
  · intro p hp
    exact branchRecipient_within_two B rightSource hp

lemma uPrev_within_two_w :
    WithinTwoUnitEdges Erdos957Cases24.Case2.uPrev w := by
  exact Or.inr ⟨v,
    by simpa [UnitAdjacent, v] using Erdos957Cases24.Case2.dist_uPrev_v,
    by simpa [UnitAdjacent, v, w] using Erdos957Cases24.Case2.dist_v_w⟩

lemma uPrev_within_two_a :
    WithinTwoUnitEdges Erdos957Cases24.Case2.uPrev a := by
  exact Or.inr ⟨v,
    by simpa [UnitAdjacent, v] using Erdos957Cases24.Case2.dist_uPrev_v,
    by simpa [UnitAdjacent] using dist_v_a⟩

lemma sideTarget_geometry (right : Bool) :
    InTransferRectangle (sideTarget right) ∧
      BelowSupport (sideTarget right) ∧
      WithinTwoUnitEdges (sideSource right) (sideTarget right) := by
  cases right
  · exact ⟨a_in_rectangle, a_below_support, uPrev_within_two_a⟩
  · exact ⟨b_in_rectangle, b_below_support,
      by simpa [sideSource, sideTarget] using u_within_two_b⟩

lemma sideRecipient_geometry {A : Finset Point} {right : Bool} {p : Point}
    (hp : p ∈ sideRecipientSet A right) :
    InTransferRectangle p ∧ BelowSupport p ∧
      WithinTwoUnitEdges (sideSource right) p := by
  simp only [sideRecipientSet] at hp
  split_ifs at hp
  · have hpv : p = v := by simpa only [Finset.mem_singleton] using hp
    subst p
    cases right
    · exact ⟨v_in_rectangle, v_below_support, uPrev_within_two_v⟩
    · exact ⟨v_in_rectangle, v_below_support,
        by simpa [sideSource] using u_within_two_v⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · cases right
      · exact ⟨v_in_rectangle, v_below_support, uPrev_within_two_v⟩
      · exact ⟨v_in_rectangle, v_below_support,
          by simpa [sideSource] using u_within_two_v⟩
    · cases right
      · exact ⟨w_in_rectangle, w_below_support, uPrev_within_two_w⟩
      · exact ⟨w_in_rectangle, w_below_support,
          by simpa [sideSource] using u_within_two_w⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · cases right
      · exact ⟨v_in_rectangle, v_below_support, uPrev_within_two_v⟩
      · exact ⟨v_in_rectangle, v_below_support,
          by simpa [sideSource] using u_within_two_v⟩
    · exact sideTarget_geometry right

/-- Every source-indexed Case 4 recipient is horizontally within one unit
of the canonical edge origin; in particular it satisfies the requested
`3/2` bound. -/
lemma sideRecipient_horizontal_le_one {A : Finset Point} {right : Bool} {p : Point}
    (hp : p ∈ sideRecipientSet A right) :
    |p 0| ≤ 1 := by
  simp only [sideRecipientSet] at hp
  split_ifs at hp
  · have hpv : p = v := by simpa only [Finset.mem_singleton] using hp
    subst p
    norm_num [v, Erdos957Cases24.Case2.v]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · norm_num [v, Erdos957Cases24.Case2.v]
    · norm_num [w, Erdos957Cases24.Case2.w]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · norm_num [v, Erdos957Cases24.Case2.v]
    · cases right
      · norm_num [sideTarget, a]
      · norm_num [sideTarget, b, Erdos957Cases24.Case2.b]

lemma sideRecipient_horizontal_le_three_halves {A : Finset Point}
    {right : Bool} {p : Point} (hp : p ∈ sideRecipientSet A right) :
    |p 0| ≤ 3 / 2 := by
  exact (sideRecipient_horizontal_le_one hp).trans (by norm_num)

/-- One Case 4 source row with actual hull exclusion supplied explicitly. -/
theorem sourceLocalTransfer_of_target_exclusion (A H : Finset Point) (right : Bool)
    (hnotHull : ∀ p ∈ sideRecipientSet A right, p ∉ H)
    (hrec : sideRecipientSet A right ⊆ A)
    (hv : unitDegree A v ≤ 5)
    (ha : unitDegree A a ≤ 5)
    (hb : unitDegree A b ≤ 5) :
    Nonempty (LocalTransfer A H (sideSource right) 2) := by
  have hsdeg : unitDegree A (sideTarget right) ≤ 5 := by
    cases right
    · simpa [sideTarget] using ha
    · simpa [sideTarget] using hb
  refine ⟨
    { recipients := sideRecipientSet A right
      tokens := sideTokens A right
      positive_iff_mem := sideTokens_positive_iff_mem A right
      recipients_subset_configuration := hrec
      row_sum := sideRowSum A right hrec
      target_not_hull := ?_
      target_capacity := ?_
      target_horizontal_le_three_halves := ?_
      target_in_rectangle := ?_
      target_below_support := ?_
      target_within_two := ?_ }⟩
  · exact hnotHull
  · intro p hp
    by_cases hv4 : unitDegree A v ≤ 4
    · have hpv : p = v := by simpa [sideRecipientSet, hv4] using hp
      subst p
      simp [sideTokens, hv4]
      omega
    · by_cases hw5 : unitDegree A w ≤ 5
      · have hpvw : p = v ∨ p = w := by
          simpa [sideRecipientSet, hv4, hw5] using hp
        rcases hpvw with rfl | rfl
        · simp [sideTokens, hv4, hw5, v_ne_w]
          omega
        · simp [sideTokens, hv4, hw5, v_ne_w.symm]
          omega
      · have hpvs : p = v ∨ p = sideTarget right := by
          simpa [sideRecipientSet, hv4, hw5] using hp
        rcases hpvs with rfl | rfl
        · simp [sideTokens, hv4, hw5, (sideTarget_ne_v right).symm]
          omega
        · simp [sideTokens, hv4, hw5, sideTarget_ne_v]
          omega
  · intro p hp
    exact sideRecipient_horizontal_le_three_halves hp
  · intro p hp
    exact (sideRecipient_geometry hp).1
  · intro p hp
    exact (sideRecipient_geometry hp).2.1
  · intro p hp
    exact (sideRecipient_geometry hp).2.2

/-- Canonical-coordinate half-plane wrapper.  Use
`sourceLocalTransfer_of_target_exclusion` for an actual cyclic hull. -/
theorem sourceLocalTransfer (A H : Finset Point) (right : Bool)
    (hH : HullAboveSupport H)
    (hrec : sideRecipientSet A right ⊆ A)
    (hv : unitDegree A v ≤ 5)
    (ha : unitDegree A a ≤ 5)
    (hb : unitDegree A b ≤ 5) :
    Nonempty (LocalTransfer A H (sideSource right) 2) := by
  apply sourceLocalTransfer_of_target_exclusion A H right
  · intro p hp
    exact not_mem_hull_of_belowSupport hH (sideRecipient_geometry hp).2.1
  · exact hrec
  · exact hv
  · exact ha
  · exact hb

/-- Fully geometric source-indexed Case 4 constructor.  All degree bounds and
continuation exclusions are derived from one-separation, the five displayed
neighbors, exact degree five at the middle point, and strict support. -/
theorem sourceLocalTransfer_of_strict_support (A H : Finset Point) (right : Bool)
    (hH : HullAboveSupport H)
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A {Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.u})
    (hvA : v ∈ A)
    (hfive : displayedFiveAtV ⊆ A)
    (hvDegree : unitDegree A v = 5) :
    Nonempty (LocalTransfer A H (sideSource right) 2) := by
  have huA : Erdos957Cases24.Case2.u ∈ A :=
    hfive (by simp [displayedFiveAtV])
  have hwA : w ∈ A := hfive (by simp [displayedFiveAtV])
  have haA : a ∈ A := hfive (by simp [displayedFiveAtV])
  have hbA : b ∈ A := hfive (by simp [displayedFiveAtV])
  have hrec : sideRecipientSet A right ⊆ A := by
    intro p hp
    simp only [sideRecipientSet] at hp
    split_ifs at hp
    · have hpv : p = v := by simpa only [Finset.mem_singleton] using hp
      exact hpv ▸ hvA
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact hp.elim (fun h ↦ h ▸ hvA) (fun h ↦ h ▸ hwA)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hvA
      · cases right
        · exact haA
        · exact hbA
  have hvLe : unitDegree A v ≤ 5 := by omega
  have haLe : unitDegree A a ≤ 5 := by
    have hleSix := unitDegree_le_six hsep a
    have hmissing := vMissing_not_mem_of_card_unitNeighbors_eq_five hfive hvDegree
    have hneSix : unitDegree A a ≠ 6 := by
      intro hsix
      exact hmissing (a_six_forces_vMissing_mem hsep hvA hwA hsix)
    omega
  have hbLe : unitDegree A b ≤ 5 := by
    have hleSix := unitDegree_le_six hsep b
    have hno := case2_uNext_not_mem_of_strict_support hstrict
    have hneSix : unitDegree A b ≠ 6 := by
      intro hsix
      exact hno (b_six_forces_uNext_mem hsep huA hvA hsix)
    omega
  exact sourceLocalTransfer A H right hH hrec hvLe haLe hbLe

/-- Actual-hull source-indexed Case 4 constructor.  Non-hull status is the
local two-extreme-neighbor classification result, not a false global
half-plane assertion about every hull vertex. -/
theorem sourceLocalTransfer_of_strict_support_and_target_exclusion
    (A H : Finset Point) (right : Bool)
    (hnotHull : ∀ p ∈ sideRecipientSet A right, p ∉ H)
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A {Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.u})
    (hvA : v ∈ A)
    (hfive : displayedFiveAtV ⊆ A)
    (hvDegree : unitDegree A v = 5) :
    Nonempty (LocalTransfer A H (sideSource right) 2) := by
  have huA : Erdos957Cases24.Case2.u ∈ A :=
    hfive (by simp [displayedFiveAtV])
  have hwA : w ∈ A := hfive (by simp [displayedFiveAtV])
  have haA : a ∈ A := hfive (by simp [displayedFiveAtV])
  have hbA : b ∈ A := hfive (by simp [displayedFiveAtV])
  have hrec : sideRecipientSet A right ⊆ A := by
    intro p hp
    simp only [sideRecipientSet] at hp
    split_ifs at hp
    · have hpv : p = v := by simpa only [Finset.mem_singleton] using hp
      exact hpv ▸ hvA
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact hp.elim (fun h ↦ h ▸ hvA) (fun h ↦ h ▸ hwA)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hvA
      · cases right
        · exact haA
        · exact hbA
  have haLe : unitDegree A a ≤ 5 := by
    have hleSix := unitDegree_le_six hsep a
    have hmissing := vMissing_not_mem_of_card_unitNeighbors_eq_five hfive hvDegree
    have hneSix : unitDegree A a ≠ 6 := by
      intro hsix
      exact hmissing (a_six_forces_vMissing_mem hsep hvA hwA hsix)
    omega
  have hbLe : unitDegree A b ≤ 5 := by
    have hleSix := unitDegree_le_six hsep b
    have hno := case2_uNext_not_mem_of_strict_support hstrict
    have hneSix : unitDegree A b ≠ 6 := by
      intro hsix
      exact hno (b_six_forces_uNext_mem hsep huA hvA hsix)
    omega
  exact sourceLocalTransfer_of_target_exclusion A H right hnotHull hrec
    (by omega) haLe hbLe

/-- A reusable final step for the two Case 4 common neighbors: once the
degree-six rigidity calculation forces a point excluded by strict hull
geometry, the target has degree at most five. -/
lemma degree_le_five_of_six_forces_forbidden {A : Finset Point} {p forced : Point}
    (hleSix : unitDegree A p ≤ 6)
    (hforce : unitDegree A p = 6 → forced ∈ A)
    (hforbidden : forced ∉ A) :
    unitDegree A p ≤ 5 := by
  have hne : unitDegree A p ≠ 6 := by
    intro hsix
    exact hforbidden (hforce hsix)
  omega

/-- In the left Case 4 branch, a completion forced at `a` would add
`vMissing` as a sixth neighbor of the five-valent middle point `v`. -/
lemma a_degree_le_five_of_completion (A : Finset Point)
    (hfive : displayedFiveAtV ⊆ A)
    (hvDegree : unitDegree A v = 5)
    (haLeSix : unitDegree A a ≤ 6)
    (haForces : unitDegree A a = 6 → vMissing ∈ A) :
    unitDegree A a ≤ 5 := by
  apply degree_le_five_of_six_forces_forbidden haLeSix haForces
  exact vMissing_not_mem_of_card_unitNeighbors_eq_five hfive hvDegree

/-- The symmetric/right common-neighbor bridge.  Its coordinate rigidity
argument supplies `bForces`; strict extremality supplies `continuation ∉ A`.
Keeping the two facts as separate hypotheses makes the exact remaining
geometry visible to callers. -/
lemma b_degree_le_five_of_completion (A : Finset Point) (continuation : Point)
    (hbLeSix : unitDegree A b ≤ 6)
    (bForces : unitDegree A b = 6 → continuation ∈ A)
    (hnoContinuation : continuation ∉ A) :
    unitDegree A b ≤ 5 := by
  exact degree_le_five_of_six_forces_forbidden hbLeSix bForces hnoContinuation

lemma tokens_positive_iff_mem (A : Finset Point) (p : Point) :
    0 < tokens A p ↔ p ∈ recipientSet (unitDegree A v) (unitDegree A w) := by
  by_cases hv : unitDegree A v ≤ 4
  · by_cases hpv : p = v <;> simp [tokens, recipientSet, hv, hpv]
  · by_cases hw : unitDegree A w ≤ 5
    · by_cases hpv : p = v
      · simp [tokens, recipientSet, hv, hw, hpv]
      · by_cases hpw : p = w <;>
          simp [tokens, recipientSet, hv, hw, hpv, hpw]
    · by_cases hpv : p = v
      · simp [tokens, recipientSet, hv, hw, hpv]
      · by_cases hpa : p = a
        · simp [tokens, recipientSet, hv, hw, hpa]
        · by_cases hpb : p = b <;>
            simp [tokens, recipientSet, hv, hw, hpv, hpa, hpb]

lemma row_sum (A : Finset Point)
    (hvA : v ∈ A) (hwA : w ∈ A) (haA : a ∈ A) (hbA : b ∈ A) :
    ∑ p ∈ A, tokens A p = 4 := by
  by_cases hv : unitDegree A v ≤ 4
  · simp [tokens, hv, hvA]
  · by_cases hw : unitDegree A w ≤ 5
    · simp only [tokens, hv, if_false, hw, if_true, Finset.sum_add_distrib]
      simp [hvA, hwA]
    · simp only [tokens, hv, if_false, hw, Finset.sum_add_distrib]
      simp [hvA, haA, hbA]

/-- The paired (pre source-splitting) Case 4 recipient set satisfies the same
sharp horizontal bound. -/
lemma recipient_horizontal_le_three_halves {degreeV degreeW : ℕ} {p : Point}
    (hp : p ∈ recipientSet degreeV degreeW) :
    |p 0| ≤ 3 / 2 := by
  simp only [recipientSet] at hp
  split_ifs at hp
  · have hpv : p = v := by simpa only [Finset.mem_singleton] using hp
    subst p
    norm_num [v, Erdos957Cases24.Case2.v]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · norm_num [v, Erdos957Cases24.Case2.v]
    · norm_num [w, Erdos957Cases24.Case2.w]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · norm_num [v, Erdos957Cases24.Case2.v]
    · norm_num [a]
    · norm_num [b, Erdos957Cases24.Case2.b]

/-- Complete two-unit local transfer for Case 4.  The primary vertex has
degree at most five.  In the last branch the two common-neighbor targets have
degree at most five. -/
theorem localTransfer (A H : Finset Point)
    (hH : HullAboveSupport H)
    (hrec : recipientSet (unitDegree A v) (unitDegree A w) ⊆ A)
    (hv : unitDegree A v ≤ 5)
    (ha : unitDegree A a ≤ 5)
    (hb : unitDegree A b ≤ 5) :
    Nonempty (LocalTransfer A H Erdos957Cases24.Case2.u 4) := by
  have hvMem : v ∈ recipientSet (unitDegree A v) (unitDegree A w) := by
    simp only [recipientSet]
    split_ifs <;> simp
  have hwMem : unitDegree A v > 4 → unitDegree A w ≤ 5 →
      w ∈ recipientSet (unitDegree A v) (unitDegree A w) := by
    intro hv4 hw5
    simp [recipientSet, not_le_of_gt hv4, hw5]
  have haMem : unitDegree A v > 4 → unitDegree A w > 5 →
      a ∈ recipientSet (unitDegree A v) (unitDegree A w) := by
    intro hv4 hw5
    simp [recipientSet, not_le_of_gt hv4, not_le_of_gt hw5]
  have hbMem : unitDegree A v > 4 → unitDegree A w > 5 →
      b ∈ recipientSet (unitDegree A v) (unitDegree A w) := by
    intro hv4 hw5
    simp [recipientSet, not_le_of_gt hv4, not_le_of_gt hw5]
  have hrow : ∑ p ∈ A, tokens A p = 4 := by
    by_cases hv4 : unitDegree A v ≤ 4
    · simp [tokens, hv4, hrec hvMem]
    · by_cases hw5 : unitDegree A w ≤ 5
      · simp only [tokens, hv4, if_false, hw5, if_true,
          Finset.sum_add_distrib]
        simp [hrec hvMem, hrec (hwMem (lt_of_not_ge hv4) hw5)]
      · simp only [tokens, hv4, if_false, hw5, Finset.sum_add_distrib]
        simp [hrec hvMem,
          hrec (haMem (lt_of_not_ge hv4) (lt_of_not_ge hw5)),
          hrec (hbMem (lt_of_not_ge hv4) (lt_of_not_ge hw5))]
  refine ⟨
    { recipients := recipientSet (unitDegree A v) (unitDegree A w)
      tokens := tokens A
      positive_iff_mem := tokens_positive_iff_mem A
      recipients_subset_configuration := hrec
      row_sum := hrow
      target_not_hull := ?_
      target_capacity := ?_
      target_horizontal_le_three_halves := ?_
      target_in_rectangle := ?_
      target_below_support := ?_
      target_within_two := ?_ }⟩
  · intro p hp
    exact not_mem_hull_of_belowSupport hH (mem_recipientSet_geometry hp).2.1
  · intro p hp
    by_cases hv4 : unitDegree A v ≤ 4
    · have hpv : p = v := by
        simpa [recipientSet, hv4] using hp
      subst p
      simp [tokens, hv4]
      omega
    · by_cases hw5 : unitDegree A w ≤ 5
      · have hpvw : p = v ∨ p = w := by
          simpa [recipientSet, hv4, hw5] using hp
        rcases hpvw with rfl | rfl
        · simp [tokens, hv4, hw5, v_ne_w]
          omega
        · simp [tokens, hv4, hw5, v_ne_w.symm]
          omega
      · have hpvab : p = v ∨ p = a ∨ p = b := by
          simpa [recipientSet, hv4, hw5] using hp
        rcases hpvab with rfl | rfl | rfl
        · simp [tokens, hv4, hw5, v_ne_a, v_ne_b]
          omega
        · simp [tokens, hv4, hw5, v_ne_a.symm, a_ne_b]
          omega
        · simp [tokens, hv4, hw5, v_ne_b.symm, a_ne_b.symm]
          omega
  · intro p hp
    exact recipient_horizontal_le_three_halves hp
  · intro p hp
    exact (mem_recipientSet_geometry hp).1
  · intro p hp
    exact (mem_recipientSet_geometry hp).2.1
  · intro p hp
    exact (mem_recipientSet_geometry hp).2.2

/-- Case 4 constructor with both common-neighbor degree bounds reduced to
their genuine regular-hexagon continuation statements.  `aForces` is paired
with the checked contradiction at the five-valent middle vertex, while
`bForces` is paired with the straight-hull-continuation exclusion. -/
theorem localTransfer_of_completions (A H : Finset Point)
    (hH : HullAboveSupport H)
    (hvA : v ∈ A)
    (hfive : displayedFiveAtV ⊆ A)
    (hvDegree : unitDegree A v = 5)
    (haLeSix : unitDegree A a ≤ 6)
    (haForces : unitDegree A a = 6 → vMissing ∈ A)
    (continuation : Point)
    (hbLeSix : unitDegree A b ≤ 6)
    (bForces : unitDegree A b = 6 → continuation ∈ A)
    (hnoContinuation : continuation ∉ A) :
    Nonempty (LocalTransfer A H Erdos957Cases24.Case2.u 4) := by
  have hwA : w ∈ A := hfive (by simp [displayedFiveAtV])
  have haA : a ∈ A := hfive (by simp [displayedFiveAtV])
  have hbA : b ∈ A := hfive (by simp [displayedFiveAtV])
  have hrec : recipientSet (unitDegree A v) (unitDegree A w) ⊆ A := by
    intro p hp
    simp only [recipientSet] at hp
    split_ifs at hp
    · have hpv : p = v := by simpa only [Finset.mem_singleton] using hp
      exact hpv ▸ hvA
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact hp.elim (fun h ↦ h ▸ hvA) (fun h ↦ h ▸ hwA)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hvA
      · exact haA
      · exact hbA
  have hvLe : unitDegree A v ≤ 5 := by omega
  have haLe : unitDegree A a ≤ 5 :=
    a_degree_le_five_of_completion A hfive hvDegree haLeSix haForces
  have hbLe : unitDegree A b ≤ 5 :=
    b_degree_le_five_of_completion A continuation hbLeSix bForces hnoContinuation
  exact localTransfer A H hH hrec hvLe haLe hbLe

end Case4

/-! ## Honest transport from an arbitrary unit-edge chart

The canonical Case 2/4 lattice is not asserted to coincide with the ordinary
source tangent chart.  In the two-extreme branch one instead chooses the
rigid chart of the consecutive unit hull edge.  The following API transports
the checked canonical row back through any such distance-preserving chart and
therefore exposes the actual recipient vertices. -/

namespace Framed

/-- A Euclidean coordinate chart.  Translation, rotation, and reflection are
all allowed; only bijectivity and preservation of distance are used. -/
structure RigidChart where
  toCanonical : Point ≃ Point
  dist_eq : ∀ p q, dist (toCanonical p) (toCanonical q) = dist p q

namespace RigidChart

variable (F : RigidChart)

/-- The actual point having a prescribed canonical coordinate. -/
def actual (p : Point) : Point := F.toCanonical.symm p

@[simp] lemma toCanonical_actual (p : Point) :
    F.toCanonical (F.actual p) = p := by
  simp [actual]

lemma actual_injective : Function.Injective F.actual :=
  F.toCanonical.symm.injective

lemma dist_actual (p q : Point) :
    dist (F.actual p) (F.actual q) = dist p q := by
  rw [← F.dist_eq, F.toCanonical_actual, F.toCanonical_actual]

/-- Coordinate image of an actual finite configuration. -/
def image (A : Finset Point) : Finset Point :=
  A.image F.toCanonical

lemma mem_image_iff {A : Finset Point} {z : Point} :
    z ∈ F.image A ↔ F.actual z ∈ A := by
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨p, hpA, hpz⟩
    have : F.actual z = p := by
      apply F.toCanonical.injective
      simpa [actual] using hpz.symm
    simpa [this] using hpA
  · intro hz
    exact Finset.mem_image.mpr ⟨F.actual z, hz, by simp [actual]⟩

@[simp] lemma actual_mem_image_iff {A : Finset Point} {p : Point} :
    F.actual p ∈ A ↔ p ∈ F.image A := by
  rw [F.mem_image_iff]

lemma image_oneSeparated {A : Finset Point} (hsep : IsOneSeparated A) :
    IsOneSeparated (F.image A) := by
  intro x hx y hy hxy
  have hxA : F.actual x ∈ A := F.mem_image_iff.mp hx
  have hyA : F.actual y ∈ A := F.mem_image_iff.mp hy
  rw [← F.dist_actual]
  exact hsep (F.actual x) hxA (F.actual y) hyA
    (fun h ↦ hxy (F.actual_injective h))

lemma unitDegree_image (A : Finset Point) (p : Point) :
    unitDegree (F.image A) (F.toCanonical p) = unitDegree A p := by
  have hneighbors : unitNeighbors (F.image A) (F.toCanonical p) =
      (unitNeighbors A p).image F.toCanonical := by
    ext z
    constructor
    · intro hz
      have hz' := mem_unitNeighbors.mp hz
      let q := F.actual z
      have hqA : q ∈ A := F.mem_image_iff.mp hz'.1
      have hpq : dist p q = 1 := by
        rw [← F.dist_eq]
        simpa [q, actual, dist_comm] using hz'.2
      exact Finset.mem_image.mpr ⟨q, mem_unitNeighbors.mpr ⟨hqA, hpq⟩,
        by simp [q, actual]⟩
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
      have hq' := mem_unitNeighbors.mp hq
      exact mem_unitNeighbors.mpr ⟨
        Finset.mem_image.mpr ⟨q, hq'.1, rfl⟩,
        by rw [F.dist_eq]; exact hq'.2⟩
  change (unitNeighbors (F.image A) (F.toCanonical p)).card =
    (unitNeighbors A p).card
  rw [hneighbors,
    Finset.card_image_iff.mpr fun _ _ _ _ h ↦ F.toCanonical.injective h]

lemma unitDegree_image_actual (A : Finset Point) (p : Point) :
    unitDegree (F.image A) p = unitDegree A (F.actual p) := by
  simpa [actual] using F.unitDegree_image A (F.actual p)

lemma withinTwo_actual {source target : Point}
    (h : WithinTwoUnitEdges source target) :
    WithinTwoUnitEdges (F.actual source) (F.actual target) := by
  rcases h with h | ⟨middle, hs, ht⟩
  · left
    rw [UnitAdjacent, F.dist_actual]
    exact h
  · right
    refine ⟨F.actual middle, ?_, ?_⟩
    · rw [UnitAdjacent, F.dist_actual]
      exact hs
    · rw [UnitAdjacent, F.dist_actual]
      exact ht

end RigidChart

/-- An actual local row together with its chosen unit-edge coordinates. -/
structure FramedLocalTransfer (F : RigidChart) (A H : Finset Point)
    (source : Point) (emitted : ℕ) where
  recipients : Finset Point
  tokens : Point → ℕ
  positive_iff_mem : ∀ p, 0 < tokens p ↔ p ∈ recipients
  recipients_subset_configuration : recipients ⊆ A
  row_sum : ∑ p ∈ A, tokens p = emitted
  target_not_hull : ∀ p ∈ recipients, p ∉ H
  target_capacity : ∀ p ∈ recipients,
    2 * unitDegree A p + tokens p ≤ 12
  target_horizontal_le_three_halves : ∀ p ∈ recipients,
    |(F.toCanonical p) 0| ≤ 3 / 2
  target_in_edge_rectangle : ∀ p ∈ recipients,
    InTransferRectangle (F.toCanonical p)
  target_below_edge : ∀ p ∈ recipients,
    BelowSupport (F.toCanonical p)
  target_within_two : ∀ p ∈ recipients,
    WithinTwoUnitEdges source p

/-- Transport a checked canonical row back to its actual unit-edge frame.
No alignment with the tangent chart and no global half-plane condition on
the hull are used. -/
noncomputable def transportLocalTransfer (F : RigidChart) (A H : Finset Point)
    (source : Point) (emitted : ℕ)
    (T : LocalTransfer (F.image A) (F.image H) source emitted) :
    FramedLocalTransfer F A H (F.actual source) emitted := by
  let R : Finset Point := T.recipients.image F.actual
  let tok : Point → ℕ := fun p ↦ T.tokens (F.toCanonical p)
  have hrow : ∑ p ∈ A, tok p = emitted := by
    rw [← T.row_sum]
    simp only [RigidChart.image, tok]
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact F.toCanonical.injective hpq
  refine
    { recipients := R
      tokens := tok
      positive_iff_mem := ?_
      recipients_subset_configuration := ?_
      row_sum := hrow
      target_not_hull := ?_
      target_capacity := ?_
      target_horizontal_le_three_halves := ?_
      target_in_edge_rectangle := ?_
      target_below_edge := ?_
      target_within_two := ?_ }
  · intro p
    rw [T.positive_iff_mem]
    constructor
    · intro hp
      exact Finset.mem_image.mpr ⟨F.toCanonical p, hp, by simp [RigidChart.actual]⟩
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, hqp⟩
      have heq : F.toCanonical p = q := by
        rw [← hqp]
        simp [RigidChart.actual]
      simpa [heq] using hq
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hqImage := T.recipients_subset_configuration hq
    exact F.mem_image_iff.mp hqImage
  · intro p hp hpH
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    apply T.target_not_hull q hq
    exact Finset.mem_image.mpr ⟨F.actual q, hpH, by simp [RigidChart.actual]⟩
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hcap := T.target_capacity q hq
    simpa [tok, F.unitDegree_image_actual] using hcap
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    simpa [RigidChart.actual] using T.target_horizontal_le_three_halves q hq
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    simpa [RigidChart.actual] using T.target_in_rectangle q hq
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    simpa [RigidChart.actual] using T.target_below_support q hq
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    exact F.withinTwo_actual (T.target_within_two q hq)

/-! ### Actual Case 2/4 role sets -/

open Erdos957Cases24

/-- The actual Case 2 recipients in an arbitrary unit-edge chart. -/
def actualCase2RecipientSet (F : RigidChart) (A : Finset Point) : Finset Point :=
  (Case2.recipientSet
    (unitDegree A (F.actual Case2.w))
    (unitDegree A (F.actual Case2.wNext))).image F.actual

/-- The actual recipients of one source-indexed Case 4 row. -/
def actualCase4RecipientSet (F : RigidChart) (A : Finset Point)
    (right : Bool) : Finset Point :=
  (Erdos957Case24Bridge.Case4.sideRecipientSet (F.image A) right).image F.actual

/-- Case 2 in an arbitrary unit-edge chart.  The support and displayed-point
hypotheses are stated in that chart, while hull exclusion is stated directly
for the actual role points. -/
theorem case2LocalTransfer_of_edge_frame (F : RigidChart) (A H : Finset Point)
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside (F.image A) {Case2.uPrev, Case2.u})
    (hbA : F.actual Case2.b ∈ A)
    (hdisplay : ∀ q ∈ Case2.displayedFiveAtB, F.actual q ∈ A)
    (hnotHull : ∀ p ∈ actualCase2RecipientSet F A, p ∉ H) :
    Nonempty (FramedLocalTransfer F A H (F.actual Case2.u) 2) := by
  let B := F.image A
  let K := F.image H
  have hbB : Case2.b ∈ B := by
    exact F.mem_image_iff.mpr hbA
  have hdisplayB : Case2.displayedFiveAtB ⊆ B := by
    intro q hq
    exact F.mem_image_iff.mpr (hdisplay q hq)
  have hnotK : ∀ p ∈ Case2.recipientSet
      (unitDegree B Case2.w) (unitDegree B Case2.wNext), p ∉ K := by
    intro p hp hpK
    apply hnotHull (F.actual p)
    · simp only [actualCase2RecipientSet, Finset.mem_image]
      refine ⟨p, ?_, rfl⟩
      simpa [B, F.unitDegree_image_actual] using hp
    · exact F.mem_image_iff.mp hpK
  rcases Erdos957Case24Bridge.Case2.localTransfer_of_strict_support_and_target_exclusion
      B K hnotK
        (F.image_oneSeparated hsep) hstrict hbB hdisplayB with ⟨T⟩
  exact ⟨transportLocalTransfer F A H Case2.u 2 T⟩

/-- Source-indexed Case 4 in an arbitrary unit-edge chart. -/
theorem case4LocalTransfer_of_edge_frame (F : RigidChart) (A H : Finset Point)
    (right : Bool)
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside (F.image A) {Case2.uPrev, Case2.u})
    (hvA : F.actual Erdos957Cases24.Case4.v ∈ A)
    (hfive : ∀ q ∈ Erdos957Cases24.Case4.displayedFiveAtV,
      F.actual q ∈ A)
    (hvDegree : unitDegree A (F.actual Erdos957Cases24.Case4.v) = 5)
    (hnotHull : ∀ p ∈ actualCase4RecipientSet F A right, p ∉ H) :
    Nonempty (FramedLocalTransfer F A H
      (F.actual (Erdos957Case24Bridge.Case4.sideSource right)) 2) := by
  let B := F.image A
  let K := F.image H
  have hvB : Erdos957Cases24.Case4.v ∈ B := F.mem_image_iff.mpr hvA
  have hfiveB : Erdos957Cases24.Case4.displayedFiveAtV ⊆ B := by
    intro q hq
    exact F.mem_image_iff.mpr (hfive q hq)
  have hvDegreeB : unitDegree B Erdos957Cases24.Case4.v = 5 := by
    simpa [B, F.unitDegree_image_actual] using hvDegree
  have hnotK : ∀ p ∈ Erdos957Case24Bridge.Case4.sideRecipientSet B right,
      p ∉ K := by
    intro p hp hpK
    apply hnotHull (F.actual p)
    · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · exact F.mem_image_iff.mp hpK
  rcases Erdos957Case24Bridge.Case4.sourceLocalTransfer_of_strict_support_and_target_exclusion
        B K right hnotK (F.image_oneSeparated hsep) hstrict hvB hfiveB hvDegreeB with ⟨T⟩
  exact ⟨transportLocalTransfer F A H
    (Erdos957Case24Bridge.Case4.sideSource right) 2 T⟩

end Framed

end Erdos957Case24Bridge
