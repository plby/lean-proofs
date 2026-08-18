/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Higher properness and Freiman coordinates for GAPs

This file formalizes Definition 2.2 and the elementary implication in Lemma
2.3 of Conlon--Fox--Pham in the finite `GAP` interface used for Erdős problem
186.

For a tuple of displayed points, `GAP.totalCoeffs` is the vector obtained by
adding their (one-sided) GAP coordinates.  A GAP is `s`-proper if, for every
number `t ≤ s` of summands, equality of the two sums of displayed points
forces equality of their total coefficient vectors.  Including all `t ≤ s`
is the convenient bounded-order version of the usual definition; it is
exactly what is needed for Freiman maps of order at most `s`.

The main result, `GAP.sProper_of_dilate_proper`, says that properness of the
displayed `s`-dilate implies `s`-properness.  Notice that a sum of only
`t ≤ s` coordinates still belongs to the coefficient box of the `s`-dilate.
The different offsets (`t * offset` versus `s * offset`) cause no problem:
they are the same on the two sides of an equality and cancel.

For positive `s`, an `s`-proper GAP is proper.  We consequently obtain its
identification map into the integral coefficient lattice and prove the full
Freiman sum equivalence up to order `s`.
-/

namespace Erdos186

open scoped BigOperators

namespace GAP

variable {d r s t : ℕ}

/-! ## Total coordinates and point sums -/

/-- The coordinatewise sum of a tuple of GAP coordinates. -/
def totalCoeffs (P : GAP d r) {t : ℕ} (a : Fin t → P.Coord) :
    Fin r → ℕ :=
  fun i ↦ ∑ k, (a k i : ℕ)

/-- The sum of the displayed points represented by a tuple of coordinates. -/
def tuplePointSum (P : GAP d r) {t : ℕ} (a : Fin t → P.Coord) :
    LatticePoint d :=
  ∑ k, P.coordPoint (a k)

@[simp]
theorem totalCoeffs_zero (P : GAP d r) (a : Fin 0 → P.Coord) :
    P.totalCoeffs a = 0 := by
  funext i
  simp [totalCoeffs]

@[simp]
theorem tuplePointSum_zero (P : GAP d r) (a : Fin 0 → P.Coord) :
    P.tuplePointSum a = 0 := by
  simp [tuplePointSum]

/-- Expanding a tuple sum separates the repeated offset from its total
coefficient vector. -/
theorem tuplePointSum_eq (P : GAP d r) (a : Fin t → P.Coord) :
    P.tuplePointSum a = fun j ↦
      (t : ℤ) * P.offset j +
        ∑ i, (P.totalCoeffs a i : ℤ) * P.steps i j := by
  funext j
  simp only [tuplePointSum, Finset.sum_apply, coordPoint, totalCoeffs]
  push_cast
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

/-- Equal total coefficient vectors always give equal sums of displayed
points.  This direction needs no properness. -/
theorem tuplePointSum_eq_of_totalCoeffs_eq (P : GAP d r)
    {a b : Fin t → P.Coord} (h : P.totalCoeffs a = P.totalCoeffs b) :
    P.tuplePointSum a = P.tuplePointSum b := by
  rw [P.tuplePointSum_eq a, P.tuplePointSum_eq b, h]

/-- A tuple of at most `s` original coordinates gives a valid coordinate in
the displayed `s`-dilate by taking coordinatewise sums. -/
def totalCoordInDilate (P : GAP d r) {s t : ℕ} (ht : t ≤ s)
    (a : Fin t → P.Coord) : (P.dilate s).Coord :=
  fun i ↦ ⟨P.totalCoeffs a i, by
    have hterm (k : Fin t) : (a k i : ℕ) ≤ P.widths i - 1 := by
      have hk := (a k i).isLt
      omega
    calc
      P.totalCoeffs a i ≤ ∑ _k : Fin t, (P.widths i - 1) := by
        exact Finset.sum_le_sum fun k _ ↦ hterm k
      _ = t * (P.widths i - 1) := by simp
      _ ≤ s * (P.widths i - 1) := Nat.mul_le_mul_right _ ht
      _ < s * (P.widths i - 1) + 1 := Nat.lt_succ_self _⟩

@[simp]
theorem totalCoordInDilate_apply (P : GAP d r) {s t : ℕ} (ht : t ≤ s)
    (a : Fin t → P.Coord) (i : Fin r) :
    ((P.totalCoordInDilate ht a i : Fin ((P.dilate s).widths i)) : ℕ) =
      P.totalCoeffs a i :=
  rfl

/-- Equality of two `t`-term point sums gives equality of the corresponding
points in the `s`-dilate whenever `t ≤ s`. -/
theorem coordPoint_totalCoordInDilate_eq_of_tuplePointSum_eq
    (P : GAP d r) {s t : ℕ} (ht : t ≤ s) {a b : Fin t → P.Coord}
    (h : P.tuplePointSum a = P.tuplePointSum b) :
    (P.dilate s).coordPoint (P.totalCoordInDilate ht a) =
      (P.dilate s).coordPoint (P.totalCoordInDilate ht b) := by
  have hlinear :
      (fun j ↦ ∑ i, (P.totalCoeffs a i : ℤ) * P.steps i j) =
        fun j ↦ ∑ i, (P.totalCoeffs b i : ℤ) * P.steps i j := by
    rw [P.tuplePointSum_eq a, P.tuplePointSum_eq b] at h
    funext j
    have hj := congrFun h j
    exact add_left_cancel hj
  funext j
  simp only [coordPoint, dilate_offset, dilate_steps,
    totalCoordInDilate_apply]
  exact congrFun hlinear j |> congrArg ((s : ℤ) * P.offset j + ·)

/-! ## Higher properness -/

/-- CFP Definition 2.2 in its literal, exact-order form: equality of two sums
of exactly `s` displayed points determines their total coefficient vectors.
The converse implication in the paper's displayed equivalence is automatic
from `tuplePointSum_eq_of_totalCoeffs_eq`. -/
def ExactSProper (P : GAP d r) (s : ℕ) : Prop :=
  ∀ a b : Fin s → P.Coord,
    P.tuplePointSum a = P.tuplePointSum b →
      P.totalCoeffs a = P.totalCoeffs b

/-- A GAP is `s`-proper if equality of two sums of at most `s` displayed
points determines their total GAP coefficient vector.  This bounded-order
form is equivalent to the literal `ExactSProper` formulation in CFP
Definition 2.2; see `sProper_iff_exact`. -/
def SProper (P : GAP d r) (s : ℕ) : Prop :=
  ∀ {t : ℕ}, t ≤ s → ∀ a b : Fin t → P.Coord,
    P.tuplePointSum a = P.tuplePointSum b →
      P.totalCoeffs a = P.totalCoeffs b

/-- The bounded-order formulation of `s`-properness is equivalent to CFP's
literal exact-order formulation.  For the nontrivial direction, pad each
shorter tuple by the same copies of `zeroCoord`. -/
theorem sProper_iff_exact (P : GAP d r) (s : ℕ) :
    P.SProper s ↔ P.ExactSProper s := by
  constructor
  · intro hP
    exact hP le_rfl
  · intro hP t ht a b hab
    have hts : t + (s - t) = s := Nat.add_sub_of_le ht
    have hP' : P.ExactSProper (t + (s - t)) := by
      simpa only [hts] using hP
    let az : Fin (s - t) → P.Coord := fun _ ↦ P.zeroCoord
    let aa : Fin (t + (s - t)) → P.Coord := Fin.append a az
    let bb : Fin (t + (s - t)) → P.Coord := Fin.append b az
    have hab' : P.tuplePointSum aa = P.tuplePointSum bb := by
      simpa [tuplePointSum, aa, bb, az, Fin.sum_univ_add] using
        congrArg (· + ∑ _ : Fin (s - t), P.coordPoint P.zeroCoord) hab
    have hcoeff := hP' aa bb hab'
    funext i
    have hi := congrFun hcoeff i
    simpa [totalCoeffs, aa, bb, az, Fin.sum_univ_add] using hi

/-- Properness of the `s`-dilate implies `s`-properness of the original GAP
(the implication used in CFP Lemma 2.3). -/
theorem sProper_of_dilate_proper (P : GAP d r) (s : ℕ)
    (hP : (P.dilate s).Proper) : P.SProper s := by
  intro t ht a b hab
  have hcoord : P.totalCoordInDilate ht a = P.totalCoordInDilate ht b :=
    hP (P.coordPoint_totalCoordInDilate_eq_of_tuplePointSum_eq ht hab)
  funext i
  exact congrArg (fun n : (P.dilate s).Coord ↦ (n i : ℕ)) hcoord

/-- Higher properness is monotone in the order. -/
theorem SProper.mono {P : GAP d r} {s t : ℕ} (hP : P.SProper s)
    (ht : t ≤ s) : P.SProper t := by
  intro u hu
  exact hP (hu.trans ht)

/-- For tuples of an allowed length, `s`-properness gives the two-way
additive-relation criterion used throughout the CFP argument. -/
theorem SProper.tuplePointSum_eq_iff_totalCoeffs_eq {P : GAP d r} {s t : ℕ}
    (hP : P.SProper s) (ht : t ≤ s) (a b : Fin t → P.Coord) :
    P.tuplePointSum a = P.tuplePointSum b ↔
      P.totalCoeffs a = P.totalCoeffs b := by
  exact ⟨hP ht a b, P.tuplePointSum_eq_of_totalCoeffs_eq⟩

/-- `s`-properness at a positive order implies ordinary properness. -/
theorem SProper.proper {P : GAP d r} {s : ℕ} (hP : P.SProper s)
    (hs : 1 ≤ s) : P.Proper := by
  intro a b hab
  let aa : Fin 1 → P.Coord := fun _ ↦ a
  let bb : Fin 1 → P.Coord := fun _ ↦ b
  have hsum : P.tuplePointSum aa = P.tuplePointSum bb := by
    simpa [tuplePointSum, aa, bb] using hab
  have hcoeff := hP hs aa bb hsum
  funext i
  apply Fin.ext
  have hi := congrFun hcoeff i
  simpa [totalCoeffs, aa, bb] using hi

/-- Ordinary properness is the order-one case of higher properness. -/
theorem sProper_one_iff_proper (P : GAP d r) : P.SProper 1 ↔ P.Proper := by
  constructor
  · intro hP
    exact hP.proper le_rfl
  · intro hP
    exact P.sProper_of_dilate_proper 1 (by
      simpa only [show P.dilate 1 = P by
        rw [GAP.mk.injEq]
        refine ⟨?_, rfl, ?_⟩
        · funext j
          simp
        · funext i
          have hi := P.width_pos i
          simp only [dilate_widths, one_mul]
          omega] using hP)

/-! ## Identification with the coefficient lattice -/

/-- The coefficient-lattice identification attached to a positive-order
`s`-proper GAP.  It sends an actual carrier point to its unique integral
coordinate vector. -/
noncomputable def identificationMap (P : GAP d r) {s : ℕ}
    (hP : P.SProper s) (hs : 1 ≤ s) :
    {x // x ∈ P.carrier} → (Fin r → ℤ) :=
  fun x i ↦ (P.coordinateMap (hP.proper hs) x i : ℕ)

@[simp]
theorem identificationMap_coordPoint (P : GAP d r) {s : ℕ}
    (hP : P.SProper s) (hs : 1 ≤ s) (a : P.Coord) :
    P.identificationMap hP hs
        ⟨P.coordPoint a, P.coordPoint_mem_carrier a⟩ =
      fun i ↦ ((a i : ℕ) : ℤ) := by
  funext i
  simp [identificationMap]

/-- Distinct carrier points have distinct coefficient-lattice
identifications. -/
theorem identificationMap_injective (P : GAP d r) {s : ℕ}
    (hP : P.SProper s) (hs : 1 ≤ s) :
    Function.Injective (P.identificationMap hP hs) := by
  intro x y hxy
  have hc : P.coordinateMap (hP.proper hs) x =
      P.coordinateMap (hP.proper hs) y := by
    funext i
    apply Fin.ext
    exact Int.ofNat_inj.mp (congrFun hxy i)
  apply Subtype.ext
  rw [← P.coordPoint_coordinateMap (hP.proper hs) x,
    ← P.coordPoint_coordinateMap (hP.proper hs) y, hc]

/-- The identification map preserves and reflects every additive relation
with at most `s` terms on each side.  In other words, it is a Freiman
isomorphism of order `s` onto its image. -/
theorem sum_identificationMap_eq_iff {P : GAP d r} {s t : ℕ}
    (hP : P.SProper s) (hs : 1 ≤ s) (ht : t ≤ s)
    (a b : Fin t → {x // x ∈ P.carrier}) :
    (∑ k, P.identificationMap hP hs (a k)) =
        ∑ k, P.identificationMap hP hs (b k) ↔
      (∑ k, (a k : LatticePoint d)) = ∑ k, (b k : LatticePoint d) := by
  let ha : P.Proper := hP.proper hs
  let ca : Fin t → P.Coord := fun k ↦ P.coordinateMap ha (a k)
  let cb : Fin t → P.Coord := fun k ↦ P.coordinateMap ha (b k)
  have hpoint_a (k : Fin t) : P.coordPoint (ca k) = a k := by
    exact P.coordPoint_coordinateMap ha (a k)
  have hpoint_b (k : Fin t) : P.coordPoint (cb k) = b k := by
    exact P.coordPoint_coordinateMap ha (b k)
  have hid_a (k : Fin t) :
      P.identificationMap hP hs (a k) =
        fun i ↦ (((ca k i : Fin (P.widths i)) : ℕ) : ℤ) := by
    funext i
    rfl
  have hid_b (k : Fin t) :
      P.identificationMap hP hs (b k) =
        fun i ↦ (((cb k i : Fin (P.widths i)) : ℕ) : ℤ) := by
    funext i
    rfl
  constructor
  · intro hcoeff
    have htotal : P.totalCoeffs ca = P.totalCoeffs cb := by
      funext i
      have hi := congrFun hcoeff i
      simp_rw [Finset.sum_apply, hid_a, hid_b] at hi
      exact_mod_cast hi
    have := P.tuplePointSum_eq_of_totalCoeffs_eq htotal
    simpa only [tuplePointSum, hpoint_a, hpoint_b] using this
  · intro hpoints
    have htuple : P.tuplePointSum ca = P.tuplePointSum cb := by
      simpa only [tuplePointSum, hpoint_a, hpoint_b] using hpoints
    have htotal := hP ht ca cb htuple
    funext i
    have hi := congrFun htotal i
    simp_rw [Finset.sum_apply, hid_a, hid_b]
    exact_mod_cast hi

end GAP
end Erdos186
