/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.UpperPackaging
import ErdosProblems.Erdos186.Numerical
import ErdosProblems.Erdos186.GAP

/-!
# Common finite language for the Pham--Zakharov argument

This file supplies the elementary bridges shared by the post-CFP part of
the proof of Erdős problem 186.  In particular it proves, in every lattice
dimension, the subset-sum obstruction furnished by a nonaveraging set.
-/

namespace Erdos186.PZ

open scoped BigOperators

noncomputable section

/-- In positive dimensions, the exponent used by the public box statement
is the exponent used by the numerical iteration. -/
theorem boxExponent_eq_pzExponent {d : ℕ} (hd : 0 < d) :
    boxExponent d = pzExponent d := by
  by_cases hd1 : d = 1
  · subst d
    simp
  · have hd2 : 2 ≤ d := by omega
    rw [pzExponent_eq_fraction hd2]
    simp only [boxExponent, hd1, ↓reduceIte]
    norm_cast
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    rfl

/-- Vector nonaveraging is inherited by subsets. -/
theorem isBoxNonaveraging_mono {d : ℕ} {A C : Finset (BoxPoint d)}
    (hA : IsBoxNonaveraging A) (hCA : C ⊆ A) : IsBoxNonaveraging C := by
  intro a ha S hS hcard
  apply hA a (hCA ha) S
  · intro x hx
    have hx' := Finset.mem_erase.mp (hS hx)
    exact Finset.mem_erase.mpr ⟨hx'.1, hCA hx'.2⟩
  · exact hcard

/-- Translation of a finite lattice set. -/
def translate {d : ℕ} (v : BoxPoint d) (A : Finset (BoxPoint d)) :
    Finset (BoxPoint d) :=
  A.image fun x ↦ x + v

@[simp]
theorem card_translate {d : ℕ} (v : BoxPoint d) (A : Finset (BoxPoint d)) :
    (translate v A).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (add_left_injective v)

/-- Translation preserves the literal vector nonaveraging property. -/
theorem isBoxNonaveraging_translate {d : ℕ} {A : Finset (BoxPoint d)}
    (v : BoxPoint d) (hA : IsBoxNonaveraging A) :
    IsBoxNonaveraging (translate v A) := by
  classical
  intro b hb T hT hcard
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  let e : BoxPoint d ↪ BoxPoint d :=
    ⟨fun x ↦ x + v, add_left_injective v⟩
  let S : Finset (BoxPoint d) := T.preimage e e.injective.injOn
  have hTsub : T ⊆ translate v A := hT.trans (Finset.erase_subset _ _)
  have hmap : S.map e = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_preimage.mp hy
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp (hTsub hx)
      refine Finset.mem_map.mpr ⟨y, Finset.mem_preimage.mpr ?_, hxy⟩
      change e y ∈ T
      rw [show e y = x by simpa [e] using hxy]
      exact hx
  have hSsub : S ⊆ A.erase a := by
    intro x hx
    have hxT : e x ∈ T := by
      rw [← hmap]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hxe := Finset.mem_erase.mp (hT hxT)
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro hxa
      apply hxe.1
      simpa [e, hxa]
    · simpa [translate, e] using hxe.2
  have hcardS : S.card = T.card := by rw [← hmap]; simp
  intro heq
  apply hA a ha S hSsub (by simpa [hcardS] using hcard)
  have hsum_map : ∑ x ∈ T, x = ∑ x ∈ S, e x := by
    rw [← hmap]
    simp [Finset.sum_map]
  rw [hsum_map] at heq
  have hcardInt : (T.card : ℤ) = S.card := by simp [hcardS]
  rw [hcardInt] at heq
  simpa [e, Finset.sum_add_distrib, smul_add] using heq

/-- A nonzero common deviation sum gives a forbidden average.  This is the
dimension-free version of the easy implication in the Erdős--Straus
subset-sum criterion. -/
theorem averaging_witness_of_common_deviation_sum {d : ℕ}
    {A A₁ A₂ : Finset (BoxPoint d)} {a z : BoxPoint d}
    (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisj : Disjoint A₁ A₂)
    (hz : z ≠ 0)
    (hz₁ : ∑ x ∈ A₁, (x - a) = z)
    (hz₂ : ∑ x ∈ A₂, (a - x) = z) :
    ¬ IsBoxNonaveraging A := by
  intro hA
  have hA₁ne : A₁.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    subst A₁
    simp at hz₁
    exact hz hz₁.symm
  have hA₂ne : A₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    subst A₂
    simp at hz₂
    exact hz hz₂.symm
  let S := A₁ ∪ A₂
  have hSsub : S ⊆ A.erase a := by
    exact Finset.union_subset hA₁ hA₂
  have hScard : 2 ≤ S.card := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint hdisj]
    have h₁ : 0 < A₁.card := Finset.card_pos.mpr hA₁ne
    have h₂ : 0 < A₂.card := Finset.card_pos.mpr hA₂ne
    omega
  apply hA a ha S hSsub hScard
  funext i
  have hcoord₁ :
      (∑ x ∈ A₁, x i) - (A₁.card : ℤ) * a i = z i := by
    have h := congrFun hz₁ i
    simpa [Finset.sum_sub_distrib] using h
  have hcoord₂ :
      (A₂.card : ℤ) * a i - ∑ x ∈ A₂, x i = z i := by
    have h := congrFun hz₂ i
    simpa [Finset.sum_sub_distrib] using h
  dsimp [S]
  rw [Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj]
  simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
  change ((A₁.card + A₂.card : ℕ) : ℤ) * a i =
    (∑ x ∈ A₁, x i) + ∑ x ∈ A₂, x i
  push_cast
  linear_combination -hcoord₁ + hcoord₂

/-- Contrapositive form used after the Pham--Zakharov intersection theorem. -/
theorem no_common_deviation_sum_of_nonaveraging {d : ℕ}
    {A A₁ A₂ : Finset (BoxPoint d)} {a z : BoxPoint d}
    (hA : IsBoxNonaveraging A)
    (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisj : Disjoint A₁ A₂)
    (hz₁ : ∑ x ∈ A₁, (x - a) = z)
    (hz₂ : ∑ x ∈ A₂, (a - x) = z) :
    z = 0 := by
  by_contra hz
  exact averaging_witness_of_common_deviation_sum ha hA₁ hA₂ hdisj hz hz₁ hz₂ hA

/-! ## The canonical coefficient box of a proper GAP -/

/-- The coordinate tuple of a GAP, regarded as an integer lattice point. -/
def gapCoordLattice {d r : ℕ} (P : GAP d r) (n : P.Coord) : BoxPoint r :=
  fun i ↦ (n i : ℤ)

/-- The axis-aligned integer box of displayed GAP coefficients. -/
def gapCoefficientBox {d r : ℕ} (P : GAP d r) : IntegerBox r where
  lower := 0
  upper i := (P.widths i : ℤ) - 1

@[simp]
theorem gapCoordLattice_mem_coefficientBox {d r : ℕ} (P : GAP d r)
    (n : P.Coord) :
    gapCoordLattice P n ∈ (gapCoefficientBox P).carrier := by
  rw [IntegerBox.mem_carrier_iff]
  intro i
  constructor
  · exact Int.natCast_nonneg _
  · change (n i : ℤ) ≤ (P.widths i : ℤ) - 1
    have hn := (n i).isLt
    omega

/-- Distinct GAP coordinate tuples give distinct integer lattice points. -/
theorem gapCoordLattice_injective {d r : ℕ} (P : GAP d r) :
    Function.Injective (gapCoordLattice P) := by
  intro n m hnm
  funext i
  apply Fin.val_injective
  exact Int.ofNat_inj.mp (congrFun hnm i)

/-- The coefficient box has cardinality equal to the displayed GAP volume. -/
@[simp]
theorem gapCoefficientBox_card {d r : ℕ} (P : GAP d r) :
    (gapCoefficientBox P).carrier.card = P.volume := by
  classical
  simp [gapCoefficientBox, IntegerBox.carrier, GAP.volume,
    show ∀ i, 1 ≤ P.widths i by exact fun i ↦ P.width_pos i]

/-- The integer coefficient of a point in a proper GAP. -/
noncomputable def gapIdentify {d r : ℕ} (P : GAP d r) (hP : P.Proper)
    (x : {x // x ∈ P.carrier}) : BoxPoint r :=
  gapCoordLattice P (P.coordinateMap hP x)

@[simp]
theorem gapIdentify_mem_coefficientBox {d r : ℕ} (P : GAP d r)
    (hP : P.Proper) (x : {x // x ∈ P.carrier}) :
    gapIdentify P hP x ∈ (gapCoefficientBox P).carrier :=
  gapCoordLattice_mem_coefficientBox P _

/-- Properness makes the identification map injective. -/
theorem gapIdentify_injective {d r : ℕ} (P : GAP d r) (hP : P.Proper) :
    Function.Injective (gapIdentify P hP) := by
  intro x y hxy
  have hcoord : P.coordinateMap hP x = P.coordinateMap hP y :=
    gapCoordLattice_injective P hxy
  apply Subtype.ext
  rw [← P.coordPoint_coordinateMap hP x,
    ← P.coordPoint_coordinateMap hP y, hcoord]

/-- Equality of averages in coefficient space implies equality of averages
after evaluating the GAP.  The offset cancels because both sides contain
the same number of summands. -/
theorem gap_average_reflect {d r : ℕ} (P : GAP d r) (n : P.Coord)
    (S : Finset P.Coord)
    (havg : (S.card : ℤ) • gapCoordLattice P n =
      ∑ m ∈ S, gapCoordLattice P m) :
    (S.card : ℤ) • P.coordPoint n = ∑ m ∈ S, P.coordPoint m := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  have hi : ∀ i, (S.card : ℤ) * (n i : ℤ) =
      ∑ m ∈ S, (m i : ℤ) := by
    intro i
    simpa [gapCoordLattice] using congrFun havg i
  simp only [GAP.coordPoint, Finset.sum_apply, mul_add,
    Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply add_left_cancel (a := -((S.card : ℤ) * P.offset j))
  simp only [neg_add_cancel_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi_mem
  rw [← Finset.sum_mul, ← hi i]
  ring

end

end Erdos186.PZ
