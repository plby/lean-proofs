/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Basic

/-!
# Coordinates for the Pham--Zakharov reduction

This file records the exact coordinate-identification facts used in
Definition 9 of Pham--Zakharov.  A positive proper dilation of a GAP already
forces the original GAP to be proper.  Hence a set in the GAP may be moved to
its coefficient lattice without changing either its cardinality or the
nonaveraging property.
-/

namespace Erdos186.PZ.Reduction

open scoped BigOperators

noncomputable section

variable {d r k : ℕ}

namespace GAP

/-- An admissible coordinate of `P` is still admissible in every positive
dilation of `P`. -/
private def coordinateToDilate (P : Erdos186.GAP d r) (k : ℕ) (hk : 0 < k) :
    P.Coord → (P.dilate k).Coord := fun n i ↦
  ⟨n i, by
    have hw : P.widths i = 1 * (P.widths i - 1) + 1 := by
      have := P.width_pos i
      omega
    have hmul : 1 * (P.widths i - 1) ≤ k * (P.widths i - 1) :=
      Nat.mul_le_mul_right _ hk
    have hle : P.widths i ≤ k * (P.widths i - 1) + 1 := by
      calc
        P.widths i = 1 * (P.widths i - 1) + 1 := hw
        _ ≤ k * (P.widths i - 1) + 1 := Nat.add_le_add_right hmul 1
    exact (n i).isLt.trans_le hle⟩

/-- Properness at a positive dilation scale implies properness of the
undilated GAP. -/
theorem proper_of_dilate_proper (P : Erdos186.GAP d r) (hk : 0 < k)
    (hproper : (P.dilate k).Proper) : P.Proper := by
  intro n m hnm
  have hlift : coordinateToDilate P k hk n = coordinateToDilate P k hk m := by
    apply hproper
    funext j
    have hj := congrFun hnm j
    simp only [Erdos186.GAP.coordPoint, Erdos186.GAP.dilate,
      coordinateToDilate]
    have hsum :
        ∑ i, (n i : ℤ) * P.steps i j = ∑ i, (m i : ℤ) * P.steps i j := by
      simpa only [Erdos186.GAP.coordPoint] using add_left_cancel hj
    rw [hsum]
  funext i
  apply Fin.val_injective
  simpa only [coordinateToDilate] using
    congrArg Fin.val (congrFun hlift i)

/-! ## The coefficient box as a GAP -/

/-- The canonical rank-`r` GAP in `ℤ^r` whose carrier is the coefficient box
of `P`.  Its steps are the standard coordinate vectors. -/
def coefficientGAP (P : Erdos186.GAP d r) : Erdos186.GAP r r where
  offset := 0
  steps i j := if i = j then 1 else 0
  widths := P.widths
  width_pos := P.width_pos

@[simp] theorem coefficientGAP_volume (P : Erdos186.GAP d r) :
    (coefficientGAP P).volume = P.volume := rfl

/-- Evaluating the coefficient GAP is just coercion of bounded coordinates
to the integer coefficient lattice. -/
@[simp] theorem coefficientGAP_coordPoint (P : Erdos186.GAP d r)
    (n : (coefficientGAP P).Coord) :
    (coefficientGAP P).coordPoint n = gapCoordLattice P n := by
  funext j
  simp [coefficientGAP, Erdos186.GAP.coordPoint, gapCoordLattice]

/-- The standard-coordinate presentation is proper. -/
theorem coefficientGAP_proper (P : Erdos186.GAP d r) :
    (coefficientGAP P).Proper := by
  intro n m hnm
  exact gapCoordLattice_injective P (by simpa using hnm)

/-- Every point displayed by the coefficient GAP belongs to the canonical
integer coefficient box. -/
theorem coefficientGAP_carrier_subset_coefficientBox
    (P : Erdos186.GAP d r) :
    (coefficientGAP P).carrier ⊆ (gapCoefficientBox P).carrier := by
  intro x hx
  obtain ⟨n, rfl⟩ := Erdos186.GAP.mem_carrier_iff.mp hx
  rw [coefficientGAP_coordPoint]
  exact gapCoordLattice_mem_coefficientBox P n

/-- The canonical coefficient GAP and coefficient box have exactly the same
lattice points. -/
@[simp] theorem coefficientGAP_carrier (P : Erdos186.GAP d r) :
    (coefficientGAP P).carrier = (gapCoefficientBox P).carrier := by
  apply Finset.eq_of_subset_of_card_le
    (coefficientGAP_carrier_subset_coefficientBox P)
  rw [gapCoefficientBox_card,
    Erdos186.GAP.card_carrier_eq_volume _ (coefficientGAP_proper P),
    coefficientGAP_volume]

/-! ## The difference of two coefficient boxes -/

/-- A standard-coordinate GAP containing every difference of two points of
the coefficient box of `P`. -/
def differenceCoefficientGAP (P : Erdos186.GAP d r) : Erdos186.GAP r r where
  offset j := -((P.widths j : ℤ) - 1)
  steps i j := if i = j then 1 else 0
  widths i := 2 * (P.widths i - 1) + 1
  width_pos := fun _ ↦ Nat.zero_lt_succ _

@[simp] theorem differenceCoefficientGAP_coordPoint
    (P : Erdos186.GAP d r) (n : (differenceCoefficientGAP P).Coord) :
    (differenceCoefficientGAP P).coordPoint n =
      fun j ↦ -((P.widths j : ℤ) - 1) + (n j : ℤ) := by
  funext j
  simp [differenceCoefficientGAP, Erdos186.GAP.coordPoint]

/-- The difference GAP contains zero. -/
theorem zero_mem_differenceCoefficientGAP (P : Erdos186.GAP d r) :
    0 ∈ (differenceCoefficientGAP P).carrier := by
  let n : (differenceCoefficientGAP P).Coord := fun i ↦
    ⟨P.widths i - 1, by
      have hi := P.width_pos i
      change P.widths i - 1 < 2 * (P.widths i - 1) + 1
      omega⟩
  refine Erdos186.GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
  funext j
  rw [differenceCoefficientGAP_coordPoint]
  dsimp [n]
  have hj := P.width_pos j
  rw [Nat.cast_sub (by omega : 1 ≤ P.widths j)]
  omega

/-- The difference of any two coefficient-box points is displayed by the
difference GAP. -/
theorem sub_mem_differenceCoefficientGAP_of_mem
    (P : Erdos186.GAP d r) {z x : BoxPoint r}
    (hz : z ∈ (gapCoefficientBox P).carrier)
    (hx : x ∈ (gapCoefficientBox P).carrier) :
    z - x ∈ (differenceCoefficientGAP P).carrier := by
  rw [← coefficientGAP_carrier] at hz hx
  obtain ⟨nz, hnz⟩ := Erdos186.GAP.mem_carrier_iff.mp hz
  obtain ⟨nx, hnx⟩ := Erdos186.GAP.mem_carrier_iff.mp hx
  have hnz' : gapCoordLattice P nz = z := by
    rw [← coefficientGAP_coordPoint]
    exact hnz
  have hnx' : gapCoordLattice P nx = x := by
    rw [← coefficientGAP_coordPoint]
    exact hnx
  let n : (differenceCoefficientGAP P).Coord := fun i ↦
    ⟨(nz i : ℕ) + (P.widths i - 1 - (nx i : ℕ)), by
      have hzlt := (nz i).isLt
      have hxlt := (nx i).isLt
      change (nz i : ℕ) < P.widths i at hzlt
      change (nx i : ℕ) < P.widths i at hxlt
      change (nz i : ℕ) + (P.widths i - 1 - (nx i : ℕ)) <
        2 * (P.widths i - 1) + 1
      omega⟩
  refine Erdos186.GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
  funext j
  rw [differenceCoefficientGAP_coordPoint]
  have hzj := congrFun hnz' j
  have hxj := congrFun hnx' j
  simp only [gapCoordLattice] at hzj hxj
  dsimp [n]
  have hxlt := (nx j).isLt
  change (nx j : ℕ) < P.widths j at hxlt
  have hxle : (nx j : ℕ) ≤ P.widths j - 1 := by omega
  have hw : 1 ≤ P.widths j := P.width_pos j
  change -((P.widths j : ℤ) - 1) +
      (((nz j : ℕ) + (P.widths j - 1 - (nx j : ℕ)) : ℕ) : ℤ) =
    z j - x j
  rw [Nat.cast_add, Nat.cast_sub hxle, Nat.cast_sub hw, hxj, hzj]
  ring

/-- Translating a subset of the coefficient box by the negative of another
coefficient-box point lands in the difference GAP. -/
theorem translate_subset_differenceCoefficientGAP
    (P : Erdos186.GAP d r) {X : Finset (BoxPoint r)}
    (hX : X ⊆ (gapCoefficientBox P).carrier) {x : BoxPoint r}
    (hx : x ∈ (gapCoefficientBox P).carrier) :
    PZ.translate (-x) X ⊆ (differenceCoefficientGAP P).carrier := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  simpa [sub_eq_add_neg] using
    sub_mem_differenceCoefficientGAP_of_mem P (hX hz) hx

/-- The difference coefficient GAP costs at most `2^r` in volume. -/
theorem differenceCoefficientGAP_volume_le (P : Erdos186.GAP d r) :
    (differenceCoefficientGAP P).volume ≤ 2 ^ r * P.volume := by
  rw [Erdos186.GAP.volume, Erdos186.GAP.volume]
  calc
    ∏ i, (differenceCoefficientGAP P).widths i ≤
        ∏ i, 2 * P.widths i := by
      apply Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      intro i _
      change 2 * (P.widths i - 1) + 1 ≤ 2 * P.widths i
      have hi := P.width_pos i
      omega
    _ = 2 ^ r * ∏ i, P.widths i := by
      rw [Finset.prod_mul_distrib]
      simp

end GAP

/-! ## Identification of a subset with its coefficient vectors -/

/-- Restrict the canonical carrier identification of a proper GAP to a
specified subset of its carrier. -/
noncomputable def coordinateEmbeddingOfSubset (P : Erdos186.GAP d r)
    (hP : P.Proper) (A : Finset (BoxPoint d)) (hA : A ⊆ P.carrier) :
    {x // x ∈ A} ↪ BoxPoint r where
  toFun x := gapIdentify P hP ⟨x, hA x.property⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    have hcarrier := gapIdentify_injective P hP hxy
    exact congrArg (fun z : {z // z ∈ P.carrier} ↦ z.val) hcarrier

/-- The image of `A` in the coefficient lattice of `P`. -/
noncomputable def coordinateImage (P : Erdos186.GAP d r) (hP : P.Proper)
    (A : Finset (BoxPoint d)) (hA : A ⊆ P.carrier) : Finset (BoxPoint r) :=
  A.attach.map (coordinateEmbeddingOfSubset P hP A hA)

/-- Every identified point lies in the canonical coefficient box. -/
theorem coordinateImage_subset_coefficientBox (P : Erdos186.GAP d r)
    (hP : P.Proper) (A : Finset (BoxPoint d)) (hA : A ⊆ P.carrier) :
    coordinateImage P hP A hA ⊆ (gapCoefficientBox P).carrier := by
  intro z hz
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_map.mp hz
  exact gapIdentify_mem_coefficientBox P hP ⟨x, hA x.property⟩

/-- Passing to GAP coordinates loses no elements. -/
@[simp]
theorem card_coordinateImage (P : Erdos186.GAP d r) (hP : P.Proper)
    (A : Finset (BoxPoint d)) (hA : A ⊆ P.carrier) :
    (coordinateImage P hP A hA).card = A.card := by
  simp [coordinateImage]

/-- The bounded GAP-coordinate tuple underlying the coordinate embedding. -/
private noncomputable def boundedCoordinateEmbeddingOfSubset
    (P : Erdos186.GAP d r) (hP : P.Proper)
    (A : Finset (BoxPoint d)) (hA : A ⊆ P.carrier) : {x // x ∈ A} ↪ P.Coord where
  toFun x := P.coordinateMap hP ⟨x, hA x.property⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    have hpoint := congrArg P.coordPoint hxy
    simpa only [P.coordPoint_coordinateMap] using hpoint

/-- The canonical coefficient identification preserves the literal
distinct-elements nonaveraging property. -/
theorem coordinateImage_nonaveraging (P : Erdos186.GAP d r) (hP : P.Proper)
    {A : Finset (BoxPoint d)} (hA : A ⊆ P.carrier)
    (hNA : IsBoxNonaveraging A) :
    IsBoxNonaveraging (coordinateImage P hP A hA) := by
  classical
  let e := coordinateEmbeddingOfSubset P hP A hA
  let c := boundedCoordinateEmbeddingOfSubset P hP A hA
  let v : {x // x ∈ A} ↪ BoxPoint d := ⟨Subtype.val, Subtype.val_injective⟩
  intro b hb T hT hcard
  change b ∈ A.attach.map e at hb
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hb
  let U : Finset {x // x ∈ A} := T.preimage e e.injective.injOn
  have hTsub : T ⊆ A.attach.map e := hT.trans (Finset.erase_subset _ _)
  have hmap : U.map e = T := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact Finset.mem_preimage.mp hx
    · intro hy
      obtain ⟨x, _hxA, hxy⟩ := Finset.mem_map.mp (hTsub hy)
      refine Finset.mem_map.mpr ⟨x, Finset.mem_preimage.mpr ?_, hxy⟩
      simpa [hxy] using hy
  let S : Finset (BoxPoint d) := U.map v
  have hSsub : S ⊆ A.erase a := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    have heuT : e u ∈ T := by
      rw [← hmap]
      exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
    have heuErase := Finset.mem_erase.mp (hT heuT)
    apply Finset.mem_erase.mpr
    refine ⟨?_, u.property⟩
    intro hua
    apply heuErase.1
    exact congrArg e (Subtype.ext hua)
  have hcardUT : U.card = T.card := by
    rw [← hmap]
    simp
  have hcardS : S.card = T.card := by
    simp [S, hcardUT]
  intro havg
  apply hNA a a.property S hSsub (by simpa [hcardS] using hcard)
  have havgU : (U.card : ℤ) • e a = ∑ x ∈ U, e x := by
    rw [← hmap] at havg
    simpa using havg
  let C : Finset P.Coord := U.map c
  have hcardCU : C.card = U.card := by simp [C]
  have hec (x : {x // x ∈ A}) : e x = gapCoordLattice P (c x) := rfl
  have havgC : (C.card : ℤ) • gapCoordLattice P (c a) =
      ∑ n ∈ C, gapCoordLattice P n := by
    rw [hcardCU]
    simp only [C, Finset.sum_map]
    simpa only [hec] using havgU
  have hreflect := gap_average_reflect P (c a) C havgC
  have hpoint (x : {x // x ∈ A}) : P.coordPoint (c x) = x := by
    exact P.coordPoint_coordinateMap hP ⟨x, hA x.property⟩
  rw [hcardCU] at hreflect
  simp only [C, Finset.sum_map] at hreflect
  simp_rw [hpoint] at hreflect
  have hcardSU : S.card = U.card := by simp [S]
  have hsumS : ∑ x ∈ S, x = ∑ x ∈ U, (x : BoxPoint d) := by
    simp [S, v]
  rw [hcardSU, hsumS]
  exact hreflect

end

end Erdos186.PZ.Reduction
