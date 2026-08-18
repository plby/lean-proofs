/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Corollary217MapBack
import ErdosProblems.Erdos186.CFP.HDimension

/-!
# Integer scale contraction for the Corollary 2.17 progression

The common dense-box argument produces a centered progression whose radii
are large on the preprocessing scale.  Before mapping that progression back
to the source line, the source proof divides its coefficient radii by the
preprocessing scale.  The resulting smaller progression can then be dilated
by the product of the old dilation parameter and the preprocessing scale.

This file isolates the finite arithmetic behind that step.  No density,
random-partition, or source-evaluation hypothesis is involved.
-/

namespace Erdos186.CFP

noncomputable section

open Module LatticeBasis

/-- Dilation of the canonical coordinate GAP just multiplies its radii. -/
theorem dilate_symmetricCoordinateGAP_eq {d : ℕ}
    (radius : Fin d → ℕ) (k : ℕ) :
    (symmetricCoordinateGAP radius).dilate k =
      symmetricCoordinateGAP (fun i ↦ k * radius i) := by
  apply GAP.ext
  · funext j
    simp only [GAP.dilate_offset, symmetricCoordinateGAP]
    push_cast
    ring
  · rfl
  · funext i
    simp only [GAP.dilate_widths, symmetricCoordinateGAP_widths]
    rw [Nat.add_sub_cancel]
    ring

/-- Membership in a dilated canonical coordinate GAP is exactly a
coordinatewise absolute-value bound. -/
theorem mem_symmetricCoordinateGAP_dilate_iff {d k : ℕ}
    (radius : Fin d → ℕ) (x : LatticePoint d) :
    x ∈ ((symmetricCoordinateGAP radius).dilate k).carrier ↔
      ∀ i, |x i| ≤ (k * radius i : ℕ) := by
  rw [dilate_symmetricCoordinateGAP_eq]
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
    intro i
    rw [symmetricCoordinateGAP_coordPoint]
    have hn := (n i).isLt
    simp only [symmetricCoordinateGAP_widths] at hn
    rw [abs_le]
    constructor <;> push_cast at hn ⊢ <;> omega
  · intro hx
    let n : (symmetricCoordinateGAP (fun i ↦ k * radius i)).Coord :=
      fun i ↦ ⟨(x i + (k * radius i : ℕ)).toNat, by
        have hi := abs_le.mp (hx i)
        have hnonneg : 0 ≤ x i + (k * radius i : ℕ) := by omega
        rw [Int.toNat_lt hnonneg]
        simp only [symmetricCoordinateGAP_widths]
        push_cast
        omega⟩
    refine GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
    rw [symmetricCoordinateGAP_coordPoint]
    funext i
    dsimp only [n]
    rw [Int.toNat_of_nonneg]
    · ring
    · have hi := (abs_le.mp (hx i)).1
      omega

/-- Dividing the coordinate radii by `h` and then dilating by `h * k`
stays inside the original progression dilated by `k`. -/
theorem symmetricCoordinateGAP_dilate_mul_subset_dilate {d : ℕ}
    (radius : Fin d → ℕ) (h k : ℕ) :
    ((symmetricCoordinateGAP (fun i ↦ radius i / h)).dilate
        (h * k)).carrier ⊆
      ((symmetricCoordinateGAP radius).dilate k).carrier := by
  intro x hx
  rw [mem_symmetricCoordinateGAP_dilate_iff] at hx ⊢
  intro i
  refine (hx i).trans ?_
  exact_mod_cast (show (h * k) * (radius i / h) ≤ k * radius i by
    calc
      (h * k) * (radius i / h) = k * (h * (radius i / h)) := by ring
      _ ≤ k * radius i := Nat.mul_le_mul_left k (Nat.mul_div_le _ _))

/-- Origin-based symmetric axis boxes satisfy the same scale-contraction
inclusion.  This is the exact form used to restrict a dense-box translate
before mapping the Corollary 2.17 progression back to the source. -/
theorem symmetricAxisBox_dilate_mul_subset_dilate {d : ℕ}
    (radius : Fin d → ℕ) (h k : ℕ) :
    ((symmetricAxisBox (fun i ↦ radius i / h)).dilate (h * k)).carrier ⊆
      ((symmetricAxisBox radius).dilate k).carrier := by
  intro x hx
  rw [AxisBox.mem_carrier_iff] at hx ⊢
  intro i
  have hi := hx i
  constructor
  · simpa only [AxisBox.dilate_lower, Pi.zero_apply] using hi.1
  · simp only [AxisBox.dilate_lower, Pi.zero_apply, AxisBox.dilate_width,
      symmetricAxisBox, zero_add] at hi ⊢
    have hrad : (h * k) * (radius i / h) ≤ k * radius i := by
      calc
        (h * k) * (radius i / h) = k * (h * (radius i / h)) := by ring
        _ ≤ k * radius i := Nat.mul_le_mul_left k (Nat.mul_div_le _ _)
    have hwidth :
        (h * k) * (2 * (radius i / h) + 1 - 1) + 1 ≤
          k * (2 * radius i + 1 - 1) + 1 := by
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
      calc
        (h * k) * (2 * (radius i / h)) + 1 =
            2 * ((h * k) * (radius i / h)) + 1 := by ring
        _ ≤ 2 * (k * radius i) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 2 hrad) 1
        _ = k * (2 * radius i) + 1 := by ring
    exact hi.2.trans_le (by exact_mod_cast hwidth)

/-- The same contraction inclusion for the physical centered progression in
the lattice basis selected by Corollary 2.17. -/
theorem basisContraction_dilate_mul_subset_dilate_centeredBasisGAP
    {d : ℕ} {Gamma : Sublattice d}
    (basis : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ) (h k : ℕ) :
    ((GAP.basisContraction basis radius h).dilate (h * k)).carrier ⊆
      ((AdaptedHNF.centeredBasisGAP basis radius).dilate k).carrier := by
  have hleft :
      (GAP.basisContraction basis radius h).dilate (h * k) =
        AdaptedHNF.centeredBasisGAP basis
          (fun i ↦ (h * k) * (radius i / h)) := by
    apply GAP.ext
    · funext j
      simp only [GAP.basisContraction, GAP.dilate_offset,
        AdaptedHNF.centeredBasisGAP]
      rw [mul_neg, Finset.mul_sum]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _hi
      push_cast
      ring
    · rfl
    · funext i
      simp only [GAP.basisContraction, GAP.dilate_widths,
        AdaptedHNF.centeredBasisGAP_widths]
      rw [Nat.add_sub_cancel]
      ring
  have hright :
      (AdaptedHNF.centeredBasisGAP basis radius).dilate k =
        AdaptedHNF.centeredBasisGAP basis (fun i ↦ k * radius i) := by
    apply GAP.ext
    · funext j
      simp only [GAP.dilate_offset, AdaptedHNF.centeredBasisGAP]
      rw [mul_neg, Finset.mul_sum]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _hi
      push_cast
      ring
    · rfl
    · funext i
      simp only [GAP.dilate_widths,
        AdaptedHNF.centeredBasisGAP_widths]
      rw [Nat.add_sub_cancel]
      ring
  rw [hleft, hright, centeredBasisGAP_carrier_eq_basisProgression,
    centeredBasisGAP_carrier_eq_basisProgression]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨a, ?_, rfl⟩
  rw [mem_centeredCoefficientBox_iff] at ha ⊢
  intro i
  refine (ha i).trans ?_
  exact_mod_cast (show (h * k) * (radius i / h) ≤ k * radius i by
    calc
      (h * k) * (radius i / h) = k * (h * (radius i / h)) := by ring
      _ ≤ k * radius i := Nat.mul_le_mul_left k (Nat.mul_div_le _ _))

/-- Dividing positive radii by a no-larger positive scale preserves
nondegeneracy of the canonical coordinate progression. -/
theorem symmetricCoordinateGAP_div_nondegenerate {d : ℕ}
    (radius : Fin d → ℕ) {h : ℕ} (hh : 0 < h)
    (hradius : ∀ i, h ≤ radius i) :
    (symmetricCoordinateGAP (fun i ↦ radius i / h)).Nondegenerate := by
  apply (symmetricCoordinateGAP_centered
    (fun i ↦ radius i / h)).nondegenerate_iff.mpr
  intro i
  exact Nat.div_pos (hradius i) hh

/-- The physical lattice-basis contraction is likewise nondegenerate when
every original radius is at least the contraction scale. -/
theorem basisContraction_nondegenerate_of_scale_le
    {d : ℕ} {Gamma : Sublattice d}
    (basis : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ)
    {h : ℕ} (hh : 0 < h) (hradius : ∀ i, h ≤ radius i) :
    (GAP.basisContraction basis radius h).Nondegenerate := by
  apply (GAP.basisContraction_centered basis radius h).nondegenerate_iff.mpr
  intro i
  exact Nat.div_pos (hradius i) hh

/-- If the centered coordinate box has no width-one coordinate, then its
minimum radius is at least the fold scale used to form it. -/
theorem centeredCoordinateAxisBox_scale_le_minWidth_sub_one
    {d : ℕ} (hd : 0 < d) (P : GAP 1 d) {h : ℕ} (hh : 0 < h)
    (hwidth : 2 ≤ (Preprocessing.centeredCoordinateAxisBox P h).minWidth) :
    h ≤ (Preprocessing.centeredCoordinateAxisBox P h).minWidth - 1 := by
  let Q := Preprocessing.centeredCoordinateAxisBox P h
  have hmin : 2 * h + 1 ≤ Q.minWidth := by
    rw [AxisBox.minWidth, dif_pos hd]
    apply Finset.le_inf'
    intro i _hi
    have hwidthi : 2 ≤ Q.widths i :=
      hwidth.trans (Q.minWidth_le hd i)
    have hactive : 1 ≤ P.widths i - 1 := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hzero
      simp only [Q, Preprocessing.centeredCoordinateAxisBox,
        GAP.dilate_widths, hzero, mul_zero, zero_add] at hwidthi
      omega
    change 2 * h + 1 ≤ (2 * h) * (P.widths i - 1) + 1
    simpa only [Nat.mul_one] using Nat.add_le_add_right
      (Nat.mul_le_mul_left (2 * h) hactive) 1
  change h ≤ Q.minWidth - 1
  omega

/-- The radius lower bound retained by a Corollary 2.17 certificate is
large enough to divide by the source fold scale. -/
theorem Corollary217Certificate.sourceScale_le_radius
    {d : ℕ} (hd : 0 < d) {P : GAP 1 d} {sourceScale : ℕ}
    {S : Finset (LatticePoint d)}
    (cert : Corollary217Certificate
      (Preprocessing.centeredCoordinateAxisBox P sourceScale) S)
    (hsourceScale : 0 < sourceScale)
    (hwidth : 2 ≤
      (Preprocessing.centeredCoordinateAxisBox P sourceScale).minWidth) :
    ∀ i, sourceScale ≤ cert.radius i := by
  intro i
  exact (centeredCoordinateAxisBox_scale_le_minWidth_sub_one
    hd P hsourceScale hwidth).trans (cert.radius_lower i)

/-- Consequently the divided physical certificate progression remains
nondegenerate. -/
theorem Corollary217Certificate.basisContraction_nondegenerate
    {d : ℕ} (hd : 0 < d) {P : GAP 1 d} {sourceScale : ℕ}
    {S : Finset (LatticePoint d)}
    (cert : Corollary217Certificate
      (Preprocessing.centeredCoordinateAxisBox P sourceScale) S)
    (hsourceScale : 0 < sourceScale)
    (hwidth : 2 ≤
      (Preprocessing.centeredCoordinateAxisBox P sourceScale).minWidth) :
    (GAP.basisContraction cert.basis cert.radius sourceScale).Nondegenerate := by
  exact basisContraction_nondegenerate_of_scale_le
    cert.basis cert.radius hsourceScale
    (cert.sourceScale_le_radius hd hsourceScale hwidth)

end

end Erdos186.CFP

#print axioms Erdos186.CFP.symmetricCoordinateGAP_dilate_mul_subset_dilate
#print axioms
  Erdos186.CFP.basisContraction_dilate_mul_subset_dilate_centeredBasisGAP
