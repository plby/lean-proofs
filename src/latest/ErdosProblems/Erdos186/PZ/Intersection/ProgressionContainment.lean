/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.InitialNoDimensionIncrease
import ErdosProblems.Erdos186.PZ.Intersection.Irreducibility

/-!
# Controlling a CFP progression by the preceding coefficient box

Coverage of the enlarged progression by subset sums controls not only its
volume but also the position of the undilated progression.  If the input of
an enhanced CFP witness lies in the coefficient-difference GAP of `Q`, then
every point of the selected progression differs from its displayed offset by
a point of the fixed `2 * scaleDen` dilation of that difference GAP.

This is the concrete bounding-set clause of Pham--Zakharov Lemma 11.  The
proof uses two covered points of the enlarged progression and cancels the
positive dilation scale with the residue estimate already proved in the
reduction development.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators
open Erdos186.PZ.Reduction.CFP.EnhancedCFPWitness

noncomputable section

set_option autoImplicit false

/-- The two translation notations used by the CFP and PZ developments agree
in the additive commutative lattice. -/
theorem pzTranslate_eq_cfpTranslate {d : ℕ} (v : LatticePoint d)
    (A : Finset (LatticePoint d)) :
    PZ.translate v A = CFP.translate v A := by
  classical
  ext x
  simp [PZ.translate, CFP.translate, add_comm]

/-- Scaling an undilated coordinate tuple gives a valid coordinate tuple in
the `k`-dilate. -/
def scaleCoordIntoDilate {d r : ℕ} (P : GAP d r) (k : ℕ)
    (n : P.Coord) : (P.dilate k).Coord :=
  fun i ↦ ⟨k * (n i : ℕ), by
    have hn : (n i : ℕ) ≤ P.widths i - 1 := by
      omega
    have hmul := Nat.mul_le_mul_left k hn
    change k * (n i : ℕ) < k * (P.widths i - 1) + 1
    omega⟩

/-- Evaluation of the scaled coordinate tuple is `k` times the original
point relative to the displayed offset. -/
theorem coordPoint_scaleCoordIntoDilate {d r : ℕ} (P : GAP d r)
    (k : ℕ) (n : P.Coord) :
    (P.dilate k).coordPoint (scaleCoordIntoDilate P k n) =
      fun j ↦ (k : ℤ) * P.coordPoint n j := by
  funext j
  simp only [GAP.coordPoint, GAP.dilate_offset, GAP.dilate_steps,
    scaleCoordIntoDilate]
  push_cast
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- The zero tuple in the `k`-dilate evaluates to `k` times the original
displayed offset. -/
theorem coordPoint_zeroCoord_dilate {d r : ℕ} (P : GAP d r) (k : ℕ) :
    (P.dilate k).coordPoint (P.dilate k).zeroCoord =
      fun j ↦ (k : ℤ) * P.offset j := by
  funext j
  simp [GAP.coordPoint, GAP.zeroCoord]

/-- **Concrete Lemma-11 bounding-set control.**

If the input of an enhanced CFP witness is contained in the current
coefficient-difference progression, its selected progression is contained
in a translate of the fixed `2 * scaleDen` dilation of that progression.
No abstract bounding-set predicate is assumed. -/
theorem progression_carrier_subset_translate_controlDilation
    {d ambient s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    (Q : GAP ambient d)
    (hA : A ⊆ (Reduction.GAP.differenceCoefficientGAP Q).carrier) :
    W.progression.carrier ⊆
      CFP.translate W.progression.offset
        ((Reduction.GAP.differenceCoefficientGAP Q).dilate
          (2 * W.scaleDen)).carrier := by
  intro q hq
  obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hq
  let nk : (W.progression.dilate k).Coord :=
    scaleCoordIntoDilate W.progression k n
  let nz : (W.progression.dilate k).Coord :=
    (W.progression.dilate k).zeroCoord
  let x : LatticePoint d :=
    W.translatePoint + (W.progression.dilate k).coordPoint nk
  let y : LatticePoint d :=
    W.translatePoint + (W.progression.dilate k).coordPoint nz
  have hx : x ∈ GAP.subsetSums W.reserved := by
    apply W.covered
    exact CFP.mem_translate_iff.mpr
      ⟨(W.progression.dilate k).coordPoint nk,
        (W.progression.dilate k).coordPoint_mem_carrier nk, rfl⟩
  have hy : y ∈ GAP.subsetSums W.reserved := by
    apply W.covered
    exact CFP.mem_translate_iff.mpr
      ⟨(W.progression.dilate k).coordPoint nz,
        (W.progression.dilate k).coordPoint_mem_carrier nz, rfl⟩
  have hdiff : ∀ j, x j - y j =
      (k : ℤ) * (W.progression.coordPoint n - W.progression.offset) j := by
    intro j
    dsimp only [x, y]
    rw [show (W.progression.dilate k).coordPoint nk =
        (fun j ↦ (k : ℤ) * W.progression.coordPoint n j) by
      exact coordPoint_scaleCoordIntoDilate W.progression k n]
    rw [show (W.progression.dilate k).coordPoint nz =
        (fun j ↦ (k : ℤ) * W.progression.offset j) by
      exact coordPoint_zeroCoord_dilate W.progression k]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hcontrol :
      W.progression.coordPoint n - W.progression.offset ∈
        ((Reduction.GAP.differenceCoefficientGAP Q).dilate
          (2 * W.scaleDen)).carrier := by
    have hcoef : Reduction.GAP.differenceCoefficientGAP
        (Reduction.GAP.coefficientGAP Q) =
        Reduction.GAP.differenceCoefficientGAP Q := by
      rfl
    rw [← hcoef]
    exact divided_subsetSum_difference_mem_controlDilation W
      (Reduction.GAP.coefficientGAP Q) (by simpa only [hcoef] using hA) _
        ⟨x, hx, y, hy, hdiff⟩
  exact CFP.mem_translate_iff.mpr
    ⟨W.progression.coordPoint n - W.progression.offset, hcontrol, by
      funext j
      simp⟩

/-! ## The fixed integer control box -/

/-- The axis-parallel integer box underlying a fixed dilation of the current
coefficient-difference GAP. -/
def controlIntegerBox {ambient d : ℕ} (Q : GAP ambient d) (m : ℕ) :
    CFP.IntegerBox d where
  lower i := -((m * (Q.widths i - 1) : ℕ) : ℤ)
  upper i := ((m * (Q.widths i - 1) : ℕ) : ℤ)

/-- The control box is literally the carrier of the corresponding dilated
coefficient-difference GAP. -/
theorem controlIntegerBox_carrier {ambient d : ℕ}
    (Q : GAP ambient d) (m : ℕ) :
    (controlIntegerBox Q m).carrier =
      ((Reduction.GAP.differenceCoefficientGAP Q).dilate m).carrier := by
  ext z
  rw [CFP.IntegerBox.mem_carrier_iff,
    Reduction.GAP.mem_dilate_differenceCoefficientGAP_iff]
  rfl

/-- Cardinal cost of the fixed control box relative to the current
progression volume. -/
theorem controlIntegerBox_card_le {ambient d : ℕ}
    (Q : GAP ambient d) (m : ℕ) :
    (controlIntegerBox Q m).carrier.card ≤
      ((m + 1) ^ d * 2 ^ d) * Q.volume := by
  rw [controlIntegerBox_carrier]
  calc
    ((Reduction.GAP.differenceCoefficientGAP Q).dilate m).carrier.card ≤
        ((Reduction.GAP.differenceCoefficientGAP Q).dilate m).volume :=
      GAP.card_carrier_le_volume _
    _ ≤ (m + 1) ^ d *
        (Reduction.GAP.differenceCoefficientGAP Q).volume :=
      GAP.volume_dilate_le _ _
    _ ≤ (m + 1) ^ d * (2 ^ d * Q.volume) :=
      Nat.mul_le_mul_left _
        (Reduction.GAP.differenceCoefficientGAP_volume_le Q)
    _ = ((m + 1) ^ d * 2 ^ d) * Q.volume := by ring

/-- The bounded selector itself supplies the fixed control box in Lemma 11.
The denominator depends only on the current coefficient dimension because
every selected witness in that ambient lattice uses the context's fixed
scale constants. -/
theorem boundedCoordinateBoundingSetsControlled_of_enhancedCFP
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {ambient : ℕ}
    {A : Finset (LatticePoint ambient)} {hA : selector.Eligible A}
    (delta : ℝ) :
    BoundedCoordinateBoundingSetsControlled selector A hA delta
      (controlIntegerBox (selector.chosen A hA).progression
        (2 * context.scaleDen (selector.chosen A hA).dimension)).carrier := by
  let S := selector.chosen A hA
  intro X hX _hXne _hdense x hx
  dsimp only
  intro hshift
  let shifted := Reduction.identifiedTranslate X x
  let T := selector.chosen shifted hshift
  have hinput : shifted ⊆
      (Reduction.GAP.differenceCoefficientGAP S.progression).carrier := by
    exact Reduction.GAP.translate_subset_differenceCoefficientGAP
      S.progression (hX.trans S.identifiedCore_subset_coefficientBox) hx
  have hcontain := progression_carrier_subset_translate_controlDilation
    T.witness S.progression hinput
  have hden : T.witness.scaleDen = context.scaleDen S.dimension := by
    have hfixed :=
      (selector.input shifted hshift).selectedCFP_scaleDen
    simpa only [T, S, Reduction.BoundedCFPSelector.chosen] using hfixed
  refine ⟨T.progression.offset, ?_⟩
  rw [pzTranslate_eq_cfpTranslate]
  rw [controlIntegerBox_carrier]
  simpa only [T, S, hden] using hcontain

end

end Erdos186.PZ.Intersection
