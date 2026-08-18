/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.DiscreteJohnMixedVolume
import ErdosProblems.Erdos186.PZ.OneStepAssembly

/-!
# The active full-rank discrete-John volume bridge

The positive shrunken-radius certificate directions are completed by lattice
points of the symmetric body.  The resulting integral crosspolytope controls
the product of all nonzero inner widths, while a unit charge handles every
zero width.  This proves the remaining full-rank input to PZ Lemma 7 without
assuming that every certificate radius is positive.
-/

namespace Erdos186.PZ.OneStepAssembly

open scoped BigOperators ENNReal
open DiscreteJohn CFP.Bilu.Mahler

noncomputable section

/-- The Euclidean volume of an integer box is at most the cardinality of its
lattice carrier.  Nonemptiness is used only to order the integral endpoints.
-/
theorem volumeReal_boxRealization_le_card {d : ℕ} (B : IntegerBox d)
    (hB : B.carrier.Nonempty) :
    MeasureTheory.volume.real (boxRealization B) ≤
      (B.carrier.card : ℝ) := by
  obtain ⟨z, hz⟩ := hB
  have horderInt (i : Fin d) : B.lower i ≤ B.upper i :=
    ((IntegerBox.mem_carrier_iff.mp hz) i).1.trans
      ((IntegerBox.mem_carrier_iff.mp hz) i).2
  have horderReal : (fun i ↦ (B.lower i : ℝ)) ≤
      fun i ↦ (B.upper i : ℝ) := by
    intro i
    change (B.lower i : ℝ) ≤ (B.upper i : ℝ)
    exact_mod_cast horderInt i
  have hrealization : boxRealization B =
      ConvexDensity.closedAxisBox
        (fun i ↦ (B.lower i : ℝ)) (fun i ↦ (B.upper i : ℝ)) := by
    ext x
    rfl
  have hvolume :
      MeasureTheory.volume.real (boxRealization B) =
        ∏ i, ((B.upper i : ℝ) - (B.lower i : ℝ)) := by
    rw [hrealization]
    exact
        (ConvexDensity.volume_closedAxisBox_toReal horderReal)
  rw [hvolume, integerBox_card_carrier, Nat.cast_prod]
  apply Finset.prod_le_prod
  · intro i _
    exact sub_nonneg.mpr (horderReal i)
  · intro i _
    have hnonneg : 0 ≤ B.upper i + 1 - B.lower i := by
      have := horderInt i
      omega
    norm_cast
    rw [Int.toNat_of_nonneg hnonneg]
    omega

/-- Every integer-box realization has finite Lebesgue volume. -/
theorem volume_boxRealization_ne_top {d : ℕ} (B : IntegerBox d) :
    MeasureTheory.volume (boxRealization B) ≠ ∞ := by
  simpa [boxRealization, toDiscretizationBox,
    BoxDiscretization.IntegerBox.realization,
    ConvexDensity.closedAxisBox] using
      (ConvexDensity.volume_closedAxisBox_ne_top
        (fun i ↦ (B.lower i : ℝ)) (fun i ↦ (B.upper i : ℝ)))

/-- The unconditional active-rank bridge consumed by the PZ Lemma 7
adapter.  The constant is deliberately coarse; only dimension dependence is
needed in the density iteration. -/
theorem fullRankVolumeBridge : FullRankVolumeBridgeStatement := by
  intro d factorBound pointFactor volumeFactor hd hvolumeFactor
  let widthConstant : ℕ :=
    (2 * factorBound + 1) ^ d * 3 ^ d * d.factorial
  let volumeConstant : ℝ :=
    max 1 ((widthConstant : ℝ) * volumeFactor)
  refine ⟨volumeConstant, le_max_left _ _, ?_⟩
  intro B Omega eta S rank factor C heta hfactor heffective hrank
  have hsection :
      DiscreteJohn.RankReduction.sectionRank S.johnPoints = d :=
    heffective.symm.trans hrank
  clear heffective
  subst rank
  have houterBody : (C.outer.volume : ℝ) ≤
      (widthConstant : ℝ) * MeasureTheory.volume.real S.body := by
    simpa [widthConstant] using
      (DiscreteJohn.outer_volume_le_factorBound_mul_volumeReal C
        S.body_isSymmetricConvex.balanced
        S.body_isSymmetricConvex.convex
        S.body_isSymmetricConvex.bounded S.johnPoints_exact
        hsection hd hfactor)
  have hBnonempty : B.carrier.Nonempty := by
    refine ⟨S.center, ?_⟩
    exact (mem_latticeRestriction.mp S.center_mem).1
  have hvfNonneg : 0 ≤ volumeFactor :=
    zero_le_one.trans hvolumeFactor
  have hvfetaNonneg : 0 ≤ volumeFactor * eta :=
    mul_nonneg hvfNonneg heta.le
  have hrhs_ne_top :
      ENNReal.ofReal (volumeFactor * eta) *
          MeasureTheory.volume (boxRealization B) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (volume_boxRealization_ne_top B)
  have hbodyReal0 := ENNReal.toReal_mono hrhs_ne_top S.body_volume_le
  have hbodyReal :
      MeasureTheory.volume.real S.body ≤
        (volumeFactor * eta) *
          MeasureTheory.volume.real (boxRealization B) := by
    simpa [MeasureTheory.measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hvfetaNonneg] using hbodyReal0
  have hboxCard := volumeReal_boxRealization_le_card B hBnonempty
  have hbodyCard :
      MeasureTheory.volume.real S.body ≤
        (volumeFactor * eta) * (B.carrier.card : ℝ) :=
    hbodyReal.trans (mul_le_mul_of_nonneg_left hboxCard hvfetaNonneg)
  have hwidthNonneg : (0 : ℝ) ≤ (widthConstant : ℝ) := by
    positivity
  have hetaCardNonneg :
      0 ≤ eta * (B.carrier.card : ℝ) :=
    mul_nonneg heta.le (Nat.cast_nonneg _)
  calc
    (C.outer.volume : ℝ) ≤
        (widthConstant : ℝ) * MeasureTheory.volume.real S.body :=
      houterBody
    _ ≤ (widthConstant : ℝ) *
        ((volumeFactor * eta) * (B.carrier.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hbodyCard hwidthNonneg
    _ = ((widthConstant : ℝ) * volumeFactor) *
        (eta * (B.carrier.card : ℝ)) := by ring
    _ ≤ volumeConstant * (eta * (B.carrier.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (le_max_right (1 : ℝ) ((widthConstant : ℝ) * volumeFactor))
        hetaCardNonneg
    _ ≤ volumeConstant *
        (eta * (B.carrier.card : ℝ) + 1) := by
      have hconstantNonneg : 0 ≤ volumeConstant :=
        zero_le_one.trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left (by linarith) hconstantNonneg

end

end Erdos186.PZ.OneStepAssembly
