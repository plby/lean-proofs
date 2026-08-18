/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness

/-!
# Enlarging the input of an enhanced CFP witness

The thickness argument applies CFP only to the generators whose convex
coefficients are bounded away from zero.  Equation (15), however, is stated
for the whole oriented side.  The same progression, reserve, and core are a
witness for the larger side after charging the omitted generators to the
loss parameter.  This file records that purely finite change of input.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Regard an enhanced CFP witness on `X` as a witness on a finite superset
`Y`.  The only changed parameter is the honest additional loss `|Y \ X|`.
-/
def CFP.EnhancedCFPWitness.enlargeInput
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness X s D k loss) (hXY : X ⊆ Y) :
    CFP.EnhancedCFPWitness Y s D k (loss + (Y \ X).card) where
  core := W.core
  reserved := W.reserved
  rank := W.rank
  rank_le := W.rank_le
  progression := W.progression
  core_subset := W.core_subset.trans hXY
  reserved_subset_core := W.reserved_subset_core
  core_large := by
    have hdiff := Finset.card_sdiff_of_subset hXY
    have hlarge := W.core_large
    omega
  reserved_small := W.reserved_small
  core_zero_subset := W.core_zero_subset
  homogeneous := W.homogeneous
  translatePoint := W.translatePoint
  covered := W.covered
  dilate_proper := W.dilate_proper
  k_pos := W.k_pos
  scaleNum := W.scaleNum
  scaleDen := W.scaleDen
  scaleNum_pos := W.scaleNum_pos
  scaleDen_pos := W.scaleDen_pos
  scale_lower := W.scale_lower
  scale_upper := W.scale_upper
  progression_proper := W.progression_proper
  progression_symmetric := W.progression_symmetric
  progression_nondegenerate := W.progression_nondegenerate
  covered_translate_homogeneous := W.covered_translate_homogeneous

@[simp] theorem CFP.EnhancedCFPWitness.enlargeInput_core
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness X s D k loss) (hXY : X ⊆ Y) :
    (W.enlargeInput hXY).core = W.core :=
  rfl

@[simp] theorem CFP.EnhancedCFPWitness.enlargeInput_reserved
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness X s D k loss) (hXY : X ⊆ Y) :
    (W.enlargeInput hXY).reserved = W.reserved :=
  rfl

@[simp] theorem CFP.EnhancedCFPWitness.enlargeInput_progression
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness X s D k loss) (hXY : X ⊆ Y) :
    (W.enlargeInput hXY).progression = W.progression :=
  rfl

@[simp] theorem CFP.EnhancedCFPWitness.enlargeInput_translatePoint
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness X s D k loss) (hXY : X ⊆ Y) :
    (W.enlargeInput hXY).translatePoint = W.translatePoint :=
  rfl

end

end Erdos186.PZ.Intersection
