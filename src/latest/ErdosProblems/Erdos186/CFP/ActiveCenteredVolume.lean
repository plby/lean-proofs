/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ActiveCenteredIdentification

/-!
# Volume invariance after deleting inactive coordinates

Displayed width-one coordinates contribute the factor one to every dilated
volume.  Deleting them therefore preserves volume at every scale.
-/

namespace Erdos186.CFP

noncomputable section

namespace GAP

/-- Deleting width-one coordinates preserves every dilated displayed
volume. -/
theorem volume_dilate_activeDimensions {ambient rank : ℕ}
    (P : GAP ambient rank) (k : ℕ) :
    (P.activeDimensions.dilate k).volume = (P.dilate k).volume := by
  classical
  let f : Fin rank → ℕ := fun i ↦ k * (P.widths i - 1) + 1
  have hinactive :
      (∏ i : {i : Fin rank // ¬ 2 ≤ P.widths i}, f i) = 1 := by
    apply Finset.prod_eq_one
    intro i _hi
    have hwidth : P.widths i = 1 := by
      have := P.width_pos i
      omega
    simp [f, hwidth]
  rw [GAP.volume, GAP.volume]
  simp only [GAP.dilate_widths, GAP.activeDimensions]
  change (∏ j : Fin P.activeRank, f (P.activeIndex j)) = ∏ i, f i
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : Fin rank ↦ 2 ≤ P.widths i) f, hinactive, mul_one]
  apply Fintype.prod_equiv P.activeIndex
  intro j
  rfl

end GAP

namespace Preprocessing

/-- The centered coordinate-box volume is unchanged after passing to active
coordinates. -/
theorem centeredCoordinateAxisBox_activeDimensions_volume
    {d : ℕ} (P : GAP 1 d) (sourceScale : ℕ) :
    (centeredCoordinateAxisBox P.activeDimensions sourceScale).volume =
      (centeredCoordinateAxisBox P sourceScale).volume := by
  rw [centeredCoordinateAxisBox_volume, centeredCoordinateAxisBox_volume]
  exact GAP.volume_dilate_activeDimensions P (2 * sourceScale)

end Preprocessing

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.Preprocessing.centeredCoordinateAxisBox_activeDimensions_volume
