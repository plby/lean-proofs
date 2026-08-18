/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ActivatedCenteredAxisBox
import ErdosProblems.Erdos186.CFP.CenteredScaledRankFlexiblePhysicalCertificate

/-!
# Density transport to activated centered coordinate boxes

Activating width-one coordinates enlarges the centered coordinate box by at
most `2 ^ D` in volume when the displayed rank is at most `D`.  This module
records the exact density-denominator loss used by the physical-target
argument.  It deliberately does not assert that activation supplies the much
larger minimum-width hypothesis of Corollary 2.17: activation only supplies
minimum width two.
-/

namespace Erdos186.CFP

noncomputable section

namespace AxisBox

/-- A density inequality for a box remains true after activating its
width-one coordinates, at the cost of multiplying the denominator by
`2 ^ D`. -/
theorem density_activateWidths_of_rank_le {d D cNum cDen target : ℕ}
    (Q : AxisBox d) (hdD : d ≤ D)
    (hdensity : cNum * Q.volume ≤ cDen * target) :
    cNum * Q.activateWidths.volume ≤
      (2 ^ D * cDen) * target := by
  calc
    cNum * Q.activateWidths.volume ≤
        cNum * (2 ^ D * Q.volume) := by
      apply Nat.mul_le_mul_left
      exact (volume_activateWidths_le Q).trans
        (Nat.mul_le_mul_right Q.volume
          (Nat.pow_le_pow_right (by omega) hdD))
    _ = 2 ^ D * (cNum * Q.volume) := by ring
    _ ≤ 2 ^ D * (cDen * target) := Nat.mul_le_mul_left _ hdensity
    _ = (2 ^ D * cDen) * target := by ring

end AxisBox

namespace Preprocessing

/-- A family contained in the ordinary centered coordinate box is contained
in the activated centered coordinate box. -/
theorem centeredCoordinateFamily_subset_activated
    {d q sourceScale : ℕ} (P : GAP 1 d)
    {A : Fin q → Finset (LatticePoint d)}
    (hA : ∀ i, A i ⊆ (centeredCoordinateAxisBox P sourceScale).carrier) :
    ∀ i, A i ⊆ (activatedCenteredCoordinateAxisBox P sourceScale).carrier := by
  intro i
  exact (hA i).trans
    (centeredCoordinateAxisBox_subset_activated P sourceScale)

/-- The exact family-density transport for an activated centered coordinate
box. -/
theorem centeredCoordinateFamily_density_activated_of_rank_le
    {d D q sourceScale cNum cDen : ℕ} (P : GAP 1 d)
    {A : Fin q → Finset (LatticePoint d)} (hdD : d ≤ D)
    (hdensity : ∀ i,
      cNum * (centeredCoordinateAxisBox P sourceScale).volume ≤
        cDen * (A i).card) :
    ∀ i,
      cNum * (activatedCenteredCoordinateAxisBox P sourceScale).volume ≤
        (2 ^ D * cDen) * (A i).card := by
  intro i
  exact AxisBox.density_activateWidths_of_rank_le
    (centeredCoordinateAxisBox P sourceScale) hdD (hdensity i)

/-- The rank-flexible target bound transported to the activated centered
coordinate box.  The only new loss is the explicit factor `2 ^ D`. -/
theorem HApproximation.activatedCenteredCoordinateAxisBox_volume_le_physicalTarget_of_le
    {W : Finset ℤ}
    {x D n fold sourceScale d scaleNum scaleDen coefficient target : ℕ}
    (hstable : Stability.WeaklyStableMinimalFor W x D n)
    (V : HDimension.HApproximation W fold d scaleNum scaleDen)
    (hd : 0 < d) (hdD : d ≤ D) (hfoldn : fold ≤ n)
    (hsourceScale : sourceScale ≤ fold)
    (hinterval : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    (hnumeric :
      (2 * scaleDen) ^ d * (fold + 1) ^ (d - 1) <
        (scaleNum * fold) ^ d)
    (hphysical : (GrowthLemmas.multifoldSumset fold W).card ≤
      coefficient * target) :
    (activatedCenteredCoordinateAxisBox
        (BoundingBox.dBoundingBox W d hd).progression sourceScale).volume ≤
      (2 ^ D * (4 * (6 * scaleDen) ^ D * coefficient)) * target := by
  have hraw :=
    HApproximation.centeredCoordinateAxisBox_volume_le_physicalTarget_of_le
      hstable V hd hdD hfoldn hsourceScale hinterval hnumeric hphysical
  calc
    (activatedCenteredCoordinateAxisBox
        (BoundingBox.dBoundingBox W d hd).progression sourceScale).volume ≤
        2 ^ D *
          (centeredCoordinateAxisBox
            (BoundingBox.dBoundingBox W d hd).progression sourceScale).volume :=
      activatedCenteredCoordinateAxisBox_volume_le _ _ hdD
    _ ≤ 2 ^ D *
          ((4 * (6 * scaleDen) ^ D * coefficient) * target) :=
      Nat.mul_le_mul_left _ hraw
    _ = (2 ^ D * (4 * (6 * scaleDen) ^ D * coefficient)) * target := by
      ring

end Preprocessing

/-- The source-facing density denominator after activating the final centered
coordinate box. -/
def activatedRankFlexiblePhysicalDensityDenominator
    (D M scaleDen : ℕ) : ℕ :=
  2 ^ D * rankFlexiblePhysicalDensityDenominator D M scaleDen

theorem rankFlexiblePhysicalDensityDenominator_le_activated
    (D M scaleDen : ℕ) :
    rankFlexiblePhysicalDensityDenominator D M scaleDen ≤
      activatedRankFlexiblePhysicalDensityDenominator D M scaleDen := by
  dsimp only [activatedRankFlexiblePhysicalDensityDenominator]
  exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) D)

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.Preprocessing.HApproximation.activatedCenteredCoordinateAxisBox_volume_le_physicalTarget_of_le
