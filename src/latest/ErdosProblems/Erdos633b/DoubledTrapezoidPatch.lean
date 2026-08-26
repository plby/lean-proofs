import ErdosProblems.Erdos633b.DoubledTrapezoidGeometry
import ErdosProblems.Erdos633b.DoubledDimensions

/-! Tile the trapezoidal region by the proved integral layer construction. -/

namespace Erdos633b.DoubledCoordinates

open Sixty DoubledDimensions

noncomputable def unplaced_trapezoid_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast ha.trans hab))
      (TrapezoidPartition.trapezoidSet (frame d hd)
        (shortBase a c (outerScale a b c)) (lateralSide a b c (outerScale a b c)))
      (trapezoidCount a b c) := by
  have hh : heightUnits a b c - 1 + 1 = heightUnits a b c :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr (heightUnits_pos a b c hab hc))
  have hw : GroupTwoDimensions.scale a b + (widthUnits a b c - GroupTwoDimensions.scale a b) =
      widthUnits a b c := Nat.add_sub_of_le (widthUnits_ge_scale a b c (ha.trans hab) hc)
  have result := stacked_layers_patch d hd he a b c ha (ha.trans hab) hc hrel
    (heightUnits a b c - 1) (widthUnits a b c - GroupTwoDimensions.scale a b)
  rw [hh, hw, ← shortBase_eq a b c, ← lateralSide_eq a b c (ha.trans hab) hab.le] at result
  exact result

noncomputable def trapezoid_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let L := DoubledParameters.layout a b c (by exact_mod_cast ha) (by exact_mod_cast hab)
      (by exact_mod_cast hc) (by exact_mod_cast hrel)
    let T := outer d hd a b c (outerScale a b c) (by exact_mod_cast ha)
      (by exact_mod_cast ha.trans hab) (by exact_mod_cast hc)
      (by exact_mod_cast outerScale_pos a b c (ha.trans hab) hc)
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast ha.trans hab))
      (DoubledPartition.region T L.u L.v L.r L.μ L.height .trapezoid) (trapezoidCount a b c) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have habr : (a : ℝ) < b := by exact_mod_cast hab
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hmr : (0 : ℝ) < outerScale a b c := by exact_mod_cast outerScale_pos a b c (ha.trans hab) hc
  have hrelr : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + (a : ℝ) * b + (b : ℝ) ^ 2 := by exact_mod_cast hrel
  have result := (unplaced_trapezoid_patch d hd he a b c ha hab hc hrel).move
    (trapezoidTurn d he a b c (outerScale a b c) hcr hrelr)
  have hs := trapezoid_support d hd he a b c (outerScale a b c) har habr hcr hmr hrelr
  dsimp only at hs
  rw [hs] at result
  exact result

end Erdos633b.DoubledCoordinates
