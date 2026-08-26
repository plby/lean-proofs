import ErdosProblems.Erdos633b.DoubledPhysical
import ErdosProblems.Erdos633b.DoubledTrianglePatches
import ErdosProblems.Erdos633b.DoubledTrapezoidPatch
import ErdosProblems.Erdos633b.DoubledCounts

/-! The five genuine geometric patches assemble into the doubled triangle's integral tiling. -/

namespace Erdos633b.DoubledCoordinates

open Sixty DoubledDimensions

noncomputable def doubled_integer_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast ha.trans hab))
      (outer d hd a b c (outerScale a b c) (by exact_mod_cast ha)
        (by exact_mod_cast ha.trans hab) (by exact_mod_cast hc)
        (by exact_mod_cast outerScale_pos a b c (ha.trans hab) hc)).support
      (outerScale a b c ^ 2 * (a + 2 * b) * (2 * a + b)) := by
  have hb : 0 < b := ha.trans hab
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have habr : (a : ℝ) < b := by exact_mod_cast hab
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hm : 0 < outerScale a b c := outerScale_pos a b c hb hc
  have hmr : (0 : ℝ) < outerScale a b c := by exact_mod_cast hm
  have hrelr : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + (a : ℝ) * b + (b : ℝ) ^ 2 := by exact_mod_cast hrel
  let L := DoubledParameters.layout a b c har habr hcr hrelr
  let T := outer d hd a b c (outerScale a b c) har hbr hcr hmr
  let R := groupTwoReference d hd a b har hbr
  have hD := D_coords d hd a b c (outerScale a b c) har hbr hcr hmr hrelr
  have hG := G_coords d hd a b c (outerScale a b c) har hbr hcr hmr hrelr
  have hE := E_coords d hd a b c (outerScale a b c) har hbr hcr hmr hrelr
  have hF := F_coords d hd a b c (outerScale a b c) har hbr hcr hmr
  change T.coord 1 (pointD d a b (outerScale a b c)) = L.u ∧
    T.coord 2 (pointD d a b (outerScale a b c)) = L.v at hD
  change T.coord 1 (pointG d a b (outerScale a b c)) = 1 - L.r ∧
    T.coord 2 (pointG d a b (outerScale a b c)) = L.r at hG
  change T.coord 1 (pointE d a b (outerScale a b c)) = L.ε * L.u ∧
    T.coord 2 (pointE d a b (outerScale a b c)) = L.ε * L.v at hE
  change T.coord 1 (pointF d a b c (outerScale a b c)) = 0 ∧
    T.coord 2 (pointF d a b c (outerScale a b c)) = L.μ at hF
  have patches : ∀ k, Patch R (DoubledPartition.region T L.u L.v L.r L.μ L.height k)
      (pieceCount a b c k) := by
    intro k
    cases k
    · have hp : (L.abdTriangle T).points =
          ![point d 0 0, bigB d c (outerScale a b c), pointD d a b (outerScale a b c)] := by
        simpa [T, outer_points] using L.abdTriangle_points T _ hD
      have result := abd_patch d hd he a b c (outerScale a b c) ha hb hc hm hrel
        (L.abdTriangle T) hp
      rw [L.abdTriangle_support T] at result
      exact result
    · have hp : (L.bdgTriangle T).points = ![bigB d c (outerScale a b c),
          pointD d a b (outerScale a b c), pointG d a b (outerScale a b c)] := by
        simpa [T, outer_points] using L.bdgTriangle_points T _ _ hD hG
      have result := bdg_patch d hd he a b c (outerScale a b c) ha hb hc hm hrel
        (L.bdgTriangle T) hp
      rw [L.bdgTriangle_support T] at result
      exact result
    · have hp : (L.aefTriangle T).points = ![point d 0 0,
          pointE d a b (outerScale a b c), pointF d a b c (outerScale a b c)] := by
        simpa [T, outer_points] using L.aefTriangle_points T _ _ hE hF
      have result := aef_patch d hd he a b c ha hb hc hrel (L.aefTriangle T) hp
      rw [L.aefTriangle_support T] at result
      exact result
    · have hp : (L.cfgTriangle T).points = ![bigC d a b c (outerScale a b c),
          pointF d a b c (outerScale a b c), pointG d a b (outerScale a b c)] := by
        simpa [T, outer_points] using L.cfgTriangle_points T _ _ hF hG
      have result := cfg_patch d hd he a b c ha hab hc hrel (L.cfgTriangle T) hp
      rw [L.cfgTriangle_support T] at result
      exact result
    · exact trapezoid_patch d hd he a b c ha hab hc hrel
  have result := DoubledPartition.assemble T R L.u L.v L.r L.μ L.height L.v_pos L.r_pos
    L.v_lt_r L.r_lt_one L.uv_lt_one L.delta_pos L.height_neg.le (pieceCount a b c) patches
  rw [five_count_identity a b c hab.le hrel] at result
  exact result

noncomputable def doubled_integer_tiling (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Tiling (outer d hd a b c (outerScale a b c) (by exact_mod_cast ha)
      (by exact_mod_cast ha.trans hab) (by exact_mod_cast hc)
      (by exact_mod_cast outerScale_pos a b c (ha.trans hab) hc))
      (outerScale a b c ^ 2 * (a + 2 * b) * (2 * a + b)) :=
  (doubled_integer_patch d hd he a b c ha hab hc hrel).toTiling

end Erdos633b.DoubledCoordinates
