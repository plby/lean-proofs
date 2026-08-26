import ErdosProblems.Erdos633b.DoubledRotation
import ErdosProblems.Erdos633b.DoubledTrapezoidSupport

/-! The four vertices of the rigidly placed trapezoid are exactly F,E,D,G. -/

namespace Erdos633b.DoubledCoordinates

open Sixty

noncomputable def shortBase (a c m : ℝ) : ℝ := m * a * c
noncomputable def lateralSide (a b c m : ℝ) : ℝ := m * a * c * (b - a) / (a + b)

theorem shortBase_pos (a c m : ℝ) (ha : 0 < a) (hc : 0 < c) (hm : 0 < m) :
    0 < shortBase a c m := by unfold shortBase; positivity

theorem lateralSide_pos (a b c m : ℝ) (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hm : 0 < m) :
    0 < lateralSide a b c m := by
  have hb : 0 < b := ha.trans hab
  unfold lateralSide
  positivity

theorem trapezoidTurn_vertices (d : ℝ) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 4) :
    trapezoidTurn d he a b c m hc hrel
      (![point d 0 0, point d (shortBase a c m + lateralSide a b c m) 0,
        point d (shortBase a c m) (lateralSide a b c m),
        point d 0 (lateralSide a b c m)] i) =
      ![pointF d a b c m, pointE d a b m, pointD d a b m, pointG d a b m] i := by
  have hZ : 0 < a + b := add_pos ha hb
  fin_cases i
  · change trapezoidTurn d he a b c m hc hrel (point d 0 0) = pointF d a b c m
    rw [trapezoidTurn_point]
    simp [point_zero]
  · change trapezoidTurn d he a b c m hc hrel
      (point d (shortBase a c m + lateralSide a b c m) 0) = pointE d a b m
    rw [trapezoidTurn_point, pointF_eq d a b c m ha hb hc, pointE_eq, ← point_add]
    congr 1 <;> dsimp only [shortBase, lateralSide] <;> field_simp <;> ring
  · change trapezoidTurn d he a b c m hc hrel
      (point d (shortBase a c m) (lateralSide a b c m)) = pointD d a b m
    rw [trapezoidTurn_point, pointF_eq d a b c m ha hb hc, pointD, ← point_add]
    congr 1 <;> dsimp only [shortBase, lateralSide] <;> field_simp <;> ring
  · change trapezoidTurn d he a b c m hc hrel
      (point d 0 (lateralSide a b c m)) = pointG d a b m
    rw [trapezoidTurn_point, pointF_eq d a b c m ha hb hc, pointG, ← point_add]
    congr 1 <;> dsimp only [shortBase, lateralSide] <;> field_simp <;> ring

theorem trapezoid_scale (a b c m : ℝ) (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let L := DoubledParameters.layout a b c ha hab hc hrel
    DoubledPartition.delta L.u L.v L.r * (shortBase a c m + lateralSide a b c m) =
      L.u * L.μ * shortBase a c m := by
  have hb : 0 < b := ha.trans hab
  have hZ : 0 < a + b := add_pos ha hb
  have hP : 0 < a + 2 * b := by linarith
  have hQ : 0 < 2 * a + b := by linarith
  dsimp only [DoubledParameters.layout, DoubledPartition.delta, shortBase, lateralSide]
  rw [hrel]
  field_simp
  ring

end Erdos633b.DoubledCoordinates
