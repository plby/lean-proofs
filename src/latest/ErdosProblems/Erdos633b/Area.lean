import ErdosProblems.Erdos633b.Geometry
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Area of an actual congruent-triangle tiling

The only disjointness assumption is disjoint interiors. Convex boundaries
have measure zero, so finite additivity applies to these geometric tilings.
-/

open MeasureTheory
open scoped ENNReal

namespace Erdos633b

namespace Triangle

theorem support_isCompact (T : Triangle) : IsCompact T.support :=
  (Set.finite_range T.points).isCompact_convexHull ℝ

theorem interior_support_nonempty (T : Triangle) : (interior T.support).Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  exact T.span_eq_top (by simp [Plane])

theorem volume_support_pos (T : Triangle) : 0 < volume T.support :=
  Measure.measure_pos_of_nonempty_interior volume T.interior_support_nonempty

theorem volume_support_ne_top (T : Triangle) : volume T.support ≠ ∞ :=
  T.support_isCompact.measure_ne_top

noncomputable def area (T : Triangle) : ℝ := (volume T.support).toReal

theorem area_pos (T : Triangle) : 0 < T.area :=
  ENNReal.toReal_pos T.volume_support_pos.ne' T.volume_support_ne_top

end Triangle

theorem rigidMotion_measurePreserving (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    MeasurePreserving g volume volume := by
  have h := (measurePreserving_add_right (volume : Measure Plane) (g 0)).comp
    g.linearIsometryEquiv.measurePreserving
  have heq : (g : Plane → Plane) = (fun x => x + g 0) ∘ g.linearIsometryEquiv := by
    funext x
    simpa using (g.map_vadd (0 : Plane) x)
  rw [heq]
  exact h

theorem volume_rigidMotion_support (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    volume (g '' T.support) = volume T.support := by
  have h := rigidMotion_measurePreserving g
  have hm : MeasurableSet (g '' T.support) :=
    (T.support_isCompact.image g.continuous).isClosed.measurableSet
  calc
    volume (g '' T.support) = (Measure.map g volume) (g '' T.support) := by rw [h.map_eq]
    _ = volume (g ⁻¹' (g '' T.support)) := Measure.map_apply h.measurable hm
    _ = volume T.support := by rw [Set.preimage_image_eq _ g.injective]

namespace Tiling

theorem piece_volume_interior {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin n) :
    volume (interior (d.place i '' d.tile.support)) = volume d.tile.support := by
  have hc : Convex ℝ (d.place i '' d.tile.support) :=
    d.tile.support_convex.affine_image (d.place i).toAffineMap
  rw [measure_interior_of_null_frontier (hc.addHaar_frontier volume),
    volume_rigidMotion_support]

/-- Finite area additivity with boundary intersections allowed. -/
theorem volume_eq_mul {T : Triangle} {n : ℕ} (d : Tiling T n) :
    volume T.support = n * volume d.tile.support := by
  have hpiece (i : Fin n) :
      volume (d.place i '' d.tile.support) ≤
        volume (interior (d.place i '' d.tile.support)) := by
    rw [d.piece_volume_interior, volume_rigidMotion_support]
  calc
    volume T.support = volume (⋃ i, d.place i '' d.tile.support) := by rw [d.covers]
    _ = volume (⋃ i, interior (d.place i '' d.tile.support)) :=
      (measure_iUnion_congr_of_subset (fun _ => interior_subset) hpiece).symm
    _ = ∑' i, volume (interior (d.place i '' d.tile.support)) :=
      measure_iUnion d.disjoint_interiors (fun _ => isOpen_interior.measurableSet)
    _ = n * volume d.tile.support := by simp [d.piece_volume_interior]

theorem area_eq_mul {T : Triangle} {n : ℕ} (d : Tiling T n) :
    T.area = n * d.tile.area := by
  have h := congrArg ENNReal.toReal d.volume_eq_mul
  simpa only [Triangle.area, ENNReal.toReal_mul, ENNReal.toReal_natCast] using h

end Tiling

end Erdos633b
