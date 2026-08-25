import StackExchange.Puzzling139335.RectangularHull.Transport
import StackExchange.Puzzling139335.RectangularHull.Interlacing

/-!
# Disjoint Jordan pieces cannot have the same rectangular hull

An affine homeomorphism normalizes the actual common hull to the unit
square. All four vertices belong to each original piece by extremality.
The two diagonally opposite pairs then alternate on the square boundary.
-/

open Set

namespace Puzzling139335.RectangularHull

theorem same_rectangular_hull_impossible {P Q : Set Plane} (R : Frame)
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q))
    (hPHull : convexHull ℝ P = R.carrier)
    (hQHull : convexHull ℝ Q = R.carrier) : False := by
  let e : Plane ≃ₜ Plane := R.fromUnitSquare.symm.toHomeomorph
  have hPS : e '' P ⊆ unitSquare := by
    rintro x ⟨p, hp, rfl⟩
    exact (R.toUnitSquare_mem_unitSquare_iff p).mpr
      (R.subset_carrier_of_convexHull_eq hPHull hp)
  have hQS : e '' Q ⊆ unitSquare := by
    rintro x ⟨q, hq, rfl⟩
    exact (R.toUnitSquare_mem_unitSquare_iff q).mpr
      (R.subset_carrier_of_convexHull_eq hQHull hq)
  have hPv (j : Fin 4) : corner j ∈ e '' P := by
    refine ⟨R.fromUnitSquare (corner j), ?_, R.fromUnitSquare.symm_apply_apply _⟩
    apply R.vertices_subset_of_convexHull_eq hPHull
    rw [← R.fromUnitSquare_image_corners]
    exact mem_image_of_mem _ (mem_range_self j)
  have hQv (j : Fin 4) : corner j ∈ e '' Q := by
    refine ⟨R.fromUnitSquare (corner j), ?_, R.fromUnitSquare.symm_apply_apply _⟩
    apply R.vertices_subset_of_convexHull_eq hQHull
    rw [← R.fromUnitSquare_image_corners]
    exact mem_image_of_mem _ (mem_range_self j)
  exact bottom_top_interlacing_impossible (hP.image_homeomorph e)
    (hQ.image_homeomorph e) hPS hQS (disjoint_interiors_image_homeomorph hdis e)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) (by norm_num)
    (by simpa [corner, Schoenflies.Plane.mk] using hPv 0)
    (by simpa [corner, Schoenflies.Plane.mk] using hPv 2)
    (by simpa [corner, Schoenflies.Plane.mk] using hQv 1)
    (by simpa [corner, Schoenflies.Plane.mk] using hQv 3)

theorem squareDissection_distinct_rectangular_hulls (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) (R : Frame)
    (hi : convexHull ℝ (d.piece i) = R.carrier) :
    convexHull ℝ (d.piece j) ≠ R.carrier := by
  intro hj
  exact same_rectangular_hull_impossible R (d.jordan i) (d.jordan j)
    (d.disjoint_interiors hij) hi hj

end Puzzling139335.RectangularHull
