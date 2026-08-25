import StackExchange.Puzzling139335.WeightedMass.Family
import StackExchange.Puzzling139335.WeightedMass.Isometry
import StackExchange.Puzzling139335.WeightedMass.Square
import StackExchange.Puzzling139335.JordanRegion

/-!
# Equal weighted areas of the four Jordan pieces

The measure argument only needs the triple-contact set to have zero area.
The finite-set hypothesis below is kept explicit, so the geometric proof of
triple-contact finiteness can be supplied independently.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

/-- Away from triple contacts, the four densities add to one in the interior
of the square. -/
theorem SquareDissection.sum_piece_weightedDensity_eq_one (d : SquareDissection)
    {x : Plane} (hx : x ∈ interior unitSquare)
    (htriple : x ∉ tripleContactSet d.piece) :
    ∑ i, weightedDensity (d.piece i) x = 1 :=
  sum_weightedDensity_eq_one d.piece (fun i => (d.jordan i).isClosed)
    (fun i => (d.jordan i).closure_interior) d.disjoint_interiors d.covers hx htriple

/-- The densities give the square's indicator almost everywhere, even when
the piece frontiers themselves have positive area. -/
theorem SquareDissection.sum_piece_weightedDensity_ae_eq_indicator
    (d : SquareDissection) (hfinite : (tripleContactSet d.piece).Finite) :
    (fun x => ∑ i, weightedDensity (d.piece i) x) =ᵐ[volume]
      unitSquare.indicator (fun _ => 1) :=
  sum_weightedDensity_ae_eq_indicator d.piece (fun i => (d.jordan i).isClosed)
    (fun i => (d.jordan i).closure_interior) d.disjoint_interiors d.covers
    volume volume_frontier_unitSquare (hfinite.measure_zero volume)

/-- If triple contacts form a finite set, the four weighted masses sum to the
area of the unit square. -/
theorem SquareDissection.sum_piece_weightedMass (d : SquareDissection)
    (hfinite : (tripleContactSet d.piece).Finite) :
    ∑ i, weightedMass volume (d.piece i) = 1 := by
  calc
    ∑ i, weightedMass volume (d.piece i) = volume unitSquare :=
      sum_weightedMass_eq_measure d.piece (fun i => (d.jordan i).isClosed)
        (fun i => (d.jordan i).closure_interior) d.disjoint_interiors d.covers
        volume volume_frontier_unitSquare (hfinite.measure_zero volume)
    _ = 1 := volume_unitSquare

/-- Each congruent piece has one quarter of the weighted area, without a
zero-area assumption on the individual piece frontiers. -/
theorem SquareDissection.piece_weightedMass (d : SquareDissection)
    (hfinite : (tripleContactSet d.piece).Finite) (i : Fin 4) :
    weightedMass volume (d.piece i) = (1 : ℝ≥0∞) / 4 := by
  apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2
  calc
    4 * weightedMass volume (d.piece i) =
        ∑ _j : Fin 4, weightedMass volume (d.piece i) := by
      simp [nsmul_eq_mul]
    _ = ∑ j, weightedMass volume (d.piece j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (d.congruent i j).weightedMass_eq
    _ = 1 := d.sum_piece_weightedMass hfinite

end Puzzling139335
