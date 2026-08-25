import StackExchange.Puzzling139335.WeightedMass
import StackExchange.Puzzling139335.TripleContact

/-!
# Unconditional weighted mass identities for the dissection

The geometric finite-contact theorem discharges the only extra hypothesis
in the measure-theoretic helpers. These identities do not assume that a
Jordan boundary has zero area.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

theorem SquareDissection.density_sum_ae (d : SquareDissection) :
    (fun x => ∑ i, weightedDensity (d.piece i) x) =ᵐ[volume]
      unitSquare.indicator (fun _ => 1) :=
  d.sum_piece_weightedDensity_ae_eq_indicator d.tripleContactSet_finite

theorem SquareDissection.sum_piece_weightedMass_eq_one (d : SquareDissection) :
    ∑ i, weightedMass volume (d.piece i) = 1 :=
  d.sum_piece_weightedMass d.tripleContactSet_finite

theorem SquareDissection.piece_weightedMass_eq_quarter
    (d : SquareDissection) (i : Fin 4) :
    weightedMass volume (d.piece i) = (1 : ℝ≥0∞) / 4 :=
  d.piece_weightedMass d.tripleContactSet_finite i

end Puzzling139335
