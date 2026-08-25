import StackExchange.Puzzling139335.N4OuterPair.Remainder
import StackExchange.Puzzling139335.Mass
import StackExchange.Puzzling139335.TranslationCancellation.Density

/-!
# Reflection invariance of the two middle densities

The original dissection has total weighted density equal almost everywhere
to the indicator of the square.  Passing to real densities permits subtracting
the reflected outer pair.  This proves invariance of the sum of the two middle
densities without any regularity or contact assumption on their union.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

/-- The unconditional four-piece density identity, with values in `ℝ`. -/
theorem SquareDissection.densityReal_sum_ae (d : SquareDissection) :
    (fun x => ∑ i, weightedDensityReal (d.piece i) x) =ᵐ[volume]
      unitSquare.indicator (fun _ => (1 : ℝ)) := by
  filter_upwards [d.density_sum_ae] with x hx
  calc
    ∑ i, weightedDensityReal (d.piece i) x =
        ∑ i, (weightedDensity (d.piece i) x).toReal := by
      simp only [weightedDensityReal_eq_toReal]
    _ = (∑ i, weightedDensity (d.piece i) x).toReal := by
      symm
      exact ENNReal.toReal_sum (fun i _ =>
        ne_top_of_le_ne_top ENNReal.one_ne_top (weightedDensity_le_one (d.piece i) x))
    _ = (unitSquare.indicator (fun _ => (1 : ℝ≥0∞)) x).toReal :=
      congrArg ENNReal.toReal hx
    _ = unitSquare.indicator (fun _ => (1 : ℝ)) x := by
      by_cases hxQ : x ∈ unitSquare <;> simp [hxQ]

namespace N4OuterPair.Configuration

variable {d : SquareDissection}

/-- The horizontal reflection preserves the sum of the actual middle-piece
densities almost everywhere.  It need not preserve either middle piece. -/
theorem middle_density_sum_reflected_ae (h : N4OuterPair.Configuration d) :
    (fun x =>
      weightedDensityReal (d.piece 2) (ReflectionSeparation.horizontal x) +
        weightedDensityReal (d.piece 3) (ReflectionSeparation.horizontal x)) =ᵐ[volume]
      (fun x => weightedDensityReal (d.piece 2) x + weightedDensityReal (d.piece 3) x) := by
  have hpres := affineIsometry_measurePreserving ReflectionSeparation.horizontal
  have hsumH := hpres.quasiMeasurePreserving.ae d.densityReal_sum_ae
  filter_upwards [d.densityReal_sum_ae, hsumH] with x hx hxH
  have houter0 : weightedDensityReal (d.piece 0) (ReflectionSeparation.horizontal x) =
      weightedDensityReal (d.piece 1) x := by
    have heq := weightedDensityReal_image_affineIsometry
      ReflectionSeparation.horizontal (d.piece 1) x
    rwa [h.reflection_back] at heq
  have houter1 : weightedDensityReal (d.piece 1) (ReflectionSeparation.horizontal x) =
      weightedDensityReal (d.piece 0) x := by
    have heq := weightedDensityReal_image_affineIsometry
      ReflectionSeparation.horizontal (d.piece 0) x
    rwa [h.reflected] at heq
  have hindicator : unitSquare.indicator (fun _ => (1 : ℝ))
      (ReflectionSeparation.horizontal x) = unitSquare.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hxQ : x ∈ unitSquare
    · have hxHQ := ReflectionSeparation.horizontal_mem_unitSquare.mpr hxQ
      simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxHQ]
    · have hxHQ : ReflectionSeparation.horizontal x ∉ unitSquare :=
        fun hxH => hxQ (ReflectionSeparation.horizontal_mem_unitSquare.mp hxH)
      simp only [Set.indicator_of_notMem hxQ, Set.indicator_of_notMem hxHQ]
  simp only [Fin.sum_univ_four] at hx hxH
  rw [houter0, houter1, hindicator] at hxH
  linarith

end N4OuterPair.Configuration

end Puzzling139335
