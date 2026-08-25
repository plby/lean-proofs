import StackExchange.Puzzling139335.PackingMass.Basic
import StackExchange.Puzzling139335.TripleContact
import StackExchange.Puzzling139335.Mass
import StackExchange.Puzzling139335.WeightedMass.Square

/-!
# Weighted mass bounds for Jordan packings

Finitely many Jordan regions with disjoint interiors have only finitely many
triple contacts.  Thus the packing inequalities apply without a separate
contact-set hypothesis and without assuming the regions cover their container.
Congruence separately determines the total weighted mass of four copies of
the pieces of a square dissection.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

section JordanPacking

variable {ι : Type*} [Fintype ι]

/-- The weighted densities of a finite Jordan packing are bounded almost
everywhere by the indicator of any containing set. -/
theorem jordan_regions_sum_weightedDensity_ae_le_indicator
    (P : ι → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {S : Set Plane} (hsub : ∀ i, P i ⊆ S) :
    (fun x => ∑ i, weightedDensity (P i) x) ≤ᵐ[volume]
      S.indicator (fun _ => 1) :=
  sum_weightedDensity_ae_le_indicator P (fun i => (hP i).isClosed)
    (fun i => (hP i).closure_interior) hdis hsub volume
    ((jordan_regions_tripleContactSet_finite P hP hdis).measure_zero volume)

/-- A finite Jordan packing has total weighted mass at most the volume of
its measurable container. -/
theorem jordan_regions_sum_weightedMass_le_volume
    (P : ι → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {S : Set Plane} (hsub : ∀ i, P i ⊆ S) (hS : MeasurableSet S) :
    ∑ i, weightedMass volume (P i) ≤ volume S :=
  sum_weightedMass_le_measure P (fun i => (hP i).isClosed)
    (fun i => (hP i).closure_interior) hdis hsub hS volume
    ((jordan_regions_tripleContactSet_finite P hP hdis).measure_zero volume)

/-- A Jordan packing contained in the unit square has weighted mass at most
one; covering the square is not an assumption. -/
theorem jordan_regions_sum_weightedMass_le_one
    (P : ι → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hsub : ∀ i, P i ⊆ unitSquare) :
    ∑ i, weightedMass volume (P i) ≤ 1 := by
  simpa only [volume_unitSquare] using
    jordan_regions_sum_weightedMass_le_volume P hP hdis hsub measurableSet_unitSquare

end JordanPacking

/-- Any region congruent to a dissection piece has weighted mass one quarter. -/
theorem SquareDissection.weightedMass_eq_quarter_of_congruent
    (d : SquareDissection) {P : Set Plane} {i : Fin 4}
    (hcongr : Congruent P (d.piece i)) :
    weightedMass volume P = (1 : ℝ≥0∞) / 4 :=
  hcongr.weightedMass_eq.trans (d.piece_weightedMass_eq_quarter i)

/-- Four copies, one congruent to each original piece, have total weighted
mass one regardless of their new positions. -/
theorem SquareDissection.sum_weightedMass_eq_one_of_congruent
    (d : SquareDissection) (P : Fin 4 → Set Plane)
    (hcongr : ∀ i, Congruent (P i) (d.piece i)) :
    ∑ i, weightedMass volume (P i) = 1 := by
  calc
    ∑ i, weightedMass volume (P i) = ∑ _i : Fin 4, (1 : ℝ≥0∞) / 4 := by
      apply Finset.sum_congr rfl
      intro i _
      exact d.weightedMass_eq_quarter_of_congruent (hcongr i)
    _ = 1 := by
      norm_num
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Four copies of a fixed original piece also have total weighted mass one;
no containment or disjointness assumption is needed for this identity. -/
theorem SquareDissection.sum_weightedMass_eq_one_of_congruent_piece
    (d : SquareDissection) (i : Fin 4) (P : Fin 4 → Set Plane)
    (hcongr : ∀ j, Congruent (P j) (d.piece i)) :
    ∑ j, weightedMass volume (P j) = 1 := by
  calc
    ∑ j, weightedMass volume (P j) = ∑ _j : Fin 4, (1 : ℝ≥0∞) / 4 := by
      apply Finset.sum_congr rfl
      intro j _
      exact d.weightedMass_eq_quarter_of_congruent (hcongr j)
    _ = 1 := by
      norm_num
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

end Puzzling139335
