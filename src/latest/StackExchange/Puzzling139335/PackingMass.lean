import StackExchange.Puzzling139335.PackingMass.Basic
import StackExchange.Puzzling139335.PackingMass.Jordan
import StackExchange.Puzzling139335.PackingMass.Saturation
import StackExchange.Puzzling139335.SquareExterior

/-!
# Saturation of a packing by four congruent pieces

There is no coverage assumption on the new family. Its weighted masses bound
the measure of its actual union from below. If their sum reaches the area of
the square, finite closedness and regularity of the square force full coverage.
This is the measure bridge used for new symmetry images of an original piece.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

section GeneralPacking

variable {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [Fintype ι]

/-- Saturating the ambient measure by the sum of packing masses leaves a null
complement in the ambient set. -/
theorem packing_null_complement_of_mass_saturation
    (P : ι → Set X) (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {S : Set X} (hsub : ∀ i, P i ⊆ S) (μ : Measure X)
    (hSfinite : μ S ≠ ∞) (htriple : μ (tripleContactSet P) = 0)
    (hmass : μ S ≤ ∑ i, weightedMass μ (P i)) : μ (S \ ⋃ i, P i) = 0 := by
  have hK : IsClosed (⋃ i, P i) := isClosed_iUnion_of_finite hclosed
  have hbound : ∑ i, weightedMass μ (P i) ≤ μ (⋃ i, P i) :=
    sum_weightedMass_le_measure P hclosed hreg hdisj
      (fun i x hx => mem_iUnion.mpr ⟨i, hx⟩) hK.measurableSet μ htriple
  exact PackingMass.measure_sdiff_eq_zero_of_saturation hK.measurableSet
    (iUnion_subset hsub) hSfinite (hmass.trans hbound)

/-- A saturated packing in a regular closed container covers it exactly,
including the container boundary. -/
theorem packing_iUnion_eq_of_mass_saturation
    (P : ι → Set X) (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {S : Set X} (hsub : ∀ i, P i ⊆ S) (μ : Measure X) [μ.IsOpenPosMeasure]
    (hSregular : closure (interior S) = S) (hSfinite : μ S ≠ ∞)
    (htriple : μ (tripleContactSet P) = 0)
    (hmass : μ S ≤ ∑ i, weightedMass μ (P i)) : (⋃ i, P i) = S := by
  apply Subset.antisymm (iUnion_subset hsub)
  exact PackingMass.subset_of_isClosed_of_null_sdiff
    (isClosed_iUnion_of_finite hclosed) hSregular
    (packing_null_complement_of_mass_saturation P hclosed hreg hdisj hsub μ
      hSfinite htriple hmass)

/-- In an arbitrary finite-measure ambient set, saturation still excludes
every nonempty open gap; regularity of the ambient set is unnecessary. -/
theorem packing_no_open_gap_of_mass_saturation
    (P : ι → Set X) (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {S : Set X} (hsub : ∀ i, P i ⊆ S) (μ : Measure X) [μ.IsOpenPosMeasure]
    (hSfinite : μ S ≠ ∞) (htriple : μ (tripleContactSet P) = 0)
    (hmass : μ S ≤ ∑ i, weightedMass μ (P i))
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) (hUS : U ⊆ S) :
    ¬ Disjoint U (⋃ i, P i) := by
  intro hgap
  exact hne.ne_empty (PackingMass.eq_empty_of_isOpen_disjoint_of_null_sdiff
    (packing_null_complement_of_mass_saturation P hclosed hreg hdisj hsub μ
      hSfinite htriple hmass) hU hUS hgap)

end GeneralPacking

/-- A finite Jordan packing with total weighted mass one fills the square.
Triple-contact finiteness is proved geometrically, not assumed here. -/
theorem jordan_packing_covers_unitSquare_of_mass_one {ι : Type*} [Fintype ι]
    (P : ι → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hsub : ∀ i, P i ⊆ unitSquare)
    (hmass : ∑ i, weightedMass volume (P i) = 1) : (⋃ i, P i) = unitSquare := by
  apply packing_iUnion_eq_of_mass_saturation P (fun i => (hP i).isClosed)
    (fun i => (hP i).closure_interior) hdis hsub volume closure_interior_unitSquare
  · simp only [volume_unitSquare, ENNReal.one_ne_top, ne_eq, not_false_eq_true]
  · exact (jordan_regions_tripleContactSet_finite P hP hdis).measure_zero volume
  · rw [volume_unitSquare, hmass]

/-- Four newly positioned congruent copies of the original four pieces cover
the square whenever they fit and their interiors are disjoint. -/
theorem SquareDissection.congruent_packing_covers (d : SquareDissection)
    (P : Fin 4 → Set Plane) (hP : ∀ i, IsJordanRegion (P i))
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hsub : ∀ i, P i ⊆ unitSquare)
    (hcongr : ∀ i, Congruent (P i) (d.piece i)) : (⋃ i, P i) = unitSquare :=
  jordan_packing_covers_unitSquare_of_mass_one P hP hdis hsub
    (d.sum_weightedMass_eq_one_of_congruent P hcongr)

/-- The same saturation holds for four copies of one fixed original piece,
as needed for the square-symmetry orbit argument. -/
theorem SquareDissection.congruent_piece_packing_covers (d : SquareDissection)
    (i : Fin 4) (P : Fin 4 → Set Plane) (hP : ∀ j, IsJordanRegion (P j))
    (hdis : Pairwise fun j k => Disjoint (interior (P j)) (interior (P k)))
    (hsub : ∀ j, P j ⊆ unitSquare)
    (hcongr : ∀ j, Congruent (P j) (d.piece i)) : (⋃ j, P j) = unitSquare :=
  jordan_packing_covers_unitSquare_of_mass_one P hP hdis hsub
    (d.sum_weightedMass_eq_one_of_congruent_piece i P hcongr)

/-- Such a four-copy packing cannot miss any nonempty subset of the square,
and therefore cannot miss a nonempty open center neighborhood. -/
theorem SquareDissection.congruent_piece_packing_no_gap (d : SquareDissection)
    (i : Fin 4) (P : Fin 4 → Set Plane) (hP : ∀ j, IsJordanRegion (P j))
    (hdis : Pairwise fun j k => Disjoint (interior (P j)) (interior (P k)))
    (hsub : ∀ j, P j ⊆ unitSquare)
    (hcongr : ∀ j, Congruent (P j) (d.piece i))
    {U : Set Plane} (hne : U.Nonempty) (hUS : U ⊆ unitSquare) :
    ¬ Disjoint U (⋃ j, P j) := by
  intro hgap
  obtain ⟨x, hx⟩ := hne
  apply disjoint_left.mp hgap hx
  rw [d.congruent_piece_packing_covers i P hP hdis hsub hcongr]
  exact hUS hx

end Puzzling139335
