import Wikipedia.NoExoticSixSphere.GenericFamilyUnorderedAtlas
import Wikipedia.NoExoticSixSphere.GenericFamilySingularBoundary
import Wikipedia.NoExoticSixSphere.CutCurveIntervalClosures

/-!
# Actual finite cuts of the compact unordered generic-family curve

The constructed global quotient atlas gives a finite cover by compact interval
neighborhoods. Their actual endpoint set contains the diagonal boundary.
Components of its complement are open and have nondegenerate closed-interval
closures in the original space, with the actual coordinate maps retained.

The compact container remains explicit. Endpoint incidence, finiteness of the
edge set, and evenness of the boundary count are not asserted here.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open GLOrthonormalization OperatorRank CurveDecomposition

theorem exists_finite_cuts_with_interval_components (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun p : ℝ × Vector 3 ↦ fderiv ℝ (f p.1) p.2))
    (hoff : ∀ q : ℝ × (Vector 3 × Vector 3), q.2.1 ≠ q.2.2 →
      DoublePointPerturbation.baseDifference f q = 0 →
      Surjective (fderiv ℝ (DoublePointPerturbation.baseDifference f) q))
    {K : Set (ℝ × (Vector 3 × Vector 3))} (hK : IsCompact K)
    (hbound : doublePoints f ⊆ K) :
    ∃ N : UnorderedClosedDoublePoints f → IntervalNeighborhood (UnorderedClosedDoublePoints f),
    ∃ t : Finset (UnorderedClosedDoublePoints f),
      (∀ q, (N q).chart = unorderedChart f hf hreg hoff q) ∧
      univ ⊆ ⋃ i ∈ t, (N i).openSet ∧
      (cutSet t N).Finite ∧ diagonalOrbits f ⊆ cutSet t N ∧
      ∀ x : {q : UnorderedClosedDoublePoints f // q ∉ cutSet t N},
        IsOpen (cutComponent (cutSet t N) x) ∧
        ∃ i ∈ t, ∃ a b : ℝ, a < b ∧
          ∃ h : closure (cutComponent (cutSet t N) x) ≃ₜ Icc a b,
            ∀ y, (h y).val = CurveChart.realCoordinate (N i).chart y.val := by
  let := t2Space_unordered f
  let := compactSpace_unordered_of_compact_container f hK hbound
  let := unorderedChartedSpace f hf hreg hoff
  let := chartedSpace_locallyConnected (X := UnorderedClosedDoublePoints f)
  obtain ⟨N, t, hN, hcov⟩ := exists_finite_interval_cover (unorderedChart f hf hreg hoff)
    (unorderedChart_mem_source f hf hreg hoff)
  have hB : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      ((N i).chart y).val = 0 ↔ y ∈ diagonalOrbits f := by
    intro i hi
    rw [hN i]
    exact unorderedChart_zero_iff f hf hreg hoff i
  refine ⟨N, t, hN, hcov, finite_cutSet t N,
    boundary_subset_cutSet t N hcov (diagonalOrbits f) hB, ?_⟩
  intro x
  exact ⟨isOpen_cutComponent (finite_cutSet t N).isClosed x,
    exists_cutComponent_interval t N hcov x⟩

end NoExoticSixSphere.FamilyEmbedding
