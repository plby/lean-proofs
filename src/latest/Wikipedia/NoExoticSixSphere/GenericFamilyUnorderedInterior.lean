import Wikipedia.NoExoticSixSphere.DoublePointManifold
import Wikipedia.NoExoticSixSphere.FamilyDoublePointOpenLocus
import Wikipedia.NoExoticSixSphere.InvolutionFreeChart
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# Actual interior charts of the unordered generic double curve

The regular off-diagonal zero set carries the constructed one-dimensional
atlas. Its open inclusion into the actual closure transports those charts.
The swap quotient is locally an open embedding at distinct pairs, so these
charts descend to real-line charts whose whole source avoids diagonal orbits.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open GLOrthonormalization InvolutionQuotient

theorem exists_unordered_interior_chart (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hr : ∀ q : ℝ × (Vector 3 × Vector 3), q.2.1 ≠ q.2.2 →
      DoublePointPerturbation.baseDifference f q = 0 →
      Surjective (fderiv ℝ (DoublePointPerturbation.baseDifference f) q))
    (r : closure (doublePoints f)) (hne : r.val.2.1 ≠ r.val.2.2) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints f) ℝ,
      unorderedProj f r ∈ d.source ∧ Disjoint d.source (diagonalOrbits f) := by
  obtain ⟨a, ha⟩ := DoublePointPerturbation.exists_doublePoint_manifold f hf hr 1
    (by simp [GLOrthonormalization.Vector])
  let := a
  let u : doublePoints f := ⟨r.val, hne, closure_doublePoints_equal_image f hf r.property⟩
  let e := (chartAt (Vector 1) u).trans
    EuclideanTailCoordinates.scalar.symm.toHomeomorph.toOpenPartialHomeomorph
  have hue : u ∈ e.source := ⟨mem_chart_source _ _, mem_univ _⟩
  have hi := isOpenEmbedding_orderedInclusion f hf.continuous
  let c := e.lift_openEmbedding hi
  have hrc : r ∈ c.source := ⟨u, hue, rfl⟩
  have hfree : swapClosure f r ≠ r := fun he ↦ hne ((swapClosure_fixed_iff f r).mp he)
  obtain ⟨d, hrd, hde, hdis⟩ := exists_free_chart (swapClosure f)
    (swapClosure_involutive f) (swapClosure f).continuous r hfree c hrc
  refine ⟨d, hrd, ?_⟩
  rw [diagonalOrbits_eq_fixed]
  exact hdis

end NoExoticSixSphere.FamilyEmbedding
