import Wikipedia.NoExoticSixSphere.GenericFamilyUnorderedInterior
import Wikipedia.NoExoticSixSphere.GenericFamilyUnorderedBoundary

/-!
# Real-line and half-line charts cover the actual unordered double curve

The full spatial-jet regularity supplies the boundary charts and the separate
off-diagonal regularity supplies the interior charts. Together they cover
every point of the genuine quotient, with the diagonal orbit set retained
as the exact zero-coordinate boundary in each boundary chart.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open GLOrthonormalization InvolutionQuotient OperatorRank

theorem unordered_local_models (f : ℝ → Vector 3 → Vector 6)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun p : ℝ × Vector 3 ↦ fderiv ℝ (f p.1) p.2))
    (hoff : ∀ q : ℝ × (Vector 3 × Vector 3), q.2.1 ≠ q.2.2 →
      DoublePointPerturbation.baseDifference f q = 0 →
      Surjective (fderiv ℝ (DoublePointPerturbation.baseDifference f) q))
    (q : UnorderedClosedDoublePoints f) :
    (∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints f) ℝ,
      q ∈ d.source ∧ Disjoint d.source (diagonalOrbits f)) ∨
    (∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints f) HalfLine,
      q ∈ d.source ∧ d q = ⟨0, le_rfl⟩ ∧
      ∀ y ∈ d.source, (d y).val = 0 ↔ y ∈ diagonalOrbits f) := by
  by_cases hq : q ∈ diagonalOrbits f
  · exact Or.inr (exists_unordered_boundary_chart f hf hreg q hq)
  · obtain ⟨r, rfl⟩ := (isOpenQuotientMap_unorderedProj f).surjective q
    have hne : r.val.2.1 ≠ r.val.2.2 :=
      fun he ↦ hq ((mem_diagonalOrbits_iff f r).mpr he)
    exact Or.inl (exists_unordered_interior_chart f hf hoff r hne)

end NoExoticSixSphere.FamilyEmbedding
