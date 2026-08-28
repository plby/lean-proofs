import Wikipedia.NoExoticSixSphere.CompactHalfLineBoundary
import Wikipedia.NoExoticSixSphere.GenericFamilyUnorderedAtlas
import Wikipedia.NoExoticSixSphere.GenericFamilySingularBoundary

/-!
# Even singularity count for the actual compact generic-family double curve

The original unordered quotient is compact when the actual ordered double
points lie in a supplied compact container. Its genuine half-line atlas then
has finite even boundary. The proved bijection with the original singular
parameters transfers the count, without treating a model singularity as an
original parameter or counting two ordered copies of a boundary point.

The compact-container and Euclidean genericity hypotheses remain explicit.
Endpoint-relative localization on the original manifold is not asserted.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open GLOrthonormalization OperatorRank CurveDecomposition

variable (f : ℝ → Vector 3 → Vector 6) (hf : ContDiff ℝ ∞ (uncurry f))
  (hreg : RegularThreeSix (fun p : ℝ × Vector 3 ↦ fderiv ℝ (f p.1) p.2))
  (hoff : ∀ q : ℝ × (Vector 3 × Vector 3), q.2.1 ≠ q.2.2 →
    DoublePointPerturbation.baseDifference f q = 0 →
    Surjective (fderiv ℝ (DoublePointPerturbation.baseDifference f) q))

include hf hreg hoff

theorem finite_even_diagonalOrbits {K : Set (ℝ × (Vector 3 × Vector 3))}
    (hK : IsCompact K) (hbound : doublePoints f ⊆ K) :
    (diagonalOrbits f).Finite ∧ Even (diagonalOrbits f).ncard := by
  let := t2Space_unordered f
  let := compactSpace_unordered_of_compact_container f hK hbound
  exact finite_even_boundary_of_compact_atlas (diagonalOrbits f)
    (unorderedChart f hf hreg hoff) (unorderedChart_mem_source f hf hreg hoff)
    (unorderedChart_zero_iff f hf hreg hoff)

theorem finite_even_singular_parameters {K : Set (ℝ × (Vector 3 × Vector 3))}
    (hK : IsCompact K) (hbound : doublePoints f ⊆ K) :
    {p : ℝ × Vector 3 | ¬ Injective (fderiv ℝ (f p.1) p.2)}.Finite ∧
      Even (Nat.card {p : ℝ × Vector 3 | ¬ Injective (fderiv ℝ (f p.1) p.2)}) := by
  have h := finite_even_diagonalOrbits f hf hreg hoff hK hbound
  let := h.1.to_subtype
  have hfin : Finite {p : ℝ × Vector 3 | ¬ Injective (fderiv ℝ (f p.1) p.2)} :=
    Finite.of_equiv (diagonalOrbits f) (singularBoundaryEquiv f hf hreg).symm
  refine ⟨finite_coe_iff.mp hfin, ?_⟩
  rw [singularBoundary_card f hf hreg, Nat.card_coe_set_eq]
  exact h.2

end NoExoticSixSphere.FamilyEmbedding
