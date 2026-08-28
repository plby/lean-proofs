import Wikipedia.HopfProblem.DegreeCollapseSurgeryExteriorDeformation
import Wikipedia.HopfProblem.DegreeCollapseIntegralEmbeddingRangeHomology
import Wikipedia.NoExoticSixSphere.RelativeHomologyMapComparison

/-!
# The actual closed exterior pair and the open core-complement pair

The existing radial deformation identifies the original exterior with the
whole core complement. Applying the actual pair sequence to the identity
ambient map proves that enlarging the relative subspace induces a homology
isomorphism in every degree. The map is the original map of pairs.
-/

noncomputable section

open Function Set ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorRetraction

open Wikipedia.SmoothSixDPoincare SingularMayerVietoris PeriodTorusHigherHomology
open NoExoticSixSphere.RelativeSingularHomology

variable {E F R X Y : Type} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

omit [NormedSpace ℝ F] in
theorem exteriorRange_subset_complement : range d.oldExterior ⊆ d.OldComplement := by
  rintro x ⟨r, rfl⟩
  exact d.oldExterior_avoids r

def exteriorRangeToComplement : C(range d.oldExterior, d.OldComplement) :=
  restrictedMap (ContinuousMap.id X) (exteriorRange_subset_complement d)

omit [NormedSpace ℝ F] in
theorem exteriorRangeToComplement_rangeMap :
    (exteriorRangeToComplement d).comp
      (IntegralEmbeddingRange.rangeMap ⟨d.oldExterior, d.oldExterior_closed.continuous⟩) =
        exteriorInclusion d := rfl

theorem exteriorRangeToComplement_homology_bijective (k : ℕ) :
    Bijective (singularHomologyMap (exteriorRangeToComplement d) k) := by
  let j : C(R, X) := ⟨d.oldExterior, d.oldExterior_closed.continuous⟩
  have hr := IntegralEmbeddingRange.rangeMap_homology_bijective j
    d.oldExterior_closed.isEmbedding k
  have he : Bijective ((singularHomologyMap (exteriorRangeToComplement d) k).comp
      (singularHomologyMap (IntegralEmbeddingRange.rangeMap j) k)) := by
    rw [← singularHomologyMap_comp]
    exact (homotopyEquivHomologyEquiv (homotopyEquiv d) k).bijective
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hr.2 x
    obtain ⟨b, rfl⟩ := hr.2 y
    exact congrArg (singularHomologyMap (IntegralEmbeddingRange.rangeMap j) k) (he.1 hxy)
  · intro y
    obtain ⟨a, ha⟩ := he.2 y
    exact ⟨singularHomologyMap (IntegralEmbeddingRange.rangeMap j) k a, ha⟩

abbrev exteriorToComplement (k : ℕ) :
    Homology (range d.oldExterior) k →ₗ[ℤ] Homology d.OldComplement k :=
  map (ContinuousMap.id X) (exteriorRange_subset_complement d) k

theorem exteriorToComplement_bijective (k : ℕ) :
    Bijective (exteriorToComplement d k) := by
  apply map_bijective_of_absolute (ContinuousMap.id X) (exteriorRange_subset_complement d)
  · intro n
    rw [singularHomologyMap_id]
    exact bijective_id
  · exact exteriorRangeToComplement_homology_bijective d

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorRetraction
