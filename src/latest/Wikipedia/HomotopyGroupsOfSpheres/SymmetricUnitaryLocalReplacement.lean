import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonTangent
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryOrthogonalEmbedding
import Wikipedia.NoExoticSixSphere.OrthogonalLocalSegment

/-!
# Local path replacement within the symmetric determinant-one space

Both relative logarithms are trace zero and reversible at the starting
matrix. Their linear interpolation has the same properties, so the actual
orthogonal replacement lifts to the original constrained matrix space.
-/

noncomputable section

open Set unitInterval
open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.LocalReplacement

open ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N] {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, SpecialSpace N))
  (h : ∀ p : I × X, (H (0, p.2), H p) ∈ ShortLog.domain N)

include h in
theorem groupCondition (p : I × X) :
    (orthogonalFamily H (0, p.2))⁻¹ * orthogonalFamily H p ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)).source := by
  change (specialOrthogonal (H (0, p.2)))⁻¹ * specialOrthogonal (H p) ∈ _
  rw [← ShortLog.orthogonal_relative]
  exact ComplexSkewMatrices.CompatibleLog.orthogonal_mem_source _ (h p)

def direction (s t : I) (x : X) : ReversibleDirection (H (0, x)) :=
  (1 - (s : ℝ)) • ⟨ShortLog.generator (H (0, x)) (H (t, x)),
    ShortLog.generator_mem_start (h (t, x))⟩ +
  (s : ℝ) • ((t : ℝ) • ⟨ShortLog.generator (H (0, x)) (H (1, x)),
    ShortLog.generator_mem_start (h (1, x))⟩)

theorem logs_toOrthogonal (p : I × X) :
    NoExoticSixSphere.OrthogonalExponential.LocalSegment.logs
      (orthogonalFamily H) (groupCondition H h) p =
      ComplexSkewMatrices.toOrthogonalSkew (ShortLog.generator (H (0, p.2)) (H p)) :=
  ShortLog.orthogonal_logarithm_eq (h p)

theorem direction_toOrthogonal (s t : I) (x : X) :
    ComplexSkewMatrices.toOrthogonalSkew (direction H h s t x).val =
      (1 - (s : ℝ)) • NoExoticSixSphere.OrthogonalExponential.LocalSegment.logs
        (orthogonalFamily H) (groupCondition H h) (t, x) +
      (s : ℝ) • ((t : ℝ) • NoExoticSixSphere.OrthogonalExponential.LocalSegment.logs
        (orthogonalFamily H) (groupCondition H h) (1, x)) := by
  change ComplexSkewMatrices.toOrthogonalSkew
    ((1 - (s : ℝ)) • ShortLog.generator (H (0, x)) (H (t, x)) +
      (s : ℝ) • ((t : ℝ) • ShortLog.generator (H (0, x)) (H (1, x)))) = _
  rw [map_add, map_smul, map_smul, map_smul,
    logs_toOrthogonal H h, logs_toOrthogonal H h]

def point (q : I × (I × X)) : SpecialSpace N :=
  reversibleStep (H (0, q.2.2)) (direction H h q.1 q.2.1 q.2.2).val
    (direction H h q.1 q.2.1 q.2.2).property.1
    (direction H h q.1 q.2.1 q.2.2).property.2 1

theorem point_toOrthogonal (q : I × (I × X)) :
    specialOrthogonal (point H h q) =
      NoExoticSixSphere.OrthogonalExponential.LocalSegment.replacement
        (orthogonalFamily H) (groupCondition H h) q := by
  change orthogonal ((H (0, q.2.2)).val.val *
    ComplexSkewMatrices.exponential ((1 : ℝ) • (direction H h q.1 q.2.1 q.2.2).val)) = _
  rw [map_mul, ComplexSkewMatrices.orthogonal_exponential, one_smul, direction_toOrthogonal]
  rfl

def replacement : C(I × (I × X), SpecialSpace N) :=
  ⟨point H h, continuous_of_specialOrthogonal
    ((NoExoticSixSphere.OrthogonalExponential.LocalSegment.replacement
      (orthogonalFamily H) (groupCondition H h)).continuous.congr
      (fun q ↦ (point_toOrthogonal H h q).symm))⟩

theorem replacement_toOrthogonal (q : I × (I × X)) :
    specialOrthogonal (replacement H h q) =
      NoExoticSixSphere.OrthogonalExponential.LocalSegment.replacement
        (orthogonalFamily H) (groupCondition H h) q := point_toOrthogonal H h q

theorem replacement_zero (p : I × X) : replacement H h (0, p) = H p := by
  apply specialOrthogonal_injective
  rw [replacement_toOrthogonal,
    NoExoticSixSphere.OrthogonalExponential.LocalSegment.replacement_zero]
  rfl

theorem replacement_time_zero (s : I) (x : X) : replacement H h (s, (0, x)) = H (0, x) := by
  apply specialOrthogonal_injective
  rw [replacement_toOrthogonal,
    NoExoticSixSphere.OrthogonalExponential.LocalSegment.replacement_time_zero]
  rfl

theorem replacement_time_one (s : I) (x : X) : replacement H h (s, (1, x)) = H (1, x) := by
  apply specialOrthogonal_injective
  rw [replacement_toOrthogonal,
    NoExoticSixSphere.OrthogonalExponential.LocalSegment.replacement_time_one]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.LocalReplacement
