import Wikipedia.NoExoticSixSphere.RectangularDeformationHomotopy
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates

/-!
# Normalizing one block without changing the other columns

Rectangular Gram--Schmidt interpolation stays in the original range. Thus
appending an injective operator with disjoint range gives a homotopy through
injective combined operators, with the appended columns fixed throughout.
-/

noncomputable section

open Function unitInterval

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel

namespace Stiefel.RectangularDeformation

theorem range_interpolation_le {X : Type*} {N n : ℕ}
    (A : X → Vector n →L[ℝ] Vector N) (hi : ∀ x, Injective (A x)) (p : I × X) :
    (interpolation A p).range ≤ (A p.2).range := by
  rintro _ ⟨v, rfl⟩
  change (1 - (p.1 : ℝ)) • A p.2 v +
    (p.1 : ℝ) • Orthonormalization.operator A p.2 v ∈ (A p.2).range
  apply (A p.2).range.add_mem
  · exact (A p.2).range.smul_mem _ ⟨v, rfl⟩
  · apply (A p.2).range.smul_mem
    rw [← Orthonormalization.operator_range A p.2 (hi p.2)]
    exact ⟨v, rfl⟩

end Stiefel.RectangularDeformation

namespace OperatorSum

theorem homotopic_normalize_left {X : Type*} [TopologicalSpace X] {N n d : ℕ}
    (A : X → Vector n →L[ℝ] Vector N) (B : X → Vector d →L[ℝ] Vector N)
    (hA : Continuous A) (hB : Continuous B)
    (hiA : ∀ x, Injective (A x)) (hiB : ∀ x, Injective (B x))
    (hr : ∀ x, Disjoint (A x).range (B x).range)
    (F G : C(X, Monomorphism.Space N (n + d)))
    (hF : ∀ x, (F x).val = operator (A x) (B x))
    (hG : ∀ x, (G x).val = operator (Orthonormalization.operator A x) (B x)) :
    F.Homotopic G := by
  refine ⟨{
    toFun := fun p ↦ ⟨operator (RectangularDeformation.interpolation A p) (B p.2),
      injective_operator _ _ (RectangularDeformation.injective_interpolation A hiA p)
        (hiB p.2) ((hr p.2).mono_left
          (RectangularDeformation.range_interpolation_le A hiA p))⟩
    continuous_toFun := (continuous_operator _ _
      (RectangularDeformation.continuous_interpolation A hiA hA)
      (hB.comp continuous_snd)).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    change operator (RectangularDeformation.interpolation A (0, x)) (B x) = (F x).val
    rw [RectangularDeformation.interpolation_zero, hF]
  · intro x
    apply Subtype.ext
    change operator (RectangularDeformation.interpolation A (1, x)) (B x) = (G x).val
    rw [RectangularDeformation.interpolation_one, hG]

end OperatorSum

end NoExoticSixSphere
