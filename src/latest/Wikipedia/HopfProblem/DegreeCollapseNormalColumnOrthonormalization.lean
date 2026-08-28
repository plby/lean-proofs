import Wikipedia.NoExoticSixSphere.RectangularDeformationHomotopy
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates

/-!
# Normal-column Gram--Schmidt preserves the actual combined frame homotopy

The existing rectangular interpolation retains the original normal range.
Appending a disjoint injective tangent operator therefore remains injective.
The resulting homotopy acts only on normal columns and leaves the tangent
columns unchanged; it does not discard the later geometric source twist.
-/

noncomputable section

open Function unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.NormalColumnOrthonormalization

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {X : Type*} {N n d : ℕ}

theorem range_interpolation_le (A : X → Vector n →L[ℝ] Vector N)
    (hi : ∀ x, Injective (A x)) (p : I × X) :
    (RectangularDeformation.interpolation A p).range ≤ (A p.2).range := by
  rintro _ ⟨v, rfl⟩
  change (1 - (p.1 : ℝ)) • A p.2 v +
    (p.1 : ℝ) • Orthonormalization.operator A p.2 v ∈ (A p.2).range
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ ⟨v, rfl⟩
  · apply Submodule.smul_mem
    rw [← Orthonormalization.operator_range A p.2 (hi p.2)]
    exact ⟨v, rfl⟩

theorem range_interpolation (A : X → Vector n →L[ℝ] Vector N)
    (hi : ∀ x, Injective (A x)) (p : I × X) :
    (RectangularDeformation.interpolation A p).range = (A p.2).range := by
  apply Submodule.eq_of_le_of_finrank_eq (range_interpolation_le A hi p)
  rw [LinearMap.finrank_range_of_inj (RectangularDeformation.injective_interpolation A hi p),
    LinearMap.finrank_range_of_inj (hi p.2)]

theorem combined_interpolation_injective
    (A : X → Vector n →L[ℝ] Vector N) (B : X → Vector d →L[ℝ] Vector N)
    (hiA : ∀ x, Injective (A x)) (hiB : ∀ x, Injective (B x))
    (hd : ∀ x, Disjoint (A x).range (B x).range) (p : I × X) :
    Injective (OperatorSum.operator (RectangularDeformation.interpolation A p) (B p.2)) := by
  apply OperatorSum.injective_operator _ _
    (RectangularDeformation.injective_interpolation A hiA p) (hiB p.2)
  rw [range_interpolation A hiA p]
  exact hd p.2

theorem normalized_combined_injective
    (A : X → Vector n →L[ℝ] Vector N) (B : X → Vector d →L[ℝ] Vector N)
    (hiA : ∀ x, Injective (A x)) (hiB : ∀ x, Injective (B x))
    (hd : ∀ x, Disjoint (A x).range (B x).range) (x : X) :
    Injective (OperatorSum.operator (Orthonormalization.operator A x) (B x)) := by
  have h := combined_interpolation_injective A B hiA hiB hd (1, x)
  simpa only [RectangularDeformation.interpolation_one] using h

variable [TopologicalSpace X]
  (A : X → Vector n →L[ℝ] Vector N) (B : X → Vector d →L[ℝ] Vector N)
  (hA : Continuous A) (hB : Continuous B)
  (hiA : ∀ x, Injective (A x)) (hiB : ∀ x, Injective (B x))
  (hd : ∀ x, Disjoint (A x).range (B x).range)

def rawMap : C(X, Monomorphism.Space N (n + d)) where
  toFun x := ⟨OperatorSum.operator (A x) (B x),
    OperatorSum.injective_operator _ _ (hiA x) (hiB x) (hd x)⟩
  continuous_toFun := (OperatorSum.continuous_operator A B hA hB).subtype_mk _

def normalizedMap : C(X, Monomorphism.Space N (n + d)) where
  toFun x := ⟨OperatorSum.operator (Orthonormalization.operator A x) (B x),
    normalized_combined_injective A B hiA hiB hd x⟩
  continuous_toFun := (OperatorSum.continuous_operator (Orthonormalization.operator A) B
    (continuous_subtype_val.comp (Orthonormalization.continuous_frame A hiA hA)) hB).subtype_mk _

def homotopy :
    (rawMap A B hA hB hiA hiB hd).Homotopy (normalizedMap A B hA hB hiA hiB hd) where
  toFun p := ⟨OperatorSum.operator (RectangularDeformation.interpolation A p) (B p.2),
    combined_interpolation_injective A B hiA hiB hd p⟩
  continuous_toFun := (OperatorSum.continuous_operator (RectangularDeformation.interpolation A)
    (B ∘ Prod.snd) (RectangularDeformation.continuous_interpolation A hiA hA)
    (hB.comp continuous_snd)).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change OperatorSum.operator (RectangularDeformation.interpolation A (0, x)) (B x) =
      OperatorSum.operator (A x) (B x)
    rw [RectangularDeformation.interpolation_zero]
  map_one_left x := by
    apply Subtype.ext
    change OperatorSum.operator (RectangularDeformation.interpolation A (1, x)) (B x) =
      OperatorSum.operator (Orthonormalization.operator A x) (B x)
    rw [RectangularDeformation.interpolation_one]

end Wikipedia.HopfProblem.DegreeCollapse.NormalColumnOrthonormalization
