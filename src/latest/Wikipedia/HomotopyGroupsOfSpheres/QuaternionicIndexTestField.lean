import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExponential
import Wikipedia.NoExoticSixSphere.OrthogonalIndexFieldLinear

/-!
# The rotating sine test field stays quaternionic-linear

Exponentiation, inverse, composition, and real scalar multiplication preserve
the quaternionic commutant. Consequently the actual orthogonal test field
restricts to a smooth endpoint-zero symplectic field, retaining linear
independence. This is a restriction of an explicit formula, not of a Bott
comparison theorem.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.IndexTestField

open NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

theorem orthogonal_transport_operator (K A : SkewSpace n) (t : ℝ) :
    (NoExoticSixSphere.OrthogonalIndexTransport.transport
      (toOrthogonalSkew n K) (toOrthogonalSkew n A) t).val =
      (Exponential.exp (t • ((-1 / 2 : ℝ) • K))).val.val.val.comp
        (A.val.comp ((Exponential.exp (t • ((-1 / 2 : ℝ) • K)))⁻¹).val.val.val) := by
  have he : NoExoticSixSphere.OrthogonalExponential.exp
      (t • ((-1 / 2 : ℝ) • toOrthogonalSkew n K)) =
        (Exponential.exp (t • ((-1 / 2 : ℝ) • K))).val := by
    change _ = NoExoticSixSphere.OrthogonalExponential.exp
      (toOrthogonalSkew n (t • ((-1 / 2 : ℝ) • K)))
    rw [map_smul, map_smul]
  unfold NoExoticSixSphere.OrthogonalIndexTransport.transport
    NoExoticSixSphere.SkewConjugation.conjugate
  rw [he]
  rfl

theorem transport_mem_commutant (K A : SkewSpace n) (t : ℝ) :
    (NoExoticSixSphere.OrthogonalIndexTransport.transport
      (toOrthogonalSkew n K) (toOrthogonalSkew n A) t).val ∈ commutant n := by
  rw [orthogonal_transport_operator]
  let g := Exponential.exp (t • ((-1 / 2 : ℝ) • K))
  exact (commutant n).mul_mem
    ((mem_symplecticSubgroup_iff n g.val).mp g.property)
    ((commutant n).mul_mem A.property.2
      ((mem_symplecticSubgroup_iff n g⁻¹.val).mp g⁻¹.property))

def field (K A : SkewSpace n) (t : ℝ) : SkewSpace n :=
  ⟨(NoExoticSixSphere.OrthogonalIndexTestField.field
    (toOrthogonalSkew n K) (toOrthogonalSkew n A) t).val,
    ⟨(NoExoticSixSphere.OrthogonalIndexTestField.field
      (toOrthogonalSkew n K) (toOrthogonalSkew n A) t).property,
      (commutant n).smul_mem (transport_mem_commutant K A t) (Real.sin (Real.pi * t))⟩⟩

theorem toOrthogonal_field (K A : SkewSpace n) (t : ℝ) :
    toOrthogonalSkew n (field K A t) = NoExoticSixSphere.OrthogonalIndexTestField.field
      (toOrthogonalSkew n K) (toOrthogonalSkew n A) t := Subtype.ext rfl

theorem field_zero (K A : SkewSpace n) : field K A 0 = 0 := by
  apply Subtype.ext
  exact congrArg (fun B : NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4) => B.val)
    (NoExoticSixSphere.OrthogonalIndexTestField.field_zero
    (toOrthogonalSkew n K) (toOrthogonalSkew n A))

theorem field_one (K A : SkewSpace n) : field K A 1 = 0 := by
  apply Subtype.ext
  exact congrArg (fun B : NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4) => B.val)
    (NoExoticSixSphere.OrthogonalIndexTestField.field_one
    (toOrthogonalSkew n K) (toOrthogonalSkew n A))

theorem contDiff_field (K A : SkewSpace n) : ContDiff ℝ ∞ (field K A) := by
  let L : NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4) →L[ℝ]
      (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
    (skewAdjoint.submodule ℝ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))).subtypeL
  have hL : ContDiff ℝ ∞ L :=
    finiteLinearMap_contDiff
      (E := NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4))
      (F := Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) L.toLinearMap
  have hval : ContDiff ℝ ∞ (fun t => (field K A t).val) := by
    change ContDiff ℝ ∞ (fun t => L (NoExoticSixSphere.OrthogonalIndexTestField.field
      (toOrthogonalSkew n K) (toOrthogonalSkew n A) t))
    exact hL.comp (NoExoticSixSphere.OrthogonalIndexTestField.contDiff_field
      (toOrthogonalSkew n K) (toOrthogonalSkew n A))
  have hp := (CayleyAtlas.contDiff_skewProjection (n := n)).comp hval
  simpa only [Function.comp_def, CayleyAtlas.skewProjection_coe] using hp

def fieldLinear (K : SkewSpace n) : SkewSpace n →ₗ[ℝ] (ℝ → SkewSpace n) where
  toFun := field K
  map_add' A B := by
    funext t
    apply Subtype.ext
    exact congrArg (fun f : ℝ → NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4) =>
      (f t).val) ((NoExoticSixSphere.OrthogonalIndexTestField.fieldLinear
        (toOrthogonalSkew n K)).map_add (toOrthogonalSkew n A) (toOrthogonalSkew n B))
  map_smul' r A := by
    funext t
    apply Subtype.ext
    exact congrArg (fun f : ℝ → NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4) =>
      (f t).val) ((NoExoticSixSphere.OrthogonalIndexTestField.fieldLinear
        (toOrthogonalSkew n K)).map_smul r (toOrthogonalSkew n A))

theorem fieldLinear_injective (K : SkewSpace n) : Function.Injective (fieldLinear K) := by
  intro A B h
  have he : NoExoticSixSphere.OrthogonalIndexTestField.fieldLinear (toOrthogonalSkew n K)
      (toOrthogonalSkew n A) =
      NoExoticSixSphere.OrthogonalIndexTestField.fieldLinear (toOrthogonalSkew n K)
        (toOrthogonalSkew n B) := by
    funext t
    apply Subtype.ext
    exact congrArg (fun f : ℝ → SkewSpace n => (f t).val) h
  have hab := NoExoticSixSphere.OrthogonalIndexTestField.fieldLinear_injective
    (toOrthogonalSkew n K) he
  exact Subtype.ext (congrArg
    (fun C : NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4) => C.val) hab)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.IndexTestField
