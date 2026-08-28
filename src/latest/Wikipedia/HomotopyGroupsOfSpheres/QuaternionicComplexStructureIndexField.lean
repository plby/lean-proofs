import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureAntipodalIndex
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureExponential
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicIndexTestField

/-!
# Rotating negative test fields remain tangent to complex structures

Parallel conjugation transports both the complex structure and its
anticommuting direction by the same symplectic operator. Multiplication by
the endpoint-zero sine factor preserves the anticommutation relation.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open NoExoticSixSphere.GLOrthonormalization Exponential

variable {n : ℕ}

private theorem sandwich_anticommute {A : Type*} [Ring A] (g h J K : A)
    (hgi : h * g = 1) (hJK : J * K = -(K * J)) :
    (g * (J * h)) * (g * (K * h)) = -((g * (K * h)) * (g * (J * h))) := by
  have hm (X Y : A) : (g * (X * h)) * (g * (Y * h)) = g * ((X * Y) * h) := by
    calc
      _ = g * (X * ((h * g) * (Y * h))) := by simp only [mul_assoc]
      _ = _ := by rw [hgi, one_mul]; simp only [mul_assoc]
  rw [hm, hm, hJK, neg_mul, mul_neg]

theorem conjugateSkew_anticommute (g : symplecticSubgroup n) (J : Space n) (A : SkewSpace n)
    (hJA : J.val.val * A.val = -(A.val * J.val.val)) :
    (conjugate g J).val.val * (conjugateSkew g A).val =
      -((conjugateSkew g A).val * (conjugate g J).val.val) := by
  have hgi : (g⁻¹).val.val.val * g.val.val.val = 1 :=
    congrArg (fun a : symplecticSubgroup n ↦ a.val.val.val) (inv_mul_cancel g)
  exact sandwich_anticommute g.val.val.val (g⁻¹).val.val.val J.val.val A.val hgi hJA

theorem exponentialCurve_eq_conjugate (J : Space n) (K : AntiSkewSpace J) (t : ℝ) :
    exponentialCurve J K t =
      conjugate (exp (t • ((-1 / 2 : ℝ) • antiSkewToSkew J K))) J := by
  unfold exponentialCurve exponentialStep
  apply congrArg (fun L : SkewSpace n ↦ conjugate (exp L) J)
  rw [map_smul, map_smul]
  module

theorem indexField_eq_smul_conjugate (K A : SkewSpace n) (t : ℝ) :
    IndexTestField.field K A t = Real.sin (Real.pi * t) •
      conjugateSkew (exp (t • ((-1 / 2 : ℝ) • K))) A := by
  apply Subtype.ext
  change Real.sin (Real.pi * t) •
      (NoExoticSixSphere.OrthogonalIndexTransport.transport
        (toOrthogonalSkew n K) (toOrthogonalSkew n A) t).val = _
  rw [IndexTestField.orthogonal_transport_operator]
  rfl

theorem indexField_mem_antiSkew (J : Space n) (K A : AntiSkewSpace J) (t : ℝ) :
    (IndexTestField.field (antiSkewToSkew J K) (antiSkewToSkew J A) t).val ∈
      antiSkewSubmodule (exponentialCurve J K t) := by
  rw [exponentialCurve_eq_conjugate, indexField_eq_smul_conjugate, Submodule.coe_smul]
  apply Submodule.smul_mem
  exact ⟨(conjugateSkew _ (antiSkewToSkew J A)).property,
    conjugateSkew_anticommute _ J (antiSkewToSkew J A) A.property.2⟩

def indexDirection (J : Space n) (K A : AntiSkewSpace J) (t : ℝ) :
    AntiSkewSpace (exponentialCurve J K t) :=
  ⟨(IndexTestField.field (antiSkewToSkew J K) (antiSkewToSkew J A) t).val,
    indexField_mem_antiSkew J K A t⟩

theorem indexDirection_toSkew (J : Space n) (K A : AntiSkewSpace J) (t : ℝ) :
    antiSkewToSkew (exponentialCurve J K t) (indexDirection J K A t) =
      IndexTestField.field (antiSkewToSkew J K) (antiSkewToSkew J A) t := rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
