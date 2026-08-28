import Wikipedia.NoExoticSixSphere.SmoothProjection
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Local transport between smoothly varying projection ranges

For projections `P` and `Q`, the operator `QP + (1-Q)(1-P)` intertwines them.
It is the identity when `P = Q`, hence it is invertible for `Q` near `P`.
This gives explicit smooth local identifications of the ranges and their
complements. No global trivialization is asserted.
-/

open scoped Manifold ContDiff Topology
open Function Set

namespace NoExoticSixSphere

section Algebra

variable {R : Type*} [Ring R]

/-- The standard intertwining operator between two projections. -/
def projectionIntertwiner (P Q : R) : R := Q * P + (1 - Q) * (1 - P)

/-- Transport at the reference projection is the identity. -/
theorem projectionIntertwiner_self (P : R) (hP : IsIdempotentElem P) :
    projectionIntertwiner P P = 1 := by
  unfold projectionIntertwiner
  rw [hP, hP.one_sub]
  simpa only [add_sub_assoc] using add_sub_cancel_left P 1

/-- The transport intertwines the two projections. -/
theorem projectionIntertwiner_intertwines (P Q : R)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    Q * projectionIntertwiner P Q = projectionIntertwiner P Q * P := by
  calc
    Q * projectionIntertwiner P Q = (Q * Q) * P + (Q * (1 - Q)) * (1 - P) := by
      simp only [projectionIntertwiner, mul_add, mul_assoc]
    _ = Q * P := by rw [hQ, hQ.mul_one_sub_self, zero_mul, add_zero]
    _ = Q * (P * P) + (1 - Q) * ((1 - P) * P) := by
      rw [hP, hP.one_sub_mul_self, mul_zero, add_zero]
    _ = projectionIntertwiner P Q * P := by
      simp only [projectionIntertwiner, add_mul, mul_assoc]

end Algebra

section Ranges

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- When invertible, the intertwiner identifies the actual ranges of the projections. -/
theorem projectionIntertwiner_map_range (P Q : F →L[ℝ] F)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) :
    Submodule.map (projectionIntertwiner P Q).toLinearMap P.range = Q.range := by
  have hcomm := projectionIntertwiner_intertwines P Q hP hQ
  have hsurj : Surjective (projectionIntertwiner P Q : F →L[ℝ] F) := by
    obtain ⟨r, hr⟩ := hR
    simpa only [← hr, ContinuousLinearEquiv.coe_coe] using r.surjective
  rw [← LinearMap.range_comp]
  have hlin : (projectionIntertwiner P Q).toLinearMap.comp P.toLinearMap =
      Q.toLinearMap.comp (projectionIntertwiner P Q).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap hcomm.symm
  rw [hlin]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)

/-- Package an invertible operator using its actual operator inverse. -/
noncomputable def invertibleOperatorEquiv (A : F →L[ℝ] F) (hA : A.IsInvertible) : F ≃L[ℝ] F where
  toLinearEquiv := { A.toLinearMap with
    invFun := A.inverse
    left_inv := hA.inverse_apply_self
    right_inv := hA.self_apply_inverse }
  continuous_toFun := A.continuous
  continuous_invFun := A.inverse.continuous

/-- Invertible transport restricts to an equivalence of the projection ranges. -/
noncomputable def projectionRangeEquiv (P Q : F →L[ℝ] F)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) : P.range ≃L[ℝ] Q.range :=
  (invertibleOperatorEquiv (projectionIntertwiner P Q) hR).ofSubmodules P.range Q.range
    (projectionIntertwiner_map_range P Q hP hQ hR)

/-- The range equivalence is given by the explicit ambient transport. -/
theorem projectionRangeEquiv_apply (P Q : F →L[ℝ] F)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) (v : P.range) :
    (projectionRangeEquiv P Q hP hQ hR v : F) = projectionIntertwiner P Q v := rfl

/-- The inverse range equivalence is the ambient inverse restricted to the range. -/
theorem projectionRangeEquiv_symm_apply (P Q : F →L[ℝ] F)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) (v : Q.range) :
    ((projectionRangeEquiv P Q hP hQ hR).symm v : F) =
      (projectionIntertwiner P Q).inverse v := rfl

/-- A projection fixes every vector in its range. -/
theorem projection_apply_range (P : F →L[ℝ] F) (hP : IsIdempotentElem P) (v : P.range) :
    P v = v := by
  obtain ⟨w, hw⟩ := v.property
  rw [← hw]
  exact congrArg (fun A : F →L[ℝ] F ↦ A w) hP

end Ranges

section Smoothness

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  (P : M → F →L[ℝ] F)

/-- The domain on which projection transport from `x₀` is invertible. -/
def projectionTransportDomain (x₀ : M) : Set M :=
  {x | (projectionIntertwiner (P x₀) (P x)).IsInvertible}

omit [CompleteSpace F] in
/-- The ambient transport family is smooth. -/
theorem contMDiff_projectionIntertwiner
    (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun x ↦ projectionIntertwiner (P x₀) (P x)) :=
  (hP.clm_comp contMDiff_const).add
    ((contMDiff_const.sub hP).clm_comp contMDiff_const)

/-- Invertible transport is an open condition. -/
theorem isOpen_projectionTransportDomain
    (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    IsOpen (projectionTransportDomain P x₀) := by
  have hi : IsOpen {A : F →L[ℝ] F | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  exact hi.preimage (contMDiff_projectionIntertwiner P hP x₀).continuous

omit [CompleteSpace F] [TopologicalSpace M] in
/-- The transport domain contains its center. -/
theorem mem_projectionTransportDomain (hP : ∀ x, IsIdempotentElem (P x)) (x₀ : M) :
    x₀ ∈ projectionTransportDomain P x₀ := by
  change (projectionIntertwiner (P x₀) (P x₀)).IsInvertible
  rw [projectionIntertwiner_self _ (hP x₀)]
  exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩

/-- The inverse ambient transport family is smooth throughout its open domain. -/
theorem contMDiffOn_projectionIntertwiner_inverse
    (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) ∞
      (fun x ↦ (projectionIntertwiner (P x₀) (P x)).inverse)
      (projectionTransportDomain P x₀) := by
  intro x hx
  have hi := hx.contDiffAt_map_inverse (n := ∞)
  exact (ContDiffAt.comp_contMDiffAt
    (f := fun y ↦ projectionIntertwiner (P x₀) (P y)) (x := x) hi
    (contMDiff_projectionIntertwiner P hP x₀).contMDiffAt).contMDiffWithinAt

end Smoothness

end NoExoticSixSphere
