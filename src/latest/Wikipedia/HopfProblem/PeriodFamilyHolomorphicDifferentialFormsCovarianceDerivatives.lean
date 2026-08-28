import Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialFormsCovarianceBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupExtensionDerivative
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Native derivatives of the local lifted triangle action

The original open upper-half-plane coordinate and original complex period
vectors are retained. The derivative of the actual lifted action includes
the base-dependent right-block correction. Its scalar base derivative is
exactly the restriction of the original full upper-half-plane derivative.
-/

noncomputable section

open Matrix UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance

open SpecialPeriods HolomorphicDifferentialForms
open SpecialPeriods.Threefold.HolomorphicForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] coverChartedSpace cover_isManifold

variable (U : TopologicalSpace.Opens ℍ)

/-- The scalar derivative of the actual restricted base action. -/
def baseDerivative (g : TriangleGroup) (hg : Preserves U g) (z : U) : ℂ :=
  mfderiv I₁ I₁ (baseMap U g hg) z (1 : ℂ)

/-- Entrywise derivatives of the actual restricted period right block. -/
def rightBlockDerivative (g : TriangleGroup) (z : U) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => mfderiv I₁ I₁ (fun w : U => rightBlock U g w i k) z (1 : ℂ)

private theorem scalar_linear_apply (L : ℂ →L[ℂ] ℂ) (c : ℂ) : L c = L 1 * c := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using L.map_smul c (1 : ℂ)

/-- The native derivative of the actual open-submanifold action agrees with
the derivative of the original full action under the identity inclusions. -/
theorem baseMap_mfderiv_eq_extension (g : TriangleGroup) (hg : Preserves U g) (z : U) :
    mfderiv I₁ I₁ (baseMap U g hg) z =
      mfderiv I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z.val := by
  let Lr : ℂ →L[ℂ] ℂ := mfderiv I₁ I₁ (baseMap U g hg) z
  let Lb : ℂ →L[ℂ] ℂ :=
    mfderiv I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z.val
  have hr : HasMFDerivAt I₁ I₁ (baseMap U g hg) z Lr :=
    ((baseMap_holomorphic U g hg).mdifferentiable (by simp) z).hasMFDerivAt
  have hb : HasMFDerivAt I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z.val Lb :=
    ((triangleGeometricRepresentation_holomorphic g).mdifferentiable
      (by simp) z.val).hasMFDerivAt
  have hrestricted := (hasMFDerivAt_openSubtypeVal U (baseMap U g hg z)).comp z hr
  have hfull := hb.comp z (hasMFDerivAt_openSubtypeVal U z)
  have he : (ContinuousLinearMap.id ℂ ℂ).comp Lr =
      Lb.comp (ContinuousLinearMap.id ℂ ℂ) :=
    hrestricted.mfderiv.symm.trans hfull.mfderiv
  change Lr = Lb
  simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using he

/-- Restriction does not change the actual scalar base Jacobian. -/
theorem baseDerivative_eq_extension (g : TriangleGroup) (hg : Preserves U g) (z : U) :
    baseDerivative U g hg z = RegularCover.groupBaseDerivativeExtension g z.val :=
  congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (baseMap_mfderiv_eq_extension U g hg z)

theorem baseDerivative_holomorphic (g : TriangleGroup) (hg : Preserves U g) :
    ContMDiff I₁ I₁ ω (baseDerivative U g hg) := by
  have he : baseDerivative U g hg =
      fun z : U => RegularCover.groupBaseDerivativeExtension g z.val :=
    funext (baseDerivative_eq_extension U g hg)
  rw [he]
  exact (RegularCover.groupBaseDerivativeExtension_holomorphic g).comp contMDiff_subtype_val

theorem baseDerivative_ne_zero (g : TriangleGroup) (hg : Preserves U g) (z : U) :
    baseDerivative U g hg z ≠ 0 := by
  rw [baseDerivative_eq_extension]
  exact RegularCover.groupBaseDerivativeExtension_ne_zero g z.val

/-- Matrix-entry derivatives are those of the full original period cocycle. -/
theorem rightBlockDerivative_apply_eq_extension (g : TriangleGroup) (z : U)
    (i k : Fin 2) :
    rightBlockDerivative U g z i k =
      mfderiv I₁ I₁ (fun w : ℍ => RegularCover.groupRightBlockExtension g w i k)
        z.val (1 : ℂ) := by
  have hg := (RegularCover.groupRightBlockExtension_entry_holomorphic g i k).mdifferentiable
    (by simp) z.val
  have hf := (contMDiff_subtype_val (I := I₁) (n := ω) (U := U)).mdifferentiable
    (by simp) z
  have h := mfderiv_comp_apply z
    (g := fun w : ℍ => RegularCover.groupRightBlockExtension g w i k)
    (f := (Subtype.val : U → ℍ)) hg hf (1 : ℂ)
  rw [mfderiv_openSubtypeVal] at h
  exact h.trans rfl

theorem rightBlockDerivative_entry_holomorphic (g : TriangleGroup) (i k : Fin 2) :
    ContMDiff I₁ I₁ ω (fun z : U => rightBlockDerivative U g z i k) :=
  FlatDerivative.mfderiv_apply_one_holomorphic_of_constant_charts
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun z : U => rightBlock U g z i k) (rightBlock_entry_holomorphic U g i k)

/-- The derivative of the actual lifted action, including every term caused
by the base dependence of its original right-block matrix. -/
theorem complexLift_mfderiv_apply (g : TriangleGroup) (hg : Preserves U g)
    (x : Cover U) (v : Model) :
    mfderiv IF IF (complexLift U g hg) x v =
      (baseDerivative U g hg x.1 * v.1,
        rightBlock U g x.1 *ᵥ v.2 +
          v.1 • (rightBlockDerivative U g x.1 *ᵥ x.2)) := by
  rw [modelWithCornersSelf_prod]
  have hd : HasMFDerivAt ((I₁).prod I₂) ((I₁).prod I₂) (complexLift U g hg) x
      (mfderiv ((I₁).prod I₂) ((I₁).prod I₂) (complexLift U g hg) x) := by
    rw [← modelWithCornersSelf_prod]
    exact ((complexLift_holomorphic U g hg).mdifferentiable (by simp) x).hasMFDerivAt
  have hf : HasMFDerivAt ((I₁).prod I₂) I₁ (fun y : Cover U => y.1) x
      (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂) := hasMFDerivAt_fst x
  have hs : HasMFDerivAt ((I₁).prod I₂) I₂ (fun y : Cover U => y.2) x
      (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) := hasMFDerivAt_snd x
  have hfo : HasMFDerivAt ((I₁).prod I₂) I₁ (fun y : Cover U => y.1)
      (complexLift U g hg x) (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂) :=
    hasMFDerivAt_fst (complexLift U g hg x)
  have hso : HasMFDerivAt ((I₁).prod I₂) I₂ (fun y : Cover U => y.2)
      (complexLift U g hg x) (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) :=
    hasMFDerivAt_snd (complexLift U g hg x)
  apply Prod.ext
  · have hb := ((baseMap_holomorphic U g hg).mdifferentiable (by simp) x.1).hasMFDerivAt
    have heq := (hfo.comp x hd).mfderiv.symm.trans (hb.comp x hf).mfderiv
    have heqv := congrArg (fun A : Model →L[ℂ] ℂ => A v) heq
    change (mfderiv ((I₁).prod I₂) ((I₁).prod I₂) (complexLift U g hg) x v).1 =
      mfderiv I₁ I₁ (baseMap U g hg) x.1 v.1 at heqv
    exact heqv.trans (scalar_linear_apply _ _)
  · funext i
    let L (k : Fin 2) : ℂ →L[ℂ] ℂ :=
      mfderiv I₁ I₁ (fun w : U => rightBlock U g w i k) x.1
    have hB (k : Fin 2) : HasMFDerivAt I₁ I₁
        (fun w : U => rightBlock U g w i k) x.1 (L k) :=
      ((rightBlock_entry_holomorphic U g i k).mdifferentiable (by simp) x.1).hasMFDerivAt
    have he (k : Fin 2) : HasMFDerivAt I₂ I₁
        (fun ζ : ComplexPlane₂ => ζ k) x.2 (ContinuousLinearMap.proj k) :=
      (ContinuousLinearMap.proj k : ComplexPlane₂ →L[ℂ] ℂ).hasMFDerivAt
    have hm (k : Fin 2) := ((hB k).comp x hf).mul ((he k).comp x hs)
    have hsum := (hm 0).add (hm 1)
    have heo : HasMFDerivAt I₂ I₁ (fun ζ : ComplexPlane₂ => ζ i)
        (complexLift U g hg x).2 (ContinuousLinearMap.proj i) :=
      (ContinuousLinearMap.proj i : ComplexPlane₂ →L[ℂ] ℂ).hasMFDerivAt
    have hout := heo.comp x (hso.comp x hd)
    have hsame := hout.mfderiv
    have hfun : (fun y : Cover U => (complexLift U g hg y).2 i) =
        ((fun y : Cover U => rightBlock U g y.1 i 0 * y.2 0) +
          (fun y : Cover U => rightBlock U g y.1 i 1 * y.2 1)) := by
      funext y
      simp only [complexLift, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply]
    change mfderiv ((I₁).prod I₂) I₁
      (fun y : Cover U => (complexLift U g hg y).2 i) x = _ at hsame
    rw [hfun] at hsame
    have heq := hsame.symm.trans hsum.mfderiv
    have heqv := congrArg (fun A : Model →L[ℂ] ℂ => A v) heq
    change (mfderiv ((I₁).prod I₂) ((I₁).prod I₂) (complexLift U g hg) x v).2 i =
      (rightBlock U g x.1 i 0 * v.2 0 + x.2 0 * L 0 v.1) +
        (rightBlock U g x.1 i 1 * v.2 1 + x.2 1 * L 1 v.1) at heqv
    rw [scalar_linear_apply (L 0), scalar_linear_apply (L 1)] at heqv
    rw [heqv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, rightBlockDerivative]
    change (rightBlock U g x.1 i 0 * v.2 0 + x.2 0 * (L 0 1 * v.1)) +
        (rightBlock U g x.1 i 1 * v.2 1 + x.2 1 * (L 1 1 * v.1)) =
      rightBlock U g x.1 i 0 * v.2 0 + rightBlock U g x.1 i 1 * v.2 1 +
        v.1 * (L 0 1 * x.2 0 + L 1 1 * x.2 1)
    ring

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance
