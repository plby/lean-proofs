import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsRegularCover
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The native derivative of the lifted triangle action

The lifted action uses the original regular upper-half-plane coordinate
and the original period-vector coordinates. Its derivative is obtained
from the manifold chain rule and the entrywise product rule for the
constructed right-block matrix.
-/

noncomputable section

open Matrix
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] coverChartedSpace cover_isManifold

/-- The derivative of the actual base action in the inherited complex chart. -/
def groupBaseDerivative (g : TriangleGroup) (z : TriangleRegularPoint) : ℂ :=
  mfderiv I₁ I₁ (fun w : TriangleRegularPoint => g • w) z (1 : ℂ)

/-- The entrywise derivative of the actual period right block. -/
def groupRightBlockDerivative (g : TriangleGroup) (z : TriangleRegularPoint) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => mfderiv I₁ I₁ (fun w : TriangleRegularPoint => data.rightBlock g w i k) z (1 : ℂ)

private theorem scalar_linear_apply (L : ℂ →L[ℂ] ℂ) (c : ℂ) : L c = L 1 * c := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using L.map_smul c (1 : ℂ)

/-- The actual native manifold derivative, including the correction from
the base-dependent right block, for every triangle group element. -/
theorem complexLift_mfderiv_apply (g : TriangleGroup) (x : Cover) (v : Model) :
    mfderiv IF IF (data.complexLift g) x v =
      (groupBaseDerivative g x.1 * v.1,
        data.rightBlock g x.1 *ᵥ v.2 +
          v.1 • (groupRightBlockDerivative g x.1 *ᵥ x.2)) := by
  rw [modelWithCornersSelf_prod]
  have hd : HasMFDerivAt ((I₁).prod I₂) ((I₁).prod I₂) (data.complexLift g) x
      (mfderiv ((I₁).prod I₂) ((I₁).prod I₂) (data.complexLift g) x) := by
    rw [← modelWithCornersSelf_prod]
    exact ((data.complexLift_holomorphic g).mdifferentiable (by simp) x).hasMFDerivAt
  have hf : HasMFDerivAt ((I₁).prod I₂) I₁ (fun y : Cover => y.1) x
      (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂) := hasMFDerivAt_fst x
  have hs : HasMFDerivAt ((I₁).prod I₂) I₂ (fun y : Cover => y.2) x
      (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) := hasMFDerivAt_snd x
  have hfo : HasMFDerivAt ((I₁).prod I₂) I₁ (fun y : Cover => y.1)
      (data.complexLift g x) (ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂) :=
    hasMFDerivAt_fst (data.complexLift g x)
  have hso : HasMFDerivAt ((I₁).prod I₂) I₂ (fun y : Cover => y.2)
      (data.complexLift g x) (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) :=
    hasMFDerivAt_snd (data.complexLift g x)
  apply Prod.ext
  · have hb := ((data.base_holomorphic g).mdifferentiable (by simp) x.1).hasMFDerivAt
    have heq := (hfo.comp x hd).mfderiv.symm.trans (hb.comp x hf).mfderiv
    have heqv := congrArg (fun A : Model →L[ℂ] ℂ => A v) heq
    change (mfderiv ((I₁).prod I₂) ((I₁).prod I₂) (data.complexLift g) x v).1 =
      mfderiv I₁ I₁ (fun w : TriangleRegularPoint => g • w) x.1 v.1 at heqv
    exact heqv.trans (scalar_linear_apply _ _)
  · funext i
    let L (k : Fin 2) : ℂ →L[ℂ] ℂ :=
      mfderiv I₁ I₁ (fun w : TriangleRegularPoint => data.rightBlock g w i k) x.1
    have hB (k : Fin 2) : HasMFDerivAt I₁ I₁
        (fun w : TriangleRegularPoint => data.rightBlock g w i k) x.1 (L k) :=
      ((data.rightBlock_entry_holomorphic g i k).mdifferentiable (by simp) x.1).hasMFDerivAt
    have he (k : Fin 2) : HasMFDerivAt I₂ I₁
        (fun ζ : ComplexPlane₂ => ζ k) x.2 (ContinuousLinearMap.proj k) :=
      (ContinuousLinearMap.proj k : ComplexPlane₂ →L[ℂ] ℂ).hasMFDerivAt
    have hm (k : Fin 2) := ((hB k).comp x hf).mul ((he k).comp x hs)
    have hsum := (hm 0).add (hm 1)
    have heo : HasMFDerivAt I₂ I₁ (fun ζ : ComplexPlane₂ => ζ i)
        (data.complexLift g x).2 (ContinuousLinearMap.proj i) :=
      (ContinuousLinearMap.proj i : ComplexPlane₂ →L[ℂ] ℂ).hasMFDerivAt
    have hout := heo.comp x (hso.comp x hd)
    have hsame := hout.mfderiv
    have hfun : (fun y : Cover => (data.complexLift g y).2 i) =
        ((fun y : Cover => data.rightBlock g y.1 i 0 * y.2 0) +
          (fun y : Cover => data.rightBlock g y.1 i 1 * y.2 1)) := by
      funext y
      simp only [TrianglePeriodFamily.Data.complexLift, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, Pi.add_apply]
    change mfderiv ((I₁).prod I₂) I₁ (fun y : Cover => (data.complexLift g y).2 i) x = _
      at hsame
    rw [hfun] at hsame
    have heq := hsame.symm.trans hsum.mfderiv
    have heqv := congrArg (fun A : Model →L[ℂ] ℂ => A v) heq
    change (mfderiv ((I₁).prod I₂) ((I₁).prod I₂) (data.complexLift g) x v).2 i =
      (data.rightBlock g x.1 i 0 * v.2 0 + x.2 0 * L 0 v.1) +
        (data.rightBlock g x.1 i 1 * v.2 1 + x.2 1 * L 1 v.1) at heqv
    rw [scalar_linear_apply (L 0), scalar_linear_apply (L 1)] at heqv
    rw [heqv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, groupRightBlockDerivative]
    change (data.rightBlock g x.1 i 0 * v.2 0 + x.2 0 * (L 0 1 * v.1)) +
        (data.rightBlock g x.1 i 1 * v.2 1 + x.2 1 * (L 1 1 * v.1)) =
      data.rightBlock g x.1 i 0 * v.2 0 + data.rightBlock g x.1 i 1 * v.2 1 +
        v.1 * (L 0 1 * x.2 0 + L 1 1 * x.2 1)
    ring

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
