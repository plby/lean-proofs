import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupTransport

/-!
# Joint holomorphic transport by the actual global group factors

The actual right-block cocycle and native group-action Jacobian extend
holomorphically over the entire original upper half-plane. Their proved
invertibility gives joint holomorphic transformations of all four regular
form coefficients, with no exceptional-point factor hypotheses. The
coefficient identities below are the solved transport laws of genuine
global holomorphic forms.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension

open RegularCover
open HolomorphicDifferentialForms (Form)

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- Actual row-covector transport by the inverse original right block. -/
def oneFibreTransform (g : TriangleGroup) (x : ℍ × ComplexPlane₂) : ComplexPlane₂ :=
  x.2 ᵥ* (groupRightBlockExtension g x.1)⁻¹

/-- Actual mixed-covector transport also includes the reciprocal native
base Jacobian. -/
def twoMixedTransform (g : TriangleGroup) (x : ℍ × ComplexPlane₂) : ComplexPlane₂ :=
  (groupBaseDerivativeExtension g x.1)⁻¹ • oneFibreTransform g x

/-- Actual top-degree transport uses the full triangular differential's
base factor and right-block determinant. -/
def topTransform (g : TriangleGroup) (x : ℍ × ℂ) : ℂ :=
  x.2 / (groupBaseDerivativeExtension g x.1 * (groupRightBlockExtension g x.1).det)

/-- Actual base-one-form transport uses the reciprocal native Jacobian. -/
def oneBaseTransform (g : TriangleGroup) (x : ℍ × ℂ) : ℂ :=
  x.2 / groupBaseDerivativeExtension g x.1

@[simp] theorem oneFibreTransform_apply (g : TriangleGroup) (z : ℍ) (v : ComplexPlane₂) :
    oneFibreTransform g (z, v) = v ᵥ* (groupRightBlockExtension g z)⁻¹ := rfl

@[simp] theorem twoMixedTransform_apply (g : TriangleGroup) (z : ℍ) (v : ComplexPlane₂) :
    twoMixedTransform g (z, v) = (groupBaseDerivativeExtension g z)⁻¹ •
      (v ᵥ* (groupRightBlockExtension g z)⁻¹) := rfl

@[simp] theorem topTransform_apply (g : TriangleGroup) (z : ℍ) (c : ℂ) :
    topTransform g (z, c) =
      c / (groupBaseDerivativeExtension g z * (groupRightBlockExtension g z).det) := rfl

@[simp] theorem oneBaseTransform_apply (g : TriangleGroup) (z : ℍ) (a : ℂ) :
    oneBaseTransform g (z, a) = a / groupBaseDerivativeExtension g z := rfl

/-- Joint holomorphicity in the original upper-half-plane coordinate and
both original coefficient coordinates. -/
theorem oneFibreTransform_holomorphic (g : TriangleGroup) :
    ContMDiff ((I₁).prod I₂) I₂ ω (oneFibreTransform g) := by
  apply contMDiff_pi_space.mpr
  intro k
  have hv : ∀ i : Fin 2, ContMDiff ((I₁).prod I₂) I₁ ω
      (fun x : ℍ × ComplexPlane₂ => x.2 i) :=
    contMDiff_pi_space.mp
      (contMDiff_snd : ContMDiff ((I₁).prod I₂) I₂ ω
        (Prod.snd : ℍ × ComplexPlane₂ → ComplexPlane₂))
  have hR : ∀ i : Fin 2, ContMDiff ((I₁).prod I₂) I₁ ω
      (fun x : ℍ × ComplexPlane₂ => (groupRightBlockExtension g x.1)⁻¹ i k) :=
    fun i => (groupRightBlockExtension_inv_entry_holomorphic g i k).comp contMDiff_fst
  apply (((hv 0).mul (hR 0)).add ((hv 1).mul (hR 1))).congr
  intro x
  simp only [oneFibreTransform, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Pi.add_apply, Pi.mul_apply]

theorem twoMixedTransform_holomorphic (g : TriangleGroup) :
    ContMDiff ((I₁).prod I₂) I₂ ω (twoMixedTransform g) :=
  ((groupBaseDerivativeExtension_inv_holomorphic g).comp contMDiff_fst).smul
    (oneFibreTransform_holomorphic g)

private theorem rightBlockDet_holomorphic (g : TriangleGroup) :
    ContMDiff I₁ I₁ ω (fun z : ℍ => (groupRightBlockExtension g z).det) := by
  apply (((groupRightBlockExtension_entry_holomorphic g 0 0).mul
      (groupRightBlockExtension_entry_holomorphic g 1 1)).sub
      ((groupRightBlockExtension_entry_holomorphic g 0 1).mul
        (groupRightBlockExtension_entry_holomorphic g 1 0))).congr
  intro z
  simp only [Matrix.det_fin_two, Pi.mul_apply]

theorem topTransform_holomorphic (g : TriangleGroup) :
    ContMDiff ((I₁).prod I₁) I₁ ω (topTransform g) := by
  have hJ : ContMDiff ((I₁).prod I₁) I₁ ω
      (fun x : ℍ × ℂ => groupBaseDerivativeExtension g x.1) :=
    (groupBaseDerivativeExtension_holomorphic g).comp contMDiff_fst
  have hR : ContMDiff ((I₁).prod I₁) I₁ ω
      (fun x : ℍ × ℂ => (groupRightBlockExtension g x.1).det) :=
    (rightBlockDet_holomorphic g).comp contMDiff_fst
  exact contMDiff_snd.div₀ (hJ.mul hR) (fun x =>
    mul_ne_zero (groupBaseDerivativeExtension_ne_zero g x.1)
      (groupRightBlockExtension_det_ne_zero g x.1))

theorem oneBaseTransform_holomorphic (g : TriangleGroup) :
    ContMDiff ((I₁).prod I₁) I₁ ω (oneBaseTransform g) := by
  have hJ : ContMDiff ((I₁).prod I₁) I₁ ω
      (fun x : ℍ × ℂ => groupBaseDerivativeExtension g x.1) :=
    (groupBaseDerivativeExtension_holomorphic g).comp contMDiff_fst
  exact contMDiff_snd.div₀ hJ (fun x => groupBaseDerivativeExtension_ne_zero g x.1)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Every genuine global one-form obeys this joint fibre transformation. -/
theorem fibreOne_group_transform (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    fibreOne θ (g • z) = oneFibreTransform g (z.val, fibreOne θ z) :=
  fibreOne_group_transport_extension θ g z

/-- Every genuine global two-form obeys this joint mixed transformation. -/
theorem mixedTwo_group_transform (θ : Form Model Threefold.Space 2)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    mixedTwo θ (g • z) = twoMixedTransform g (z.val, mixedTwo θ z) :=
  mixedTwo_group_transport_extension θ g z

/-- Every genuine global top form obeys this joint scalar transformation. -/
theorem baseTop_group_transform (θ : Form Model Threefold.Space 3)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    baseTop θ (g • z) = topTransform g (z.val, baseTop θ z) :=
  baseTop_group_transport_extension θ g z

/-- Every genuine global one-form obeys this joint base transformation. -/
theorem baseOne_group_transform (θ : Form Model Threefold.Space 1)
    (g : TriangleGroup) (z : TriangleRegularPoint) :
    baseOne θ (g • z) = oneBaseTransform g (z.val, baseOne θ z) :=
  baseOne_group_transport_extension θ g z

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension
