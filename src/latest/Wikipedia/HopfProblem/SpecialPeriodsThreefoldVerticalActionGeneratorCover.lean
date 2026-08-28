import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionGeneratorGeneral
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriod
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionCover

/-!
# The exact native generator on the actual regular vector cover

The parameter acts on the original period vectors by `z ↦ z + ![0, s]`.
Differentiating this literal formula in the inherited regular-cover atlas
gives the vector `(0, ![0, 1])`. The parameter here is the additive complex
translation parameter, so no exponential normalization factor occurs.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction

open HolomorphicForms.RegularCover

attribute [local instance] coverChartedSpace cover_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- The actual jointly defined translation on the original regular vector cover. -/
def vectorJointFlow (p : Cover × ℂ) : Cover := Period.vectorFlow p.2 p.1

theorem vectorJointFlow_holomorphic :
    ContMDiff ((IF).prod 𝓘(ℂ)) IF ω vectorJointFlow :=
  Period.jointVectorFlow_holomorphic

@[simp] theorem vectorJointFlow_zero (x : Cover) : vectorJointFlow (x, 0) = x := by
  simp only [vectorJointFlow, Period.vectorFlow, Period.vector_zero, add_zero]

/-- The native analytic generator of the actual regular vector-cover flow. -/
def vectorGenerator : HolomorphicVectorFields.Field Model Cover :=
  HolomorphicVectorFields.timeGenerator Model Cover vectorJointFlow
    vectorJointFlow_holomorphic vectorJointFlow_zero

/-- The generator is exactly the original second period-vector direction. -/
theorem vectorGenerator_apply (x : Cover) :
    vectorGenerator x = (0, (![0, 1] : ComplexPlane₂)) := by
  have hd : HasDerivAt (fun s : ℂ => x.2 + Period.vector s)
      (![0, 1] : ComplexPlane₂) 0 := by
    simpa only [Period.vector_eq_smul, one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℂ)).smul_const (![0, 1] : ComplexPlane₂)).const_add x.2
  have hv : ContMDiff 𝓘(ℂ) 𝓘(ℂ, ComplexPlane₂) ω
      (fun s : ℂ => x.2 + Period.vector s) :=
    (contDiff_const.add Period.vector_holomorphic).contMDiff
  change mfderiv 𝓘(ℂ) IF (fun s : ℂ => (x.1, x.2 + Period.vector s)) 0 (1 : ℂ) = _
  erw [modelWithCornersSelf_prod,
    mfderiv_prodMk mdifferentiableAt_const (hv.mdifferentiableAt (by simp))]
  apply Prod.ext
  · erw [mfderiv_const]
    rfl
  · erw [mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
    change (1 : ℂ) • (![0, 1] : ComplexPlane₂) = (![0, 1] : ComplexPlane₂)
    exact one_smul ℂ _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction
