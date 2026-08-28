import Wikipedia.HopfProblem.CuspCoinvariantExtensionPhaseActionTopology
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCusp
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealMaps

/-!
# The original smooth period-one real action on the full cusp cap

The real action is the restriction of the existing complex vertical
flow, with exactly the original time parameter.  Joint smoothness uses
the original quotient atlas and the native product charts, changing
only the scalar field of differentiation and the order of arguments.
The actual cusp parameter, and hence every native radial collar, is
preserved.  No new action or manifold structure is introduced.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase

open ToricCharts SpecialPeriods.CuspFamily ThreefoldHomologyFinitenessCusp
open SpecialPeriods.Threefold.VerticalAction.Cusp

local notation "I₃" => modelWithCornersSelf ℝ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℝ ℂ

/-- The actual vertical flow at real time, on the unchanged entire cusp quotient. -/
def nativeRealFlow (D : Data) (t : ℝ) (q : FullSpace D) : FullSpace D :=
  flow D.correction D.radius (t : ℂ) q

@[simp] theorem nativeRealFlow_eq_flow (D : Data) (t : ℝ) (q : FullSpace D) :
    nativeRealFlow D t q = flow D.correction D.radius (t : ℂ) q := rfl

@[simp] theorem nativeRealFlow_zero (D : Data) (q : FullSpace D) :
    nativeRealFlow D 0 q = q := by
  exact flow_zero D.correction D.radius q

/-- The original additive action law, with no change of real parameter. -/
theorem nativeRealFlow_add (D : Data) (t s : ℝ) (q : FullSpace D) :
    nativeRealFlow D (t + s) q = nativeRealFlow D t (nativeRealFlow D s q) := by
  simp only [nativeRealFlow, Complex.ofReal_add, flow_add]

/-- Period one is inherited from the actual integer-period complex flow. -/
theorem nativeRealFlow_period_one (D : Data) (t : ℝ) (q : FullSpace D) :
    nativeRealFlow D (t + 1) q = nativeRealFlow D t q := by
  have hone : flow D.correction D.radius (1 : ℂ) q = q := by
    simpa only [Int.cast_one] using flow_int_cast D.correction D.radius (1 : ℤ) q
  simp only [nativeRealFlow, Complex.ofReal_add, Complex.ofReal_one, flow_add, hone]

/-- The original cusp projection is fixed at every real time, including at the centre. -/
@[simp] theorem nativeRealFlow_projection (D : Data) (t : ℝ) (q : FullSpace D) :
    CuspQuotient.projection D.correction D.radius (nativeRealFlow D t q) =
      CuspQuotient.projection D.correction D.radius q :=
  projection_flow D.correction D.radius (t : ℂ) q

/-- Every norm collar uses the same original radius before and after the action. -/
@[simp] theorem nativeRealFlow_parameterNorm (D : Data) (t : ℝ) (q : FullSpace D) :
    parameterNorm D (nativeRealFlow D t q) = parameterNorm D q :=
  congrArg norm (nativeRealFlow_projection D t q)

private theorem nativeComplexFlow_joint_real_contMDiff (D : Data) :
    letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
    ContMDiff (I₃.prod I₁) I₃ ∞
      (fun p : FullSpace D × ℂ => flow D.correction D.radius p.2 p.1) := by
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
    D.radius_lt_one D.holomorphic D.smallDrift
  have hc : ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3 × ℂ))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (fun p : FullSpace D × ℂ => flow D.correction D.radius p.2 p.1) := by
    rw [modelWithCornersSelf_prod]
    exact flow_joint_holomorphic D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  have hr := (CuspCircleNormalTrivialization.contMDiff_real_of_complex hc).of_le
    (show ∞ ≤ ω from le_top)
  rw [modelWithCornersSelf_prod] at hr
  exact hr

/-- Joint real smoothness in time-first order, in the original native quotient atlas. -/
theorem nativeRealFlow_joint_contMDiff (D : Data) :
    letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
    ContMDiff ((𝓘(ℝ)).prod I₃) I₃ ∞
      (fun p : ℝ × FullSpace D => nativeRealFlow D p.1 p.2) := by
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
    D.radius_lt_one D.holomorphic D.smallDrift
  have ht : ContMDiff ((𝓘(ℝ)).prod I₃) I₁ ∞
      (fun p : ℝ × FullSpace D => (p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.contMDiff.comp contMDiff_fst
  have hi : ContMDiff ((𝓘(ℝ)).prod I₃) (I₃.prod I₁) ∞
      (fun p : ℝ × FullSpace D => (p.2, (p.1 : ℂ))) :=
    contMDiff_snd.prodMk ht
  exact (nativeComplexFlow_joint_real_contMDiff D).comp hi

/-- The same original action is jointly continuous on the full original cap. -/
theorem nativeRealFlow_joint_continuous (D : Data) :
    Continuous (fun p : ℝ × FullSpace D => nativeRealFlow D p.1 p.2) := by
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos
    D.radius_lt_one D.holomorphic D.smallDrift
  exact (nativeRealFlow_joint_contMDiff D).continuous

end Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase
