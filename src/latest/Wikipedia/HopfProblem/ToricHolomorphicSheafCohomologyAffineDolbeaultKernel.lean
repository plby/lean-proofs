import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultSections
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarAnalytic

/-!
# The actual holomorphic kernel on the affine complex plane

Vanishing of the two actual antiholomorphic derivatives implies joint
analyticity by the proved two-variable Cauchy--Riemann theorem. Thus the
kernel consists of genuine holomorphic functions, on the same open set,
and not of a separately specified sheaf with a presumed identification.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

open PeriodTorusLineBundleClassification

/-- Included holomorphic functions have their original analytic representative. -/
theorem smoothExtend_inclusion (U : Opens (ℂ × ℂ)) (f : HolomorphicSection U) :
    smoothExtend U (inclusionSection U f) = HolomorphicFunctionSheaf.extendSection U f := rfl

/-- The actual first differential kills actual holomorphic sections. -/
theorem differentialSection_inclusion (U : Opens (ℂ × ℂ)) (f : HolomorphicSection U) :
    differentialSection U (inclusionSection U f) = 0 := by
  apply Prod.ext
  · apply ContMDiffMap.ext
    intro q
    change dbarFirst (smoothExtend U (inclusionSection U f)) q = 0
    rw [smoothExtend_inclusion]
    exact (coordinate_dbar_zero_of_analyticAt
      (HolomorphicFunctionSheaf.extendSection_analyticAt U f q q.property)).1
  · apply ContMDiffMap.ext
    intro q
    change dbarSecond (smoothExtend U (inclusionSection U f)) q = 0
    rw [smoothExtend_inclusion]
    exact (coordinate_dbar_zero_of_analyticAt
      (HolomorphicFunctionSheaf.extendSection_analyticAt U f q q.property)).2

/-- The actual sheaf inclusion and the actual first derivative compose to zero. -/
theorem inclusion_differential : inclusion ≫ differential = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (differentialSection_inclusion U.unop)

/-- A zero actual antiholomorphic derivative forces genuine joint analyticity. -/
theorem analytic_of_differential_zero (U : Opens (ℂ × ℂ)) (s : SmoothSection U)
    (hs : differentialSection U s = 0) : AnalyticOnNhd ℂ (smoothExtend U s) U := by
  apply analyticOnNhd_of_coordinate_dbar_zero U.isOpen
    ((smoothExtend_contDiffOn U s).differentiableOn (by simp))
  · intro q hq
    exact congrArg (fun p : PairSection U => p.1 ⟨q, hq⟩) hs
  · intro q hq
    exact congrArg (fun p : PairSection U => p.2 ⟨q, hq⟩) hs

/-- Every actual section in the kernel has a holomorphic preimage on its
whole original open domain, with unchanged values. -/
theorem exists_holomorphic_preimage (U : Opens (ℂ × ℂ)) (s : SmoothSection U)
    (hs : differentialSection U s = 0) :
    ∃ f : HolomorphicSection U, inclusionSection U f = s := by
  let f : HolomorphicSection U :=
    ⟨fun q => smoothExtend U s q, fun q => contMDiffAt_subtype_iff.mpr
      ((analytic_of_differential_zero U s hs) q q.property).contDiffAt.contMDiffAt⟩
  refine ⟨f, ContMDiffMap.ext fun q => ?_⟩
  exact smoothExtend_apply U s q q.property

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
