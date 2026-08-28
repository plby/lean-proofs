import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultSections
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultInclusion
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarPlane

/-!
# The genuine holomorphic kernel on the native period torus

The two actual antiholomorphic derivatives vanish on included native
holomorphic sections. Conversely, their vanishing makes the literal
covering-space lift jointly analytic by the proved Cauchy--Riemann
criterion. The original quotient-chart criterion then gives an actual
holomorphic section on the whole original open set, with unchanged values.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open PeriodTorusLineBundleClassification

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

variable (p : PeriodDomain)

/-- The extension of an included holomorphic section is holomorphic at
every point of its original open domain, in the unchanged native charts. -/
theorem smoothExtend_inclusion_contMDiffAt (U : Opens p.Torus)
    (f : HolomorphicSection p U) (x : p.Torus) (hx : x ∈ U) :
    ContMDiffAt I₂ 𝓘(ℂ) ω (smoothExtend p U (inclusionSection p U f)) x := by
  apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
  rw [smoothExtend_comp_val]
  exact f.contMDiff _

/-- The literal lift of an included holomorphic section is complex
analytic above the original open domain. -/
theorem liftSection_inclusion_contDiffAt (U : Opens p.Torus)
    (f : HolomorphicSection p U) (z : ComplexPlane₂) (hz : p.lattice.mkQ z ∈ U) :
    ContDiffAt ℂ ω (liftSection p U (inclusionSection p U f)) z :=
  ((smoothExtend_inclusion_contMDiffAt p U f (p.lattice.mkQ z) hz).comp z
    (p.torus_projection_holomorphic z)).contDiffAt

/-- Every actual antiholomorphic coordinate derivative of the holomorphic
lift vanishes on the genuine covering open set. -/
theorem dbar_lift_inclusion (i : Fin 2) (U : Opens p.Torus)
    (f : HolomorphicSection p U) (z : ComplexPlane₂) (hz : p.lattice.mkQ z ∈ U) :
    dbarCoordinate (liftSection p U (inclusionSection p U f)) i z = 0 :=
  dbarCoordinate_zero_of_differentiableAt
    ((liftSection_inclusion_contDiffAt p U f z hz).differentiableAt (by simp)) i

theorem derivativeSection_inclusion (i : Fin 2) (U : Opens p.Torus)
    (f : HolomorphicSection p U) :
    derivativeSection p i U (inclusionSection p U f) = 0 := by
  apply ContMDiffMap.ext
  intro x
  let z := DiscreteQuotient.representative p.lattice (x : p.Torus)
  have hz : p.lattice.mkQ z ∈ U := by
    simpa only [z, DiscreteQuotient.mkQ_representative] using x.property
  change dbarCoordinate (liftSection p U (inclusionSection p U f)) i z = 0
  exact dbar_lift_inclusion p i U f z hz

/-- The actual first native differential kills actual holomorphic sections. -/
theorem differentialSection_inclusion (U : Opens p.Torus) (f : HolomorphicSection p U) :
    differentialSection p U (inclusionSection p U f) = 0 :=
  Prod.ext (derivativeSection_inclusion p 0 U f) (derivativeSection_inclusion p 1 U f)

/-- The genuine holomorphic inclusion and the native differential compose to zero. -/
theorem inclusion_differential : inclusion p ≫ differential p = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (differentialSection_inclusion p U.unop)

/-- A zero native antiholomorphic differential forces genuine joint
analyticity of the original covering lift on its actual covering open. -/
theorem analytic_lift_of_differential_zero (U : Opens p.Torus) (s : SmoothSection p U)
    (hs : differentialSection p U s = 0) :
    AnalyticOnNhd ℂ (liftSection p U s) (coverOpen p U) := by
  apply analyticOnNhd_of_dbarCoordinate_zero (coverOpen p U).isOpen
    ((liftSection_contDiffOn p U s).differentiableOn (by simp))
  · intro z hz
    rw [← derivativeSection_pullback p 0 U s z hz]
    exact congrArg (fun a : PairSection p U => a.1 ⟨p.lattice.mkQ z, hz⟩) hs
  · intro z hz
    rw [← derivativeSection_pullback p 1 U s z hz]
    exact congrArg (fun a : PairSection p U => a.2 ⟨p.lattice.mkQ z, hz⟩) hs

/-- The analyticity of the genuine lift gives holomorphicity at the
original torus point by its original quotient chart. -/
theorem holomorphicAt_of_differential_zero (U : Opens p.Torus) (s : SmoothSection p U)
    (hs : differentialSection p U s = 0) (x : p.Torus) (hx : x ∈ U) :
    ContMDiffAt I₂ 𝓘(ℂ) ω (smoothExtend p U s) x := by
  apply contMDiffAt_complex_of_lift p x ω
  have hz : p.lattice.mkQ (DiscreteQuotient.chart p.lattice x x) ∈ U := by
    rw [DiscreteQuotient.mkQ_chart p.lattice x x (mem_chartSource p x)]
    exact hx
  exact ((analytic_lift_of_differential_zero p U s hs) _ hz).contDiffAt

/-- Every native smooth section in the actual kernel has a genuine
holomorphic preimage on the same whole open set, with identical values. -/
theorem exists_holomorphic_preimage (U : Opens p.Torus) (s : SmoothSection p U)
    (hs : differentialSection p U s = 0) :
    ∃ f : HolomorphicSection p U, inclusionSection p U f = s := by
  let f : HolomorphicSection p U :=
    ⟨fun x => smoothExtend p U s x, fun x => contMDiffAt_subtype_iff.mpr
      (holomorphicAt_of_differential_zero p U s hs x x.property)⟩
  refine ⟨f, ContMDiffMap.ext fun x => ?_⟩
  exact smoothExtend_apply p U s x x.property

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
