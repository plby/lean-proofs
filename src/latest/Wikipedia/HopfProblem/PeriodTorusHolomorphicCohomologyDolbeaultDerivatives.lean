import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultLifts

/-!
# Native antiholomorphic derivatives on every torus open

Each actual coordinate derivative is evaluated on a literal covering
lift. Independence of that lift proves its local formula in every
original quotient chart and hence its genuine smoothness. The resulting
operators are complex-linear, commute with all actual restrictions, and
satisfy the real mixed-derivative identity.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open PeriodTorusLineBundleClassification
open PeriodTorusLineBundleClassificationHolomorphicFrame

local notation "IR₂" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

/-- The actual derivative, named using a representative; its value on
the section domain is proved independent of this choice. -/
def derivativeValue (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus)
    (s : SmoothSection p U) (x : p.Torus) : ℂ :=
  dbarCoordinate (liftSection p U s) i (DiscreteQuotient.representative p.lattice x)

/-- The derivative in every actual covering coordinate is the literal
antiholomorphic coordinate derivative of the actual lifted function. -/
theorem derivativeValue_pullback (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus)
    (s : SmoothSection p U) (z : ComplexPlane₂) (hz : p.lattice.mkQ z ∈ U) :
    derivativeValue p i U s (p.lattice.mkQ z) = dbarCoordinate (liftSection p U s) i z := by
  apply dbar_lift_eq_of_mkQ_eq p i U s
  · simpa only [DiscreteQuotient.mkQ_representative] using hz
  · exact DiscreteQuotient.mkQ_representative p.lattice (p.lattice.mkQ z)

/-- The derivative is genuinely smooth in the original quotient charts. -/
theorem derivativeValue_contMDiffAt (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus)
    (s : SmoothSection p U) (x : p.Torus) (hx : x ∈ U) :
    ContMDiffAt IR₂ IR₁ ∞ (derivativeValue p i U s) x := by
  let z := DiscreteQuotient.chart p.lattice x x
  have hz : p.lattice.mkQ z ∈ U := by
    rw [DiscreteQuotient.mkQ_chart p.lattice x x (mem_chartSource p x)]
    exact hx
  apply contMDiffAt_real_of_lift p x ∞
  have he : (derivativeValue p i U s ∘ p.lattice.mkQ) =ᶠ[𝓝 z]
      dbarCoordinate (liftSection p U s) i := by
    filter_upwards [(coverOpen p U).isOpen.mem_nhds hz] with w hw
    exact derivativeValue_pullback p i U s w hw
  have hd := contDiffAt_dbarCoordinate (liftSection_contDiffAt p U s z hz) i
  exact hd.congr_of_eventuallyEq he

/-- Actual complex-linear differentiation of native smooth sections. -/
def derivativeSection (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus) :
    SmoothSection p U →ₗ[ℂ] SmoothSection p U where
  toFun s := ⟨fun x => derivativeValue p i U s x, fun x =>
    contMDiffAt_subtype_iff.mpr (derivativeValue_contMDiffAt p i U s x x.property)⟩
  map_add' s t := by
    apply ContMDiffMap.ext
    intro x
    let z := DiscreteQuotient.representative p.lattice (x : p.Torus)
    have hz : p.lattice.mkQ z ∈ U := by
      simpa only [z, DiscreteQuotient.mkQ_representative] using x.property
    change dbarCoordinate (liftSection p U (s + t)) i z =
      dbarCoordinate (liftSection p U s) i z + dbarCoordinate (liftSection p U t) i z
    rw [liftSection_add]
    exact dbarCoordinate_add
      ((liftSection_contDiffAt p U s z hz).differentiableAt (by simp))
      ((liftSection_contDiffAt p U t z hz).differentiableAt (by simp)) i
  map_smul' c s := by
    apply ContMDiffMap.ext
    intro x
    let z := DiscreteQuotient.representative p.lattice (x : p.Torus)
    have hz : p.lattice.mkQ z ∈ U := by
      simpa only [z, DiscreteQuotient.mkQ_representative] using x.property
    change dbarCoordinate (liftSection p U (c • s)) i z =
      c * dbarCoordinate (liftSection p U s) i z
    rw [liftSection_smul]
    exact dbarCoordinate_const_mul
      ((liftSection_contDiffAt p U s z hz).differentiableAt (by simp)) c i

@[simp] theorem derivativeSection_apply (p : PeriodDomain) (i : Fin 2)
    (U : Opens p.Torus) (s : SmoothSection p U) (x : U) :
    derivativeSection p i U s x = derivativeValue p i U s x := rfl

/-- The native section operator has its literal covering-space derivative formula. -/
theorem derivativeSection_pullback (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus)
    (s : SmoothSection p U) (z : ComplexPlane₂) (hz : p.lattice.mkQ z ∈ U) :
    derivativeSection p i U s ⟨p.lattice.mkQ z, hz⟩ =
      dbarCoordinate (liftSection p U s) i z :=
  derivativeValue_pullback p i U s z hz

/-- These genuine derivatives commute with every original section restriction. -/
theorem derivativeSection_restrict (p : PeriodDomain) (i : Fin 2)
    {U V : Opens p.Torus} (h : U ≤ V) (s : SmoothSection p V) :
    derivativeSection p i U (restriction p h s) =
      restriction p h (derivativeSection p i V s) := by
  apply ContMDiffMap.ext
  intro x
  let z := DiscreteQuotient.representative p.lattice (x : p.Torus)
  have hz : p.lattice.mkQ z ∈ U := by
    simpa only [z, DiscreteQuotient.mkQ_representative] using x.property
  exact dbarCoordinate_congr (liftSection_restrict_germ p h s z hz) i

/-- The lifted derivative agrees with the actual derivative on a full
neighborhood of every point above the section domain. -/
theorem liftSection_derivative_germ (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus)
    (s : SmoothSection p U) (z : ComplexPlane₂) (hz : p.lattice.mkQ z ∈ U) :
    liftSection p U (derivativeSection p i U s) =ᶠ[𝓝 z]
      dbarCoordinate (liftSection p U s) i := by
  filter_upwards [(coverOpen p U).isOpen.mem_nhds hz] with w hw
  rw [liftSection_apply _ _ _ w hw]
  exact derivativeSection_pullback p i U s w hw

/-- Mixed native antiholomorphic derivatives commute by the actual real
Schwarz theorem on the covering vector space. -/
theorem derivativeSection_commute (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) :
    derivativeSection p 0 U (derivativeSection p 1 U s) =
      derivativeSection p 1 U (derivativeSection p 0 U s) := by
  apply ContMDiffMap.ext
  intro x
  let z := DiscreteQuotient.representative p.lattice (x : p.Torus)
  have hz : p.lattice.mkQ z ∈ U := by
    simpa only [z, DiscreteQuotient.mkQ_representative] using x.property
  change dbarCoordinate (liftSection p U (derivativeSection p 1 U s)) 0 z =
    dbarCoordinate (liftSection p U (derivativeSection p 0 U s)) 1 z
  rw [dbarCoordinate_congr (liftSection_derivative_germ p 1 U s z hz) 0,
    dbarCoordinate_congr (liftSection_derivative_germ p 0 U s z hz) 1]
  exact dbarCoordinate_zero_one_commute_of_contDiffAt (liftSection_contDiffAt p U s z hz)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
