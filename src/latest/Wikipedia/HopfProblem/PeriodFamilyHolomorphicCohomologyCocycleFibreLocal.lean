import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultSections
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameCalculusOperations
import Wikipedia.HopfProblem.CoveringManifold

/-!
# Native differentials of the actual negative local period primitives

A holomorphic local lift of the original torus quotient defines the
negative marked real-linear primitive as a genuine smooth section in
the unchanged torus charts. Local uniqueness for the original quotient
map proves that its covering germ is the negative original plane
primitive. Its actual native Dolbeault coefficients are therefore the
negative literal marked antiholomorphic coefficients.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre

open PeriodTorusLineBundleClassification
open PeriodTorusLineBundleClassificationHolomorphicFrame

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IR₂" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

/-- The negative actual marked primitive on a native torus open is
real smooth when composed with its genuine holomorphic local lift. -/
theorem negativeLocalPrimitive_smoothAt (p : PeriodDomain) (a : Fin 4 → ℂ)
    (U : Opens p.Torus) (q : p.Torus → ComplexPlane₂)
    (hq : ContMDiffOn I₂ I₂ ω q U) (t : p.Torus) (ht : t ∈ U) :
    ContMDiffAt IR₂ IR₁ ∞ (fun y => -MarkedLinear.primitive p a (q y)) t := by
  have hqr := PeriodTorusHolomorphicCohomology.Dolbeault.contMDiffAt_real_of_complex
    p t ω (hq.contMDiffAt (U.isOpen.mem_nhds ht))
  exact ((MarkedLinear.primitive p a).contMDiff.contMDiffAt.comp t
    (hqr.of_le (by simp))).neg

/-- The literal negative local primitive, bundled as an actual native
smooth section rather than a new coefficient model. -/
def negativeLocalSection (p : PeriodDomain) (a : Fin 4 → ℂ)
    (U : Opens p.Torus) (q : p.Torus → ComplexPlane₂)
    (hq : ContMDiffOn I₂ I₂ ω q U) :
    PeriodTorusHolomorphicCohomology.Dolbeault.SmoothSection p U :=
  PeriodTorusHolomorphicCohomology.Dolbeault.sectionOfSmooth p U
    (fun t => -MarkedLinear.primitive p a (q t))
    (negativeLocalPrimitive_smoothAt p a U q hq)

@[simp] theorem negativeLocalSection_apply (p : PeriodDomain) (a : Fin 4 → ℂ)
    (U : Opens p.Torus) (q : p.Torus → ComplexPlane₂)
    (hq : ContMDiffOn I₂ I₂ ω q U) (t : U) :
    negativeLocalSection p a U q hq t = -MarkedLinear.primitive p a (q t) := rfl

/-- The original quotient and its actual local lift are inverse on a
whole neighborhood of the chosen lifted point. -/
theorem localLift_quotient_germ (p : PeriodDomain) (U : Opens p.Torus)
    (q : p.Torus → ComplexPlane₂) (hq : ContMDiffOn I₂ I₂ ω q U)
    (hproj : ∀ t ∈ U, p.lattice.mkQ (q t) = t) (t : p.Torus) (ht : t ∈ U) :
    (fun z => q (p.lattice.mkQ z)) =ᶠ[𝓝 (q t)] (fun z => z) := by
  have hqt : p.lattice.mkQ (q t) ∈ U := (hproj t ht).symm ▸ ht
  have hqc : ContinuousAt q (p.lattice.mkQ (q t)) := by
    rw [hproj t ht]
    exact (hq.contMDiffAt (U.isOpen.mem_nhds ht)).continuousAt
  apply eventuallyEq_of_localHomeomorph_comp_eq
    (DiscreteQuotient.quotient_localHomeomorph p.lattice)
    (hqc.comp p.lattice.continuous_mkQ.continuousAt) continuousAt_id
    (congrArg q (hproj t ht))
  filter_upwards [
    (PeriodTorusHolomorphicCohomology.Dolbeault.coverOpen p U).isOpen.mem_nhds hqt]
    with z hz
  exact hproj _ hz

/-- The genuine covering lift of the actual smooth section is the
negative original plane primitive near its own original local lift. -/
theorem negativeLocalSection_lift_germ (p : PeriodDomain) (a : Fin 4 → ℂ)
    (U : Opens p.Torus) (q : p.Torus → ComplexPlane₂)
    (hq : ContMDiffOn I₂ I₂ ω q U)
    (hproj : ∀ t ∈ U, p.lattice.mkQ (q t) = t) (t : p.Torus) (ht : t ∈ U) :
    PeriodTorusHolomorphicCohomology.Dolbeault.liftSection p U
      (negativeLocalSection p a U q hq) =ᶠ[𝓝 (q t)]
        (fun z => -MarkedLinear.primitive p a z) := by
  have hqt : p.lattice.mkQ (q t) ∈ U := (hproj t ht).symm ▸ ht
  filter_upwards [localLift_quotient_germ p U q hq hproj t ht,
    (PeriodTorusHolomorphicCohomology.Dolbeault.coverOpen p U).isOpen.mem_nhds hqt]
    with z hz hU
  rw [PeriodTorusHolomorphicCohomology.Dolbeault.liftSection_apply _ _ _ z hU,
    negativeLocalSection_apply, hz]

/-- Each actual native antiholomorphic coefficient has the asserted
constant value, with the negative sign forced by the local primitive. -/
theorem derivativeSection_negativeLocalSection_apply (p : PeriodDomain)
    (a : Fin 4 → ℂ) (U : Opens p.Torus) (q : p.Torus → ComplexPlane₂)
    (hq : ContMDiffOn I₂ I₂ ω q U)
    (hproj : ∀ t ∈ U, p.lattice.mkQ (q t) = t) (k : Fin 2) (t : U) :
    PeriodTorusHolomorphicCohomology.Dolbeault.derivativeSection p k U
      (negativeLocalSection p a U q hq) t = -MarkedLinear.dbarLinear p a k := by
  have hqt : p.lattice.mkQ (q t) ∈ U := (hproj t t.property).symm ▸ t.property
  have he : (⟨p.lattice.mkQ (q t), hqt⟩ : U) = t := Subtype.ext (hproj t t.property)
  have hd := PeriodTorusHolomorphicCohomology.Dolbeault.derivativeSection_pullback
    p k U (negativeLocalSection p a U q hq) (q t) hqt
  rw [he] at hd
  refine hd.trans ((dbarCoordinate_congr
    (negativeLocalSection_lift_germ p a U q hq hproj t t.property) k).trans ?_)
  rw [dbarCoordinate_neg (MarkedLinear.primitive p a).differentiableAt,
    MarkedLinear.dbarCoordinate_primitive]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CocycleFibre
