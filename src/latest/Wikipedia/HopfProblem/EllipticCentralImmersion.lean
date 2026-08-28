import Wikipedia.HopfProblem.EllipticCentralFibre
import Wikipedia.HopfProblem.PeriodFamilyFibreImmersion
import Wikipedia.HopfProblem.PeriodFamilyFibreImmersionDescent

/-!
# The central elliptic surface is an embedded complex submanifold

The central torus is an actual coordinate-fibre immersion in the varying
period family.  This normal form passes through the unramified finite
quotient on the target and descends through the finite quotient on the
source.  Thus the previously constructed closed embedding of the central
surface is a holomorphic immersion, not only a topological embedding.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ FamilyModel

theorem centralInclusion_isImmersionOfComplement (j : Kind) :
    letI := (familyPeriods j).totalChartedSpace
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω (centralInclusion j) :=
  (familyPeriods j).fibreInclusion_isImmersionOfComplement SpecialPeriods.discZero

theorem centralInclusion_isImmersion (j : Kind) :
    letI := (familyPeriods j).totalChartedSpace
    Manifold.IsImmersion I₂ I₃ ω (centralInclusion j) := by
  let := (familyPeriods j).totalChartedSpace
  exact (centralInclusion_isImmersionOfComplement j).isImmersion

/-- Every period-torus fibre remains immersed after the unramified finite
quotient of the ambient family, including noncentral fibres. -/
theorem fillingFibreInclusion_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : SpecialPeriods.Disc) :
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (fillingQuotient j v hv ∘ (familyPeriods j).fibreInclusion z) := by
  let := (familyPeriods j).totalChartedSpace
  let := (familyPeriods j).totalSpace_isManifold
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact CoveringQuotient.immersion_project
    (FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) (Family j))
    (familyAction_holomorphic j v hv.1)
    ((familyPeriods j).fibreInclusion_holomorphic z).continuous
    ((familyPeriods j).fibreInclusion_isImmersionOfComplement z)

/-- Quotienting the ambient family does not change the central immersion's
one-dimensional transverse complement. -/
theorem centralFibreCover_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (fillingQuotient j v hv ∘ centralInclusion j) :=
  fillingFibreInclusion_isImmersionOfComplement j v hv SpecialPeriods.discZero

/-- The actual quotient surface is a codimension-one holomorphic immersion
in the actual filling, for the already constructed source and target atlases. -/
theorem centralFibreInclusion_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω (centralFibreInclusion j v hv) := by
  let := affineAction j (centralPeriod j) v hv.1
  let := affineAction_continuous j (centralPeriod j) v hv.1
  let := affineAction_free j (centralPeriod j) v hv
  apply CoveringQuotient.immersion_of_comp_project
    (FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) (centralPeriod j).val.Torus)
    (affineAction_holomorphic j (centralPeriod j) v hv.1)
    (centralFibreInclusion_continuous j v hv)
  change Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
    (centralFibreInclusion j v hv ∘ surfaceProjection j (centralPeriod j) v hv)
  have he : centralFibreInclusion j v hv ∘ surfaceProjection j (centralPeriod j) v hv =
      fillingQuotient j v hv ∘ centralInclusion j := by
    funext x
    exact centralFibreInclusion_surfaceProjection j v hv x
  rw [he]
  exact centralFibreCover_isImmersionOfComplement j v hv

theorem centralFibreInclusion_isImmersion (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    Manifold.IsImmersion I₂ I₃ ω (centralFibreInclusion j v hv) :=
  (centralFibreInclusion_isImmersionOfComplement j v hv).isImmersion

/-- With the source's specified twist, the compact central complex surface
is unconditionally embedded as the whole central fibre. -/
theorem mainCentralFibre_embedded (j : Kind) :
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
        (centralFibreInclusion j j.twist (mainTwist_admissible j)) ∧
      IsClosedEmbedding (centralFibreInclusion j j.twist (mainTwist_admissible j)) ∧
      range (centralFibreInclusion j j.twist (mainTwist_admissible j)) =
        fillingProjection j j.twist (mainTwist_admissible j) ⁻¹' {Elliptic.discZero} :=
  ⟨centralFibreInclusion_isImmersionOfComplement j j.twist (mainTwist_admissible j),
    centralFibreInclusion_isClosedEmbedding j j.twist (mainTwist_admissible j),
    range_centralFibreInclusion j j.twist (mainTwist_admissible j)⟩

end Wikipedia.HopfProblem.Elliptic
