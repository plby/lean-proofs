import Wikipedia.HopfProblem.EllipticEquivariantCentralFibre
import Wikipedia.HopfProblem.PeriodFamilyFibreImmersion
import Wikipedia.HopfProblem.PeriodFamilyFibreImmersionDescent

/-!
# The central surface immersion in an arbitrary equivariant period family

The existing fibre-immersion theorem applies to the actual period map.
Its normal form passes through the unramified ambient covering and then
descends through the central torus covering, retaining the one-dimensional
complex transverse complement.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

open SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ FamilyModel

theorem centralInclusion_isImmersionOfComplement :
    letI := D.periods.totalChartedSpace
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω D.centralInclusion :=
  D.periods.fibreInclusion_isImmersionOfComplement SpecialPeriods.discZero

/-- Every genuine period-torus fibre remains immersed in the actual
finite quotient for the supplied varying-period atlas. -/
theorem fillingFibreInclusion_isImmersionOfComplement (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) :
    letI := D.chartedSpace v hv
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (D.quotient v hv ∘ D.periods.fibreInclusion z) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.chartedSpace v hv
  let := D.action v hv.1
  exact CoveringQuotient.immersion_project (D.quotientCoveringMap v hv)
    (D.action_holomorphic v hv.1)
    (D.periods.fibreInclusion_holomorphic z).continuous
    (D.periods.fibreInclusion_isImmersionOfComplement z)

theorem centralFibreCover_isImmersionOfComplement (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (D.quotient v hv ∘ D.centralInclusion) :=
  D.fillingFibreInclusion_isImmersionOfComplement v hv SpecialPeriods.discZero

/-- The actual central finite affine quotient is immersed with a complex
line as transverse complement, for the two original quotient atlases. -/
theorem centralFibreInclusion_isImmersionOfComplement (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω (D.centralFibreInclusion v hv) := by
  let := D.chartedSpace v hv
  let := affineAction j D.centralPeriod v hv.1
  let := affineAction_continuous j D.centralPeriod v hv.1
  let := affineAction_free j D.centralPeriod v hv
  apply CoveringQuotient.immersion_of_comp_project
    (FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) D.centralPeriod.val.Torus)
    (affineAction_holomorphic j D.centralPeriod v hv.1)
    (D.centralFibreInclusion_continuous v hv)
  change Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
    (D.centralFibreInclusion v hv ∘ surfaceProjection j D.centralPeriod v hv)
  have he : D.centralFibreInclusion v hv ∘ surfaceProjection j D.centralPeriod v hv =
      D.quotient v hv ∘ D.centralInclusion := by
    funext x
    exact D.centralFibreInclusion_surfaceProjection v hv x
  rw [he]
  exact D.centralFibreCover_isImmersionOfComplement v hv

theorem centralFibreInclusion_isImmersion (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    Manifold.IsImmersion I₂ I₃ ω (D.centralFibreInclusion v hv) := by
  let := D.chartedSpace v hv
  exact (D.centralFibreInclusion_isImmersionOfComplement v hv).isImmersion

/-- With the original arithmetic twist, the actual central complex
surface is embedded as the entire central fibre of the supplied filling. -/
theorem mainCentralFibre_embedded :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
        (D.centralFibreInclusion j.twist (mainTwist_admissible j)) ∧
      IsClosedEmbedding (D.centralFibreInclusion j.twist (mainTwist_admissible j)) ∧
      range (D.centralFibreInclusion j.twist (mainTwist_admissible j)) =
        D.projection j.twist (mainTwist_admissible j) ⁻¹' {Elliptic.discZero} :=
  ⟨D.centralFibreInclusion_isImmersionOfComplement j.twist (mainTwist_admissible j),
    D.centralFibreInclusion_isClosedEmbedding j.twist (mainTwist_admissible j),
    D.range_centralFibreInclusion j.twist (mainTwist_admissible j)⟩

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
