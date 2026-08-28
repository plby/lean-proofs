import Wikipedia.HopfProblem.EllipticEquivariantCentralImmersion
import Wikipedia.HopfProblem.EllipticFibreManifoldCore
import Wikipedia.HopfProblem.EllipticFibreBiholomorphCore

/-!
# The genuine central fibre atlas for arbitrary equivariant periods

The central fibre retains its literal subspace topology. Its complex
charts are actual ambient immersion slices for the supplied varying
family's quotient atlas. The finite affine quotient of the actual central
period torus is biholomorphic to this fibre through its genuine inclusion.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

variable {j : Kind} (D : Equivariant.Data j)

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ FamilyModel

/-- The literal central fibre of the supplied quotient projection. -/
abbrev CentralFibre (v : Lattice) (hv : AdmissibleTwist j v) :=
  D.projection v hv ⁻¹' {Elliptic.discZero}

theorem centralFibreHomeomorph_isImmersionOfComplement (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (Subtype.val ∘ D.centralFibreHomeomorph v hv) :=
  D.centralFibreInclusion_isImmersionOfComplement v hv

/-- The atlas obtained by restricting actual ambient immersion charts
to their zero transverse coordinate. -/
@[instance_reducible] def centralFibreChartedSpace (v : Lattice)
    (hv : AdmissibleTwist j v) : ChartedSpace ComplexPlane₂ (D.CentralFibre v hv) := by
  let := D.chartedSpace v hv
  exact EmbeddedFibre.chartedSpace (D.centralFibreHomeomorph v hv)
    (D.centralFibreHomeomorph_isImmersionOfComplement v hv)

theorem centralFibre_isManifold (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.centralFibreChartedSpace v hv
    IsManifold I₂ ω (D.CentralFibre v hv) := by
  let := D.chartedSpace v hv
  exact EmbeddedFibre.isManifold (D.centralFibreHomeomorph v hv)
    (D.centralFibreHomeomorph_isImmersionOfComplement v hv)

theorem centralFibre_inclusion_isImmersionOfComplement (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    letI := D.centralFibreChartedSpace v hv
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (Subtype.val : D.CentralFibre v hv → D.Space v hv) := by
  let := D.chartedSpace v hv
  exact EmbeddedFibre.inclusion_isImmersionOfComplement (D.centralFibreHomeomorph v hv)
    (D.centralFibreHomeomorph_isImmersionOfComplement v hv)

/-- Both directions of every selected central-fibre chart are literal
restrictions of charts in the actual ambient maximal atlas. -/
theorem centralFibre_charts_are_ambient_slices (v : Lattice)
    (hv : AdmissibleTwist j v) (x : D.CentralFibre v hv) :
    letI := D.chartedSpace v hv
    letI := D.centralFibreChartedSpace v hv
    ∃ c : OpenPartialHomeomorph (D.Space v hv) FamilyModel,
      ∃ L : (ComplexPlane₂ × ℂ) ≃L[ℂ] FamilyModel,
        c ∈ IsManifold.maximalAtlas I₃ ω (D.Space v hv) ∧
        (chartAt ComplexPlane₂ x).source = Subtype.val ⁻¹' c.source ∧
        (∀ y ∈ (chartAt ComplexPlane₂ x).source,
          c (y : D.Space v hv) = L (chartAt ComplexPlane₂ x y, 0)) ∧
        (∀ z ∈ (chartAt ComplexPlane₂ x).target,
          ((chartAt ComplexPlane₂ x).symm z : D.Space v hv) = c.symm (L (z, 0))) := by
  let := D.chartedSpace v hv
  let := D.centralFibreChartedSpace v hv
  let e := D.centralFibreHomeomorph v hv
  let hι := D.centralFibreHomeomorph_isImmersionOfComplement v hv
  obtain ⟨c, hc, hs, hf, hi⟩ := EmbeddedFibre.exists_ambient_restriction e hι x
  exact ⟨c, EmbeddedFibre.coordinateEquiv e hι x, hc, hs, hf, hi⟩

/-- The original affine quotient surface of the actual fixed central
period is biholomorphic to the actual reduced central fibre. -/
def centralFibreBiholomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.centralFibreChartedSpace v hv
    Diffeomorph I₂ I₂ (Surface j D.centralPeriod v hv) (D.CentralFibre v hv) ω := by
  let := D.chartedSpace v hv
  let := D.centralFibreChartedSpace v hv
  exact EmbeddedFibre.biholomorphOfHomeomorph (D.centralFibreHomeomorph v hv)
    (D.centralFibreInclusion_isImmersion v hv)
    (D.centralFibre_inclusion_isImmersionOfComplement v hv).isImmersion (fun _ => rfl)

@[simp] theorem centralFibreBiholomorph_coe (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j D.centralPeriod v hv) :
    letI := D.centralFibreChartedSpace v hv
    (D.centralFibreBiholomorph v hv x : D.Space v hv) = D.centralFibreInclusion v hv x := rfl

theorem centralFibreHomeomorph_holomorphic (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.centralFibreChartedSpace v hv
    ContMDiff I₂ I₂ ω (D.centralFibreHomeomorph v hv) := by
  let := D.centralFibreChartedSpace v hv
  exact (D.centralFibreBiholomorph v hv).contMDiff

theorem centralFibreHomeomorph_symm_holomorphic (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.centralFibreChartedSpace v hv
    ContMDiff I₂ I₂ ω (D.centralFibreHomeomorph v hv).symm := by
  let := D.centralFibreChartedSpace v hv
  exact (D.centralFibreBiholomorph v hv).symm.contMDiff

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
