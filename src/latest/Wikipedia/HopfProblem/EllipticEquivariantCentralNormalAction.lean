import Wikipedia.HopfProblem.EllipticEquivariantCentralNormalCoordinates
import Wikipedia.HopfProblem.EllipticBundleCharacters

/-!
# The actual normal action for arbitrary equivariant periods

The supplied family's charts retain the original base coordinate.
Differentiating the genuine finite-action rotation formula therefore
computes its action on the normal tangent quotient as the transverse
character. The complex differential is taken in the supplied varying
period atlas throughout.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

variable {j : Kind} (D : Equivariant.Data j)

local notation "IF" => modelWithCornersSelf ℂ FamilyModel

theorem familyAction_projection_coe (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    (D.periods.projection (g • x) : ℂ) =
      (normalCharacter j g : ℂ) * (D.periods.projection x : ℂ) := by
  let := D.action v hv
  rw [D.action_apply]
  change ((familyRotation j)^[g.toAdd.val] x.1 : ℂ) =
    (normalCharacter j g : ℂ) * (x.1 : ℂ)
  rw [familyRotation_iterate_val, normalCharacter_apply]

/-- The transverse part of the actual manifold differential is exactly
the normal character, for every element of the finite cyclic group. -/
theorem familyAction_mfderiv_fst (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    letI := D.action v hv
    ∀ w, (mfderiv IF IF (fun y : D.TotalSpace => g • y) x w).1 =
      (normalCharacter j g : ℂ) * w.1 := by
  let := D.periods.totalChartedSpace
  let := D.action v hv
  have hf : MDifferentiableAt IF IF (fun y : D.TotalSpace => g • y) x :=
    (D.action_holomorphic v hv g).mdifferentiableAt (by simp)
  have hinv : Filter.Tendsto (chartAt FamilyModel x).symm
      (𝓝 (chartAt FamilyModel x x)) (𝓝 x) := by
    simpa only [ContinuousAt, (chartAt FamilyModel x).left_inv
      (mem_chart_source FamilyModel x)] using
      (chartAt FamilyModel x).symm.continuousAt (mem_chart_target FamilyModel x)
  have ht : ∀ᶠ z in 𝓝 x, g • z ∈ (chartAt FamilyModel (g • x)).source :=
    (D.action_holomorphic v hv g).continuous.continuousAt
      ((chartAt FamilyModel (g • x)).open_source.mem_nhds
        (mem_chart_source FamilyModel (g • x)))
  have he : (fun z =>
      ((chartAt FamilyModel (g • x) ∘ (fun y : D.TotalSpace => g • y) ∘
        (chartAt FamilyModel x).symm) z).1) =ᶠ[𝓝 (chartAt FamilyModel x x)]
      (fun z => (normalCharacter j g : ℂ) * z.1) := by
    filter_upwards [(chartAt FamilyModel x).open_target.mem_nhds
      (mem_chart_target FamilyModel x), hinv.eventually ht] with z hz hgz
    dsimp only [Function.comp_apply]
    rw [← D.familyProjection_chart (g • x) (g • (chartAt FamilyModel x).symm z) hgz,
      D.familyAction_projection_coe, D.familyProjection_chart_symm x z hz]
  intro w
  rw [NormalCoordinates.mfderiv_eq_chart_fderiv hf]
  exact NormalLinear.fst_fderiv_of_eventuallyEq _ _ _
    (NormalCoordinates.differentiableAt_chart hf) he w

/-- The action on the quotient by the vertical tangent image is defined
by the actual differential, rather than prescribed by a scalar character. -/
def familyNormalDerivative (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    (FamilyModel ⧸ NormalLinear.vertical ComplexPlane₂) →L[ℂ]
      (FamilyModel ⧸ NormalLinear.vertical ComplexPlane₂) := by
  let := D.periods.totalChartedSpace
  let := D.action v hv
  exact NormalLinear.normalMap (mfderiv IF IF (fun y : D.TotalSpace => g • y) x)
    (normalCharacter j g : ℂ) (D.familyAction_mfderiv_fst v hv g x)

theorem familyNormalDerivative_mk (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    letI := D.action v hv
    ∀ w : FamilyModel,
      D.familyNormalDerivative v hv g x (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk (mfderiv IF IF (fun y : D.TotalSpace => g • y) x w) := by
  intro w
  rfl

/-- The proved scalar formula holds on the complete actual quotient line. -/
theorem familyNormalDerivative_eq_character (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    D.familyNormalDerivative v hv g x = (normalCharacter j g : ℂ) •
      ContinuousLinearMap.id ℂ (FamilyModel ⧸ NormalLinear.vertical ComplexPlane₂) := by
  let := D.periods.totalChartedSpace
  let := D.action v hv
  exact NormalLinear.normalMap_eq_smul _ _ (D.familyAction_mfderiv_fst v hv g x)

theorem familyNormalDerivative_coordinate (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace)
    (w : FamilyModel ⧸ NormalLinear.vertical ComplexPlane₂) :
    NormalLinear.normalEquiv ComplexPlane₂ (D.familyNormalDerivative v hv g x w) =
      (normalCharacter j g : ℂ) * NormalLinear.normalEquiv ComplexPlane₂ w := by
  rw [D.familyNormalDerivative_eq_character]
  simp only [smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
