import Wikipedia.HopfProblem.EllipticBundleCharacters
import Wikipedia.HopfProblem.EllipticBundleNormalCoordinates

/-!
# The actual transverse differential of the cyclic family action

The base coordinate in the inherited family atlas is the original disc
coordinate.  Differentiating its actual rotation identity therefore shows
that the induced action on the quotient by the vertical tangent space is
exactly the transverse character, including every element of the cyclic
group and not only its chosen generator.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

local notation "IF" => modelWithCornersSelf ℂ FamilyModel

theorem familyAction_projection_coe (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    ((familyPeriods j).projection (g • x) : ℂ) =
      (normalCharacter j g : ℂ) * ((familyPeriods j).projection x : ℂ) := by
  let := familyAction j v hv
  rw [familyAction_apply]
  change ((familyRotation j)^[g.toAdd.val] x.1 : ℂ) =
    (normalCharacter j g : ℂ) * (x.1 : ℂ)
  rw [familyRotation_iterate_val, normalCharacter_apply]

/-- The transverse part of the genuine manifold differential in the
inherited varying-period atlas is multiplication by the rotation character. -/
theorem familyAction_mfderiv_fst (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (x : Family j) :
    letI := (familyPeriods j).totalChartedSpace
    letI := familyAction j v hv
    ∀ w, (mfderiv IF IF (fun y : Family j => g • y) x w).1 =
      (normalCharacter j g : ℂ) * w.1 := by
  let := (familyPeriods j).totalChartedSpace
  let := familyAction j v hv
  have hf : MDifferentiableAt IF IF (fun y : Family j => g • y) x :=
    (familyAction_holomorphic j v hv g).mdifferentiableAt (by simp)
  have hinv : Filter.Tendsto (chartAt FamilyModel x).symm
      (𝓝 (chartAt FamilyModel x x)) (𝓝 x) := by
    simpa only [ContinuousAt, (chartAt FamilyModel x).left_inv
      (mem_chart_source FamilyModel x)] using
      (chartAt FamilyModel x).symm.continuousAt (mem_chart_target FamilyModel x)
  have ht : ∀ᶠ z in 𝓝 x, g • z ∈ (chartAt FamilyModel (g • x)).source :=
    (familyAction_holomorphic j v hv g).continuous.continuousAt
      ((chartAt FamilyModel (g • x)).open_source.mem_nhds
        (mem_chart_source FamilyModel (g • x)))
  have he : (fun z =>
      ((chartAt FamilyModel (g • x) ∘ (fun y : Family j => g • y) ∘
        (chartAt FamilyModel x).symm) z).1) =ᶠ[𝓝 (chartAt FamilyModel x x)]
      (fun z => (normalCharacter j g : ℂ) * z.1) := by
    filter_upwards [(chartAt FamilyModel x).open_target.mem_nhds
      (mem_chart_target FamilyModel x), hinv.eventually ht] with z hz hgz
    dsimp only [Function.comp_apply]
    rw [← familyProjection_chart j (g • x) (g • (chartAt FamilyModel x).symm z) hgz,
      familyAction_projection_coe,
      familyProjection_chart_symm j x z hz]
  intro w
  rw [NormalCoordinates.mfderiv_eq_chart_fderiv hf]
  exact NormalLinear.fst_fderiv_of_eventuallyEq _ _ _
    (NormalCoordinates.differentiableAt_chart hf) he w

/-- The actual derivative descends to the normal tangent quotient. -/
def familyNormalDerivative (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    (FamilyModel ⧸ NormalLinear.vertical ComplexPlane₂) →L[ℂ]
      (FamilyModel ⧸ NormalLinear.vertical ComplexPlane₂) := by
  letI := (familyPeriods j).totalChartedSpace
  letI := familyAction j v hv
  exact NormalLinear.normalMap (mfderiv IF IF (fun y : Family j => g • y) x)
    (normalCharacter j g : ℂ) (familyAction_mfderiv_fst j v hv g x)

/-- Its computation on a quotient class explicitly uses the differential
of the actual cyclic action. -/
theorem familyNormalDerivative_mk (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := (familyPeriods j).totalChartedSpace
    letI := familyAction j v hv
    ∀ w : FamilyModel,
      familyNormalDerivative j v hv g x (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk (mfderiv IF IF (fun y : Family j => g • y) x w) := by
  intro w
  rfl

/-- The normal action is exactly the character on the whole quotient line. -/
theorem familyNormalDerivative_eq_character (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (x : Family j) :
    familyNormalDerivative j v hv g x = (normalCharacter j g : ℂ) •
      ContinuousLinearMap.id ℂ (FamilyModel ⧸ NormalLinear.vertical ComplexPlane₂) := by
  let := (familyPeriods j).totalChartedSpace
  let := familyAction j v hv
  exact NormalLinear.normalMap_eq_smul _ _ _

theorem familyNormalDerivative_coordinate (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (x : Family j)
    (w : FamilyModel ⧸ NormalLinear.vertical ComplexPlane₂) :
    NormalLinear.normalEquiv ComplexPlane₂ (familyNormalDerivative j v hv g x w) =
      (normalCharacter j g : ℂ) * NormalLinear.normalEquiv ComplexPlane₂ w := by
  rw [familyNormalDerivative_eq_character]
  simp only [smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

end Wikipedia.HopfProblem.Elliptic
