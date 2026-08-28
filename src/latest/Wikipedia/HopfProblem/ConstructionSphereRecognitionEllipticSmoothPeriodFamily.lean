import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothCovers
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothCoordinates
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothForward

/-!
# Real smooth marking of the actual varying period family

The literal real-coordinate marking identifies a varying period family
with the original base times any fixed original period torus.  Smoothness
in both directions follows on the genuine complex vector covers from the
actual period matrices and their inverses, then descends in the original
quotient atlases.  In particular this is not a transported product atlas.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

open Elliptic

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U) (p₀ : PeriodDomain)

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "I₂" => modelWithCornersSelf ℝ ComplexPlane₂

local instance familyVectorChartedSpace : ChartedSpace FamilyModel (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

local instance familyRealVectorChartedSpace :
    ChartedSpace (ℂ × RealPlane₄) (U × RealPlane₄) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ RealPlane₄) (U × RealPlane₄))

/-- The target atlas is exactly the ordinary product of the inherited base
atlas and the original complex period-torus atlas. -/
@[instance_reducible] def fixedPeriodProductChartedSpace :
    ChartedSpace FamilyModel (U × p₀.Torus) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × p₀.Torus))

attribute [local instance] fixedPeriodProductChartedSpace

/-- The fixed marking changes only the original real torus coordinate. -/
def familyPeriodHomeomorph : P.TotalSpace ≃ₜ U × p₀.Torus :=
  (Homeomorph.refl U).prodCongr (flatTorusPeriodHomeomorph p₀)

@[simp] theorem familyPeriodHomeomorph_apply (b : U) (x : RealTorus₄) :
    familyPeriodHomeomorph P p₀ (b, x) = (b, flatTorusPeriodHomeomorph p₀ x) := rfl

@[simp] theorem familyPeriodHomeomorph_symm_apply (b : U) (x : p₀.Torus) :
    (familyPeriodHomeomorph P p₀).symm (b, x) =
      (b, (flatTorusPeriodHomeomorph p₀).symm x) := rfl

/-- The original fixed-period vector covering, with unchanged base coordinate. -/
def fixedPeriodCover (p : U × ComplexPlane₂) : U × p₀.Torus :=
  (p.1, p₀.lattice.mkQ p.2)

theorem fixedPeriodCover_surjective : Function.Surjective (fixedPeriodCover (U := U) p₀) := by
  rintro ⟨b, x⟩
  obtain ⟨z, rfl⟩ := p₀.lattice.mkQ_surjective x
  exact ⟨(b, z), rfl⟩

/-- The vector coordinate change from the varying to the fixed actual period basis. -/
def familyForwardLift (p : U × ComplexPlane₂) : U × ComplexPlane₂ :=
  (p.1, Elliptic.periodEquiv p₀ ((P.periodEquiv p.1).symm p.2))

/-- The exact inverse vector coordinate change. -/
def familyInverseLift (p : U × ComplexPlane₂) : U × ComplexPlane₂ :=
  (p.1, P.periodEquiv p.1 ((Elliptic.periodEquiv p₀).symm p.2))

theorem familyPeriodHomeomorph_quotientMap (p : U × ComplexPlane₂) :
    familyPeriodHomeomorph P p₀ (P.quotientMap p) =
      fixedPeriodCover p₀ (familyForwardLift P p₀ p) := by
  rcases p with ⟨b, z⟩
  change (b, flatTorusPeriodHomeomorph p₀
    (standardLattice.mkQ ((P.periodEquiv b).symm z))) = _
  rw [flatTorusPeriodHomeomorph_mkQ]
  rfl

theorem familyPeriodHomeomorph_symm_fixedCover (p : U × ComplexPlane₂) :
    (familyPeriodHomeomorph P p₀).symm (fixedPeriodCover p₀ p) =
      P.quotientMap (familyInverseLift P p₀ p) := by
  rcases p with ⟨b, z⟩
  obtain ⟨v, rfl⟩ := (Elliptic.periodEquiv p₀).surjective z
  change (b, (flatTorusPeriodHomeomorph p₀).symm (flatProjection p₀ v)) =
    (b, standardLattice.mkQ ((P.periodEquiv b).symm
      (P.periodEquiv b ((Elliptic.periodEquiv p₀).symm (Elliptic.periodEquiv p₀ v)))))
  rw [flatTorusPeriodHomeomorph_symm_flatProjection,
    ContinuousLinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

private theorem familyBase_contMDiff :
    ContMDiff IR 𝓘(ℝ, ℂ) ∞ (fun p : U × ComplexPlane₂ => p.1) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

private theorem familyVector_contMDiff :
    ContMDiff IR I₂ ∞ (fun p : U × ComplexPlane₂ => p.2) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

theorem familyForwardLift_contMDiff : ContMDiff IR IR ∞ (familyForwardLift P p₀) := by
  have hz := (Elliptic.periodEquiv p₀).contDiff.contMDiff.comp
    (PeriodFamilyHolomorphicCohomology.Smooth.inversePeriodCoordinates_native_contMDiff P)
  rw [modelWithCornersSelf_prod]
  exact familyBase_contMDiff.prodMk hz

theorem familyInverseLift_contMDiff : ContMDiff IR IR ∞ (familyInverseLift P p₀) := by
  have hv : ContMDiff IR 𝓘(ℝ, RealPlane₄) ∞
      (fun p : U × ComplexPlane₂ => (Elliptic.periodEquiv p₀).symm p.2) :=
    (Elliptic.periodEquiv p₀).symm.contDiff.contMDiff.comp familyVector_contMDiff
  have hp : ContMDiff IR (modelWithCornersSelf ℝ (ℂ × RealPlane₄)) ∞
      (fun p : U × ComplexPlane₂ => (p.1, (Elliptic.periodEquiv p₀).symm p.2)) := by
    rw [modelWithCornersSelf_prod]
    exact familyBase_contMDiff.prodMk hv
  have hz := (PeriodFamilyHolomorphicCohomology.Smooth.periodCoordinates_native_contMDiff P).comp hp
  rw [modelWithCornersSelf_prod]
  exact familyBase_contMDiff.prodMk hz

/-- The fixed-period covering is locally real analytic in the same product atlas. -/
theorem fixedPeriodCover_real_isLocalDiffeomorph :
    IsLocalDiffeomorph IR IR ω (fixedPeriodCover (U := U) p₀) := by
  have h : IsLocalDiffeomorph (modelWithCornersSelf ℂ FamilyModel)
      (modelWithCornersSelf ℂ FamilyModel) ω (fixedPeriodCover (U := U) p₀) := by
    rw [modelWithCornersSelf_prod]
    exact isLocalDiffeomorph_prodLeft 𝓘(ℂ, ℂ) (B := U)
      (discreteProject_isLocalDiffeomorph p₀.lattice ω)
  exact CuspCircleNormalTrivialization.isLocalDiffeomorph_real_of_complex h

/-- Smoothness of the literal marking from the original varying-family atlas. -/
theorem familyPeriodHomeomorph_contMDiff :
    letI := P.totalChartedSpace
    ContMDiff IR IR ∞ (familyPeriodHomeomorph P p₀) := by
  let := P.totalChartedSpace
  have hq := CuspCircleNormalTrivialization.isLocalDiffeomorph_real_of_complex
    P.quotientMap_isLocalDiffeomorph
  apply contMDiff_of_comp_real_localDiffeomorph hq P.quotientMap_surjective
  have hc : ContMDiff IR IR ∞ (fixedPeriodCover (U := U) p₀) :=
    (fixedPeriodCover_real_isLocalDiffeomorph p₀).contMDiff.of_le le_top
  exact (hc.comp (familyForwardLift_contMDiff P p₀)).congr
    (familyPeriodHomeomorph_quotientMap P p₀)

/-- Smoothness of the exact inverse in the original fixed-torus product atlas. -/
theorem familyPeriodHomeomorph_symm_contMDiff :
    letI := P.totalChartedSpace
    ContMDiff IR IR ∞ (familyPeriodHomeomorph P p₀).symm := by
  let := P.totalChartedSpace
  apply contMDiff_of_comp_real_localDiffeomorph
    (fixedPeriodCover_real_isLocalDiffeomorph p₀) (fixedPeriodCover_surjective p₀)
  have hq : ContMDiff IR IR ∞ P.quotientMap :=
    (CuspCircleNormalTrivialization.contMDiff_real_of_complex
      P.quotientMap_holomorphic).of_le le_top
  exact (hq.comp (familyInverseLift_contMDiff P p₀)).congr
    (familyPeriodHomeomorph_symm_fixedCover P p₀)

/-- A genuine real smooth trivialization of the actual period family, not a new atlas. -/
def familyPeriodDiffeomorph :
    letI := P.totalChartedSpace
    Diffeomorph IR IR P.TotalSpace (U × p₀.Torus) ∞ := by
  letI := P.totalChartedSpace
  exact {
    toEquiv := (familyPeriodHomeomorph P p₀).toEquiv
    contMDiff_toFun := familyPeriodHomeomorph_contMDiff P p₀
    contMDiff_invFun := familyPeriodHomeomorph_symm_contMDiff P p₀ }

@[simp] theorem familyPeriodDiffeomorph_apply (b : U) (x : RealTorus₄) :
    letI := P.totalChartedSpace
    familyPeriodDiffeomorph P p₀ (b, x) = (b, flatTorusPeriodHomeomorph p₀ x) := rfl

@[simp] theorem familyPeriodDiffeomorph_symm_apply (b : U) (x : p₀.Torus) :
    letI := P.totalChartedSpace
    (familyPeriodDiffeomorph P p₀).symm (b, x) =
      (b, (flatTorusPeriodHomeomorph p₀).symm x) := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth
