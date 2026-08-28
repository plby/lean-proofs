import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationEllipticLift
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticGerms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticTransport
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupExtension

/-!
# Entire upper-half-plane coefficients of genuine global vector fields

The native lift to each actual elliptic root cover extends the regular
vertical coefficients across its center. The exact gauge and base-change
differentials identify the two on the whole punctured root domain.
Transport by the actual full right-block cocycle supplies the remaining
elliptic orbit points, and density glues the resulting holomorphic germs.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open Elliptic HolomorphicForms.EllipticCover

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  HolomorphicForms.EllipticCover.coverChartedSpace
  HolomorphicForms.EllipticCover.starCoverChartedSpace
  HolomorphicForms.EllipticCover.cover_isManifold
  HolomorphicForms.EllipticCover.starCover_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace
  HolomorphicForms.RegularCover.cover_isManifold
  triangleGeometricAction

/-- The holomorphic root coefficient is the genuine regular coefficient
on the entire punctured root domain. -/
theorem ellipticVertical_eq (j : Kind) (v : Threefold.HolomorphicVectorFields.Field)
    (z : RootStar j) :
    ellipticVertical j v z.val = regularVertical v (regularBase j z) := by
  have he := ellipticCoefficients_eq_of_regular j v (z, 0)
    (regularVertical v (regularBase j z))
    (regularCoefficients_eq v (regularBase j z) (gaugePoint j (z, 0)).2)
  have hs := congrArg (Prod.snd : FamilyModel → ComplexPlane₂) he
  exact hs

/-- Each actual elliptic center has a holomorphic coefficient germ in
the original upper-half-plane coordinate. -/
theorem vertical_hasExtensionAt_center (v : Threefold.HolomorphicVectorFields.Field)
    (j : Kind) :
    HolomorphicForms.EllipticExtension.HasExtensionAt (regularVertical v)
      (Triangle.ellipticCenter j) :=
  exists_elliptic_germ_of_rootExtension j (regularVertical v) (ellipticVertical j v)
    (ellipticVertical_holomorphic j v) (ellipticVertical_eq j v)

/-- Column-vector transport by the unchanged full special-period right block. -/
def verticalTransform (g : TriangleGroup) (x : ℍ × ComplexPlane₂) : ComplexPlane₂ :=
  HolomorphicForms.RegularCover.groupRightBlockExtension g x.1 *ᵥ x.2

theorem verticalTransform_holomorphic (g : TriangleGroup) :
    ContMDiff ((I₁).prod I₂) I₂ ω (verticalTransform g) := by
  apply contMDiff_pi_space.mpr
  intro i
  have hv : ∀ k : Fin 2, ContMDiff ((I₁).prod I₂) I₁ ω
      (fun x : ℍ × ComplexPlane₂ => x.2 k) :=
    contMDiff_pi_space.mp
      (contMDiff_snd : ContMDiff ((I₁).prod I₂) I₂ ω
        (Prod.snd : ℍ × ComplexPlane₂ → ComplexPlane₂))
  have hR : ∀ k : Fin 2, ContMDiff ((I₁).prod I₂) I₁ ω
      (fun x : ℍ × ComplexPlane₂ =>
        HolomorphicForms.RegularCover.groupRightBlockExtension g x.1 i k) :=
    fun k => (HolomorphicForms.RegularCover.groupRightBlockExtension_entry_holomorphic
      g i k).comp contMDiff_fst
  apply (((hR 0).mul (hv 0)).add ((hR 1).mul (hv 1))).congr
  intro x
  simp only [verticalTransform, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.add_apply, Pi.mul_apply]

/-- The actual two center germs and actual all-word covariance construct
an entire upper-half-plane extension of both native vertical coefficients. -/
theorem exists_verticalExtension (v : Threefold.HolomorphicVectorFields.Field) :
    ∃ V : ℍ → ComplexPlane₂, ContMDiff I₁ I₂ ω V ∧
      ∀ z : TriangleRegularPoint, V z.val = regularVertical v z := by
  apply HolomorphicForms.EllipticExtension.exists_extension_of_center_germs
    (regularVertical v) (regularVertical_holomorphic v) verticalTransform
    verticalTransform_holomorphic
  · intro g z
    exact regularVertical_group v g z
  · exact vertical_hasExtensionAt_center v

/-- The holomorphic extension constructed from the genuine field itself. -/
def verticalExtension (v : Threefold.HolomorphicVectorFields.Field) : ℍ → ComplexPlane₂ :=
  Classical.choose (exists_verticalExtension v)

theorem verticalExtension_holomorphic (v : Threefold.HolomorphicVectorFields.Field) :
    ContMDiff I₁ I₂ ω (verticalExtension v) :=
  (Classical.choose_spec (exists_verticalExtension v)).1

@[simp] theorem verticalExtension_restrict (v : Threefold.HolomorphicVectorFields.Field)
    (z : TriangleRegularPoint) : verticalExtension v z.val = regularVertical v z :=
  (Classical.choose_spec (exists_verticalExtension v)).2 z

/-- Density determines the extension independently of its chosen local germs. -/
theorem verticalExtension_unique (v : Threefold.HolomorphicVectorFields.Field)
    {V : ℍ → ComplexPlane₂} (hV : ContMDiff I₁ I₂ ω V)
    (he : ∀ z : TriangleRegularPoint, V z.val = regularVertical v z) :
    V = verticalExtension v :=
  HolomorphicExtensionGluing.holomorphic_extension_unique triangleRegularDomain
    (regularVertical v) triangleRegularLocus_dense hV (verticalExtension_holomorphic v)
    he (verticalExtension_restrict v)

/-- The full original column-vector covariance holds also at every
elliptic point, by continuity and density of the actual regular locus. -/
theorem verticalExtension_group (v : Threefold.HolomorphicVectorFields.Field)
    (g : TriangleGroup) (z : ℍ) :
    verticalExtension v (triangleGeometricRepresentation g z) =
      HolomorphicForms.RegularCover.groupRightBlockExtension g z *ᵥ verticalExtension v z := by
  have he : (fun w : ℍ => verticalExtension v (triangleGeometricRepresentation g w)) =
      (fun w : ℍ => verticalTransform g (w, verticalExtension v w)) := by
    apply Continuous.ext_on triangleRegularLocus_dense
      ((verticalExtension_holomorphic v).comp
        (triangleGeometricRepresentation_holomorphic g)).continuous
      ((verticalTransform_holomorphic g).comp
        (contMDiff_id.prodMk (verticalExtension_holomorphic v))).continuous
    intro w hw
    let y : TriangleRegularPoint := ⟨w, hw⟩
    change verticalExtension v ((g • y : TriangleRegularPoint) : ℍ) =
      HolomorphicForms.RegularCover.groupRightBlockExtension g y.val *ᵥ
        verticalExtension v y.val
    rw [verticalExtension_restrict, verticalExtension_restrict,
      HolomorphicForms.RegularCover.groupRightBlockExtension_restrict]
    exact regularVertical_group v g y
  exact congrFun he z

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
