import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticNormalQuotient

/-!
# Normal quotients of the literal elliptic sphere fibres

The native surface parametrization is a proved biholomorphism onto the
literal sphere fibre with its ambient-slice atlas. Its surjective
differential shows that the tangent image of this actual subspace
inclusion is exactly the tangent image of the original central-surface
inclusion. Consequently their normal quotients are identified by the
identity on ambient tangent representatives, in their natural quotient
topologies. This explicitly relates the geometric normal bundle to the
literal global fibre, not only to a parametrized copy of it.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Elliptic.FamilyModel

attribute [local instance] Threefold.chartedSpace

variable (j : Elliptic.Kind) (b : RiemannSphere) (hb : sphereValue j = b)

/-- The derivative of the genuine fibre parametrization is surjective
in the independently constructed surface and ambient-slice atlases. -/
theorem centralSphereFibreBiholomorph_mfderiv_surjective (x : SpecialCentralSurface j) :
    letI := centralSphereFibreChartedSpace j b hb
    Surjective (mfderiv I₂ I₂ (centralSphereFibreBiholomorph j b hb) x) := by
  let := centralSphereFibreChartedSpace j b hb
  have h := (centralSphereFibreBiholomorph j b hb).isLocalDiffeomorph x
  exact (h.mfderivToContinuousLinearEquiv (by simp)).surjective

/-- Both genuine inclusions have precisely the same ambient tangent
image at the corresponding point of the literal fibre. -/
theorem centralSphereFibre_tangentRange (x : SpecialCentralSurface j) :
    letI := centralSphereFibreChartedSpace j b hb
    (mfderiv I₂ IF (centralSurfaceInclusion j) x).range =
      (mfderiv I₂ IF (Subtype.val : SphereFibre b → Threefold.Space)
        (centralSphereFibreBiholomorph j b hb x)).range := by
  let := centralSphereFibreChartedSpace j b hb
  let e := centralSphereFibreBiholomorph j b hb
  have he : (Subtype.val : SphereFibre b → Threefold.Space) ∘ e =
      centralSurfaceInclusion j := funext (centralSphereFibreBiholomorph_coe j b hb)
  have hi : MDifferentiableAt I₂ IF (Subtype.val : SphereFibre b → Threefold.Space) (e x) :=
    (centralSphereFibre_inclusion_holomorphic j b hb).mdifferentiableAt (by simp)
  have hd := mfderiv_comp x hi (e.contMDiff.mdifferentiableAt (by simp))
  rw [he] at hd
  have hs := centralSphereFibreBiholomorph_mfderiv_surjective j b hb x
  rw [hd]
  apply le_antisymm
  · rintro w ⟨u, rfl⟩
    exact ⟨mfderiv I₂ I₂ e x u, rfl⟩
  · rintro w ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := hs u
    refine ⟨v, ?_⟩
    change mfderiv I₂ IF (Subtype.val : SphereFibre b → Threefold.Space) (e x)
      (mfderiv I₂ I₂ e x v) = _
    rw [hv]
    rfl

/-- The literal normal tangent quotient of the actual subspace fibre
in the actual global complex atlas. -/
abbrev LiteralSphereNormalFibre (y : SphereFibre b) :=
  letI := Threefold.chartedSpace
  letI := centralSphereFibreChartedSpace j b hb
  Elliptic.FamilyModel ⧸
    (mfderiv I₂ IF (Subtype.val : SphereFibre b → Threefold.Space) y).range

/-- The actual normal quotient is unaffected by the proved native
biholomorphic parametrization of the literal elliptic fibre. -/
def literalNormalFibreIdentification (x : SpecialCentralSurface j) :
    letI := centralSphereFibreChartedSpace j b hb
    GlobalCentralNormalFibre j x ≃L[ℂ]
      LiteralSphereNormalFibre j b hb (centralSphereFibreBiholomorph j b hb x) := by
  let := centralSphereFibreChartedSpace j b hb
  let S : Submodule ℂ Elliptic.FamilyModel :=
    (mfderiv I₂ IF (centralSurfaceInclusion j) x).range
  let T : Submodule ℂ Elliptic.FamilyModel :=
    (mfderiv I₂ IF (Subtype.val : SphereFibre b → Threefold.Space)
      (centralSphereFibreBiholomorph j b hb x)).range
  exact
    { Submodule.quotEquivOfEq S T (centralSphereFibre_tangentRange j b hb x) with
      continuous_toFun := S.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
        continuous_quot_mk
      continuous_invFun := T.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
        continuous_quot_mk }

/-- This is the identity on genuine ambient tangent representatives,
not an unspecified abstract equivalence between one-dimensional spaces. -/
@[simp] theorem literalNormalFibreIdentification_mk (x : SpecialCentralSurface j)
    (w : Elliptic.FamilyModel) :
    letI := centralSphereFibreChartedSpace j b hb
    literalNormalFibreIdentification j b hb x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk w := rfl

@[simp] theorem literalNormalFibreIdentification_symm_mk (x : SpecialCentralSurface j)
    (w : Elliptic.FamilyModel) :
    letI := centralSphereFibreChartedSpace j b hb
    (literalNormalFibreIdentification j b hb x).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk w := rfl

/-- The original analytic special normal bundle fibre identifies with
the actual normal quotient of the literal global sphere fibre. -/
def specialNormalFibreToLiteral (x : SpecialCentralSurface j) :
    letI := centralSphereFibreChartedSpace j b hb
    (specialCentralNormalBundle j).Fiber x ≃L[ℂ]
      LiteralSphereNormalFibre j b hb (centralSphereFibreBiholomorph j b hb x) := by
  let := centralSphereFibreChartedSpace j b hb
  exact (specialNormalFibreToGlobal j x).trans (literalNormalFibreIdentification j b hb x)

theorem literalSphereNormalFibre_rank_one (x : SpecialCentralSurface j) :
    letI := centralSphereFibreChartedSpace j b hb
    Module.finrank ℂ
      (LiteralSphereNormalFibre j b hb (centralSphereFibreBiholomorph j b hb x)) = 1 := by
  let := centralSphereFibreChartedSpace j b hb
  exact (literalNormalFibreIdentification j b hb x).toLinearEquiv.symm.finrank_eq.trans
    (globalCentralNormalFibre_rank_one j x)

/-- Rank one holds at every point of the literal elliptic fibre, not
only at a separately selected surface representative. -/
theorem literalSphereNormalFibre_rank_one_all (y : SphereFibre b) :
    Module.finrank ℂ (LiteralSphereNormalFibre j b hb y) = 1 := by
  let := centralSphereFibreChartedSpace j b hb
  obtain ⟨x, rfl⟩ := (centralSphereFibreBiholomorph j b hb).surjective y
  exact literalSphereNormalFibre_rank_one j b hb x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
