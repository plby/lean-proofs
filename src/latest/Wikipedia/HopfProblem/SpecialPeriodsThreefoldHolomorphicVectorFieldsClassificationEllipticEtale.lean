import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticHolomorphic

/-!
# The genuine elliptic vector cover is étale

The original root-coordinate cover is locally biholomorphic all the way
through root zero.  It factors as an open root restriction, the actual
period-lattice covering, the free affine finite covering, and the native
open inclusion into the constructed threefold.  All atlases in this
factorization are the already chosen native atlases.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open Elliptic EllipticFilling

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] HolomorphicForms.EllipticCover.coverChartedSpace
  specialFullFillingChartedSpace specialEllipticPieceChartedSpace Threefold.chartedSpace

local instance ellipticPeriodCoverChartedSpace :
    ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

private def ellipticCoverToPeriodPartial (j : Kind) :
    PartialDiffeomorph ((I₁).prod I₂) ((I₁).prod I₂) (HolomorphicForms.EllipticCover.Cover j)
      (Disc × ComplexPlane₂) ω := by
  let e := opensInclusionPartialDiffeomorph I₁
    (HolomorphicForms.EllipticCover.rootDomain j)
    ⟨HolomorphicForms.EllipticCover.rootZero j⟩
  exact {
    toFun p := (e p.1, p.2)
    invFun p := (e.symm p.1, p.2)
    source := e.source ×ˢ univ
    target := e.target ×ˢ univ
    map_source' _ h := ⟨e.map_source h.1, mem_univ _⟩
    map_target' _ h := ⟨e.map_target h.1, mem_univ _⟩
    left_inv' _ h := Prod.ext (e.left_inv h.1) rfl
    right_inv' _ h := Prod.ext (e.right_inv h.1) rfl
    open_source := e.open_source.prod isOpen_univ
    open_target := e.open_target.prod isOpen_univ
    contMDiffOn_toFun :=
      (e.contMDiffOn_toFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd
    contMDiffOn_invFun :=
      (e.contMDiffOn_invFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd }

/-- Forgetting the extra small-radius condition is the actual open
root inclusion times the identity on the two original fibre coordinates. -/
theorem ellipticCoverToPeriod_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph IF IF ω (HolomorphicForms.EllipticCover.coverToPeriod j) := by
  rw [modelWithCornersSelf_prod]
  intro x
  refine ⟨ellipticCoverToPeriodPartial j, ⟨mem_univ _, mem_univ _⟩, ?_⟩
  intro y _
  rfl

/-- Both genuine quotient steps are unramified, including over root zero. -/
theorem ellipticFullCover_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph IF IF ω (HolomorphicForms.EllipticCover.fullCover j) := by
  let := (specialLocalData j).periods.totalChartedSpace
  intro x
  have hp := (specialLocalData j).periods.quotientMap_isLocalDiffeomorph
    (HolomorphicForms.EllipticCover.coverToPeriod j x)
  have hq := VerticalAction.Elliptic.quotient_isLocalDiffeomorph
    (specialLocalData j) j.twist (mainTwist_admissible j)
    ((specialLocalData j).periods.quotientMap
      (HolomorphicForms.EllipticCover.coverToPeriod j x))
  exact ((ellipticCoverToPeriod_isLocalDiffeomorph j x).comp
    (K := IF) (P := (specialLocalData j).TotalSpace) hp).comp
    (K := IF) (P := SpecialFullFilling j) hq

/-- The actual codomain restriction to the original small filling piece
preserves the local biholomorphism. -/
theorem ellipticLocalCover_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph IF IF ω (HolomorphicForms.EllipticCover.localCover j) :=
  isLocalDiffeomorph_codRestrictOpens IF IF (ellipticFullCover_isLocalDiffeomorph j)
    (pieceDomain specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j)
    (HolomorphicForms.EllipticCover.fullCover_mem_piece j)

/-- The genuine global elliptic cover is locally biholomorphic in the
native product and glued atlases, without removing the central fibre. -/
theorem ellipticGlobalCover_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph IF IF ω (HolomorphicForms.EllipticCover.globalCover j) := by
  intro x
  exact (ellipticLocalCover_isLocalDiffeomorph j x).comp
    (K := IF) (P := Threefold.Space)
    (EllipticGeometry.inclusion_isLocalDiffeomorph j
      (HolomorphicForms.EllipticCover.localCover j x))

/-- The actual manifold derivative, not a separately supplied coordinate
map, identifies the native tangent spaces. -/
def ellipticGlobalCoverDerivativeEquiv (j : Kind)
    (x : HolomorphicForms.EllipticCover.Cover j) :
    TangentSpace IF x ≃L[ℂ]
      TangentSpace IF (HolomorphicForms.EllipticCover.globalCover j x) :=
  (ellipticGlobalCover_isLocalDiffeomorph j x).mfderivToContinuousLinearEquiv (by simp)

@[simp] theorem ellipticGlobalCoverDerivativeEquiv_coe (j : Kind)
    (x : HolomorphicForms.EllipticCover.Cover j) :
    (ellipticGlobalCoverDerivativeEquiv j x).toContinuousLinearMap =
      mfderiv IF IF (HolomorphicForms.EllipticCover.globalCover j) x := rfl

theorem ellipticGlobalCover_mfderiv_bijective (j : Kind)
    (x : HolomorphicForms.EllipticCover.Cover j) :
    Bijective (mfderiv IF IF (HolomorphicForms.EllipticCover.globalCover j) x) :=
  (ellipticGlobalCoverDerivativeEquiv j x).bijective

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
