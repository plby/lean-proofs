import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticBaseChange
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobian
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsPatches

/-!
# The original elliptic covering maps and their native differentials

The actual root cover is locally biholomorphic also over the central fibre.
Its open restriction does not alter tangent coordinates, and the genuine
base change scales a full alternating three-covector by the native base
Jacobian.  No extension of the regular canonical form is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical
open HolomorphicForms.EllipticCover

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] coverChartedSpace starCoverChartedSpace cover_isManifold
  starCover_isManifold Threefold.chartedSpace Threefold.space_isManifold
  specialFullFillingChartedSpace specialEllipticPieceChartedSpace

local instance discProductChartedSpace : ChartedSpace Model (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

local instance discProductManifold : IsManifold I₃ ω (Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) Disc ComplexPlane₂

/-- The actual radius restriction is an open local biholomorphism. -/
theorem coverToPeriod_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph I₃ I₃ ω (coverToPeriod j) := by
  let e := opensInclusionPartialDiffeomorph I₁ (rootDomain j) ⟨rootZero j⟩
  let p : PartialDiffeomorph ((I₁).prod I₂) ((I₁).prod I₂)
      (Cover j) (Disc × ComplexPlane₂) ω :=
    { toFun := fun x => (e x.1, x.2)
      invFun := fun x => (e.symm x.1, x.2)
      source := e.source ×ˢ univ
      target := e.target ×ˢ univ
      map_source' := fun _ h => ⟨e.map_source h.1, mem_univ _⟩
      map_target' := fun _ h => ⟨e.map_target h.1, mem_univ _⟩
      left_inv' := fun _ h => Prod.ext (e.left_inv h.1) rfl
      right_inv' := fun _ h => Prod.ext (e.right_inv h.1) rfl
      open_source := e.open_source.prod isOpen_univ
      open_target := e.open_target.prod isOpen_univ
      contMDiffOn_toFun :=
        (e.contMDiffOn_toFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk
          contMDiffOn_snd
      contMDiffOn_invFun :=
        (e.contMDiffOn_invFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk
          contMDiffOn_snd }
  rw [modelWithCornersSelf_prod]
  intro x
  refine ⟨p, ⟨mem_univ _, mem_univ _⟩, ?_⟩
  intro y _
  rfl

/-- All three original tangent coordinates survive the open restriction unchanged. -/
theorem coverToPeriod_mfderiv (j : Kind) (x : Cover j) :
    mfderiv I₃ I₃ (coverToPeriod j) x = ContinuousLinearMap.id ℂ Model := by
  have hv : MDifferentiableAt I₁ I₁ (Subtype.val : Root j → Disc) x.1 :=
    (HolomorphicDifferentialForms.hasMFDerivAt_openSubtypeVal
      (rootDomain j) x.1).mdifferentiableAt
  have hi : MDifferentiableAt I₂ I₂ (id : ComplexPlane₂ → ComplexPlane₂) x.2 :=
    mdifferentiableAt_id
  have hp := mfderiv_prodMap hv hi
  rw [HolomorphicDifferentialForms.mfderiv_openSubtypeVal, mfderiv_id] at hp
  rw [modelWithCornersSelf_prod]
  change mfderiv ((I₁).prod I₂) ((I₁).prod I₂)
    (Prod.map (Subtype.val : Root j → Disc) id) x = _
  exact hp.trans (by ext v <;> rfl)

/-- The full actual affine quotient is unramified on the original root cover. -/
theorem fullCover_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph I₃ I₃ ω (fullCover j) := by
  let P := (specialLocalData j).periods
  let := P.totalChartedSpace
  let := P.coveringAction
  have hq : IsLocalDiffeomorph I₃ I₃ ω P.quotientMap :=
    CoveringQuotient.project_isLocalDiffeomorph P.quotientCoveringMap
      P.coveringAction_holomorphic
  intro x
  exact (coverToPeriod_isLocalDiffeomorph j x).comp (K := I₃)
    (P := SpecialFullFilling j)
    ((hq (coverToPeriod j x)).comp (K := I₃) (P := SpecialFullFilling j)
      (Sections.fullQuotient_isLocalDiffeomorph j (P.quotientMap (coverToPeriod j x))))

/-- Codomain restriction retains the actual locally biholomorphic root cover. -/
theorem localCover_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph I₃ I₃ ω (localCover j) :=
  isLocalDiffeomorph_codRestrictOpens I₃ I₃ (fullCover_isLocalDiffeomorph j)
    (pieceDomain specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j) (fullCover_mem_piece j)

/-- In particular the actual map into the global threefold is unramified everywhere. -/
theorem globalCover_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph I₃ I₃ ω (globalCover j) := by
  intro x
  exact (localCover_isLocalDiffeomorph j x).comp (K := I₃) (P := Threefold.Space)
    (EllipticGeometry.inclusion_isLocalDiffeomorph j (localCover j x))

/-- The actual differential gives the inverse used for fibrewise comparisons. -/
def globalCoverDerivativeEquiv (j : Kind) (x : Cover j) : Model ≃L[ℂ] Model :=
  (globalCover_isLocalDiffeomorph j x).mfderivToContinuousLinearEquiv (by simp)

@[simp] theorem globalCoverDerivativeEquiv_toContinuousLinearMap (j : Kind)
    (x : Cover j) :
    (globalCoverDerivativeEquiv j x : Model →L[ℂ] Model) =
      mfderiv I₃ I₃ (globalCover j) x := rfl

/-- The existing actual base-change differential is the block map with identity fibre part. -/
theorem baseChange_eq_blockDerivative (c : ℂ) :
    HolomorphicDifferentialForms.Coordinates.EllipticBaseChange.baseChange c =
      blockDerivative c 0 1 := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [HolomorphicDifferentialForms.Coordinates.EllipticBaseChange.baseChange_apply,
    blockDerivative_apply, smul_zero, Matrix.one_mulVec, zero_add]

/-- Equality of full alternating covectors, not only an evaluation coefficient. -/
theorem topCovector_baseChange (α : TopCovector) (c : ℂ) :
    α.compContinuousLinearMap
      (HolomorphicDifferentialForms.Coordinates.EllipticBaseChange.baseChange c) = c • α := by
  rw [baseChange_eq_blockDerivative, pullback_blockDerivative, Matrix.det_one, mul_one]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
