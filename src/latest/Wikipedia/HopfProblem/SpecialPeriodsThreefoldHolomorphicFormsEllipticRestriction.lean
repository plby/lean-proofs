import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticGauge
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsPullback

/-!
# Actual tangent maps of the inherited elliptic open restrictions

An open-submanifold inclusion has the identity derivative in the
inherited native tangent coordinates. This follows from the actual
restricted charts. Consequently restriction of a genuine differential
form to the punctured elliptic covering product keeps its actual
alternating covector unchanged.
-/

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The original open-submanifold inclusion is literally the identity
in the actual native tangent coordinates. -/
theorem hasMFDerivAt_openSubtypeVal (U : TopologicalSpace.Opens M) (x : U) :
    HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) (Subtype.val : U → M) x
      (ContinuousLinearMap.id ℂ E) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have he : writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E) x (Subtype.val : U → M)
      =ᶠ[𝓝 (extChartAt 𝓘(ℂ, E) x x)] id := by
    filter_upwards [(chartAt E x).open_target.mem_nhds
      ((chartAt E x).map_source (mem_chart_source E x))] with y hy
    change (chartAt E x.val) (((chartAt E x).symm y).val) = y
    exact (chartAt E x).right_inv hy
  exact ((hasFDerivAt_id (extChartAt 𝓘(ℂ, E) x x)).congr_of_eventuallyEq he).hasFDerivWithinAt

theorem mfderiv_openSubtypeVal (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (Subtype.val : U → M) x =
      ContinuousLinearMap.id ℂ E :=
  (hasMFDerivAt_openSubtypeVal U x).mfderiv

end Wikipedia.HopfProblem.HolomorphicDifferentialForms

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic EllipticFilling HolomorphicDifferentialForms

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] coverChartedSpace starCoverChartedSpace

/-- Forgetting the puncture does not alter any of the three tangent coordinates. -/
theorem mfderiv_starCoverInclusion (j : Kind) (x : CoverStar j) :
    mfderiv IF IF (starCoverInclusion j) x = ContinuousLinearMap.id ℂ FamilyModel := by
  have hval : MDifferentiableAt I₁ I₁
      (Subtype.val : RootStar j → Root j) x.1 :=
    (hasMFDerivAt_openSubtypeVal (rootStarDomain j) x.1).mdifferentiableAt
  have hid : MDifferentiableAt I₂ I₂ (id : ComplexPlane₂ → ComplexPlane₂) x.2 :=
    mdifferentiableAt_id
  have hp := mfderiv_prodMap hval hid
  rw [mfderiv_openSubtypeVal, mfderiv_id] at hp
  rw [modelWithCornersSelf_prod]
  change mfderiv ((I₁).prod I₂) ((I₁).prod I₂)
    (Prod.map (Subtype.val : RootStar j → Root j) id) x = _
  rw [hp]
  ext v <;> rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
