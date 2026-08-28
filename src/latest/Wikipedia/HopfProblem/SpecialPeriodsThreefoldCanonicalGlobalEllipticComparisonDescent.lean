import
  Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonDescentCovariance
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsSpecial

/-!
# The comparison unit on the actual elliptic fillings

The invariant unit descends through the original finite affine quotient.
Its holomorphicity is proved in the original filling atlas, and its exact
pullback is the already constructed disc ratio.  In particular this is a
nowhere-zero holomorphic function on the entire full filling, not merely
a prescribed germ or a function on a substitute quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace

local instance specialUpstairsChartedSpace (j : Kind) :
    ChartedSpace Model (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalChartedSpace

local instance specialUpstairsManifold (j : Kind) :
    IsManifold I₃ ω (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalSpace_isManifold

local instance discLocallyCompact : LocallyCompactSpace Disc :=
  unitDisc.isOpen.locallyCompactSpace

/-- The actual quotient lift of the already extended disc comparison unit. -/
def fullRatio (j : Kind) : SpecialFullFilling j → ℂ := by
  letI := (specialLocalData j).action j.twist (mainTwist_admissible j).1
  exact FiniteQuotient.descend (fun x : (specialLocalData j).TotalSpace => ratio j x.1)
    (ratio_action j)

/-- Exact recovery along the original finite quotient map. -/
@[simp] theorem fullRatio_fullQuotient (j : Kind) (x : (specialLocalData j).TotalSpace) :
    fullRatio j (Sections.fullQuotient j x) = ratio j x.1 := rfl

/-- The descended function is holomorphic for the original complex
structure selected from the actual varying-period family. -/
theorem fullRatio_holomorphic (j : Kind) : ContMDiff I₃ I₁ ω (fullRatio j) := by
  let := (specialLocalData j).periods.totalChartedSpace
  let := (specialLocalData j).periods.totalSpace_isManifold
  let := (specialLocalData j).action j.twist (mainTwist_admissible j).1
  let := (specialLocalData j).action_continuous j.twist (mainTwist_admissible j).1
  let := (specialLocalData j).action_free j.twist (mainTwist_admissible j)
  have hh : ContMDiff I₃ I₁ ω
      (fun x : (specialLocalData j).TotalSpace => ratio j x.1) :=
    (ratio_holomorphic j).comp (specialLocalData j).periods.projection_holomorphic
  have h := FiniteQuotient.descend_holomorphic (E := Model)
    (fun x : (specialLocalData j).TotalSpace => ratio j x.1) (ratio_action j) I₁ hh
  exact h

theorem fullRatio_ne_zero (j : Kind) (y : SpecialFullFilling j) : fullRatio j y ≠ 0 := by
  obtain ⟨x, rfl⟩ := Sections.fullQuotient_surjective j y
  exact ratio_ne_zero j x.1

/-- Recovery by the actual quotient determines the comparison function uniquely. -/
theorem fullRatio_unique (j : Kind) (f : SpecialFullFilling j → ℂ)
    (hf : ∀ x, f (Sections.fullQuotient j x) = ratio j x.1) : f = fullRatio j := by
  funext y
  obtain ⟨x, rfl⟩ := Sections.fullQuotient_surjective j y
  exact hf x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
