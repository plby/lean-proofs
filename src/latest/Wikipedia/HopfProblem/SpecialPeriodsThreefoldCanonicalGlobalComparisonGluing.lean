import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalNativeCanonical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleLocalGluing
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMaps

/-!
# Gluing genuine local maps between the two fixed global bundles

This specializes native cross-cover gauge gluing to the already
constructed divisor line and the original tangent-canonical line of the
actual threefold.  The hypotheses below are local map holomorphicity and
literal equality of fibre maps on the three actual coarse overlaps.
The geometric local maps discharge these hypotheses separately.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparison

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

/-- The independently constructed divisor/twist cocycle. -/
abbrev sourceTransitions := GlobalPrescribedDivisor.cartier.transitions

/-- The actual native inverse-Jacobian cocycle, with its proved intrinsic identification. -/
abbrev targetTransitions := NativePresentation.transitionData

variable (h : Patch → Threefold.Space → ℂˣ)
  (hhol : ∀ k, ContMDiffOn Iκ Iκ ω
    (OpenMaps.preferredMap sourceTransitions targetTransitions (h k))
    ((Bundle.TotalSpace.proj : sourceTransitions.core.TotalSpace → Threefold.Space) ⁻¹'
      (cover k : Set Threefold.Space)))
  (hagree : ∀ k l x, x ∈ cover k → x ∈ cover l → h k x = h l x)

/-- Actual local bundle maps supply the units; the original cocycles
prove their transition compatibility automatically. -/
def glueLocalMaps : LocalCrossGauge IF sourceTransitions targetTransitions Patch where
  cover := cover
  indexAt := indexAt
  mem_cover := mem_cover_at
  value k := OpenMaps.chartUnit sourceTransitions targetTransitions (h k)
  holomorphicOn k :=
    OpenMaps.chartUnit_holomorphicOn sourceTransitions targetTransitions (h k) IF
      (cover k) (hhol k)
  agreement k l i x _ hk hl :=
    OpenMaps.chartUnit_eq_of_multiplier_eq sourceTransitions targetTransitions (h k) i
      (hagree k l x hk hl)
  compatible k i j x hx _ :=
    OpenMaps.chartUnit_compatible sourceTransitions targetTransitions (h k) i j x hx

/-- In the actual preferred source and target charts, the global
comparison recovers the precise local fibre multiplier on every coarse open. -/
theorem glueLocalMaps_preferred_value (k : Patch) {x : Threefold.Space} (hx : x ∈ cover k) :
    (glueLocalMaps h hhol hagree).toCrossGauge.value
        (sourceTransitions.indexAt x, targetTransitions.indexAt x) x = h k x := by
  have he := (glueLocalMaps h hhol hagree).toCrossGauge_value_of_mem k
    (sourceTransitions.indexAt x, targetTransitions.indexAt x)
    ⟨sourceTransitions.mem_baseSet_at x, targetTransitions.mem_baseSet_at x⟩ hx
  refine he.trans ?_
  change targetTransitions.transition (targetTransitions.indexAt x)
      (targetTransitions.indexAt x) x * h k x *
      sourceTransitions.transition (sourceTransitions.indexAt x)
        (sourceTransitions.indexAt x) x = h k x
  rw [targetTransitions.transition_self _ _ (targetTransitions.mem_baseSet_at x),
    sourceTransitions.transition_self _ _ (sourceTransitions.mem_baseSet_at x), one_mul, mul_one]

theorem glueLocalMaps_fiberEquiv_apply (k : Patch) {x : Threefold.Space}
    (hx : x ∈ cover k) (v : sourceTransitions.core.Fiber x) :
    (glueLocalMaps h hhol hagree).toCrossGauge.fiberEquiv x v =
      (h k x : ℂ) * id (α := ℂ) v := by
  rw [CrossGauge.fiberEquiv_apply, glueLocalMaps_preferred_value h hhol hagree k hx]

/-- The actual global biholomorphism agrees with every given local
native total-space map on its entire original coarse open. -/
theorem glueLocalMaps_diffeomorph_eq (k : Patch) (p : sourceTransitions.core.TotalSpace)
    (hp : p.proj ∈ cover k) :
    (glueLocalMaps h hhol hagree).toCrossGauge.diffeomorph p =
      OpenMaps.preferredMap sourceTransitions targetTransitions (h k) p := by
  cases p with
  | mk x v =>
    exact congrArg (fun w : targetTransitions.core.Fiber x =>
      (⟨x, w⟩ : targetTransitions.core.TotalSpace))
      (glueLocalMaps_fiberEquiv_apply h hhol hagree k hp v)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparison
