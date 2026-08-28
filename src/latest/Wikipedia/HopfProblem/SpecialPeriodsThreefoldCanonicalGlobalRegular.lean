import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularCoefficient

/-!
# The actual regular canonical form `dt ∧ e / F`

The differential of the actual affine sphere coordinate and the actual
modular generator define a holomorphic nowhere-zero three-form on the
original regular varying-period family.  Its proved differential
invariance gives a genuine section of the original regular canonical
bundle, and the actual inclusion transports it to the global canonical
bundle on the entire regular locus.  Every scalar covariance, covering,
holomorphicity and nonvanishing assertion used here has been proved for
the constructed special periods; none is an additional hypothesis.

Extension across the filling patches is not asserted in this file.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace specialRegularFamilyChartedSpace

local instance regularFormUpstairsChartedSpace : ChartedSpace Model SpecialRegularUpstairs :=
  specialRegularData.periods.totalChartedSpace

local instance regularFormUpstairsManifold : IsManifold I₃ ω SpecialRegularUpstairs :=
  specialRegularData.periods.totalSpace_isManifold

local instance regularFormNativeManifold : IsManifold I₃ ω Threefold.SpecialRegularFamily :=
  specialRegularFamily_isManifold

local instance regularFormGlobalManifold : IsManifold I₃ ω Threefold.Space :=
  Threefold.space_isManifold

/-- The genuine upstairs form `(dt/dz)/F` times the native volume. -/
def upstairsSection (x : SpecialRegularUpstairs) : specialUpstairsCanonicalBundle.Fiber x :=
  upstairsWeightedSection regularCoefficient x

def upstairsSectionMap : SpecialRegularUpstairs → specialUpstairsCanonicalBundle.TotalSpace :=
  upstairsWeightedSectionMap regularCoefficient

theorem upstairsSection_formula (x : SpecialRegularUpstairs) :
    upstairsSection x =
      (deriv (upstairsCoordinate ∘ (chartAt ℂ x.1).symm) (x.1.val : ℂ) /
        GlobalGenerator.generator x.1.val) • specialUpstairsCanonicalVolume x := rfl

theorem upstairsSection_ne_zero (x : SpecialRegularUpstairs) : upstairsSection x ≠ 0 :=
  (upstairsWeightedSection_ne_zero_iff regularCoefficient x).mpr
    (regularCoefficient_ne_zero x.1)

theorem upstairsSectionMap_holomorphic : ContMDiff I₃ Iᴷ ω upstairsSectionMap :=
  upstairsWeightedSectionMap_holomorphic regularCoefficient regularCoefficient_holomorphic

def upstairsHolomorphicSection :
    ContMDiffSection I₃ ℂ ω specialUpstairsCanonicalBundle.Fiber :=
  upstairsWeightedHolomorphicSection regularCoefficient regularCoefficient_holomorphic

@[simp] theorem upstairsHolomorphicSection_apply (x : SpecialRegularUpstairs) :
    upstairsHolomorphicSection x = upstairsSection x := rfl

/-- This is a full alternating three-covector on the actual tangent space. -/
theorem upstairsSection_intrinsic (x : SpecialRegularUpstairs) :
    familyCanonicalIntrinsicEquiv specialRegularData.periods x (upstairsSection x) =
      regularCoefficient x.1 • volume := by
  change familyCanonicalIntrinsicEquiv specialRegularData.periods x
    (regularCoefficient x.1 • familyCanonicalVolume specialRegularData.periods x) = _
  rw [map_smul, familyCanonicalIntrinsicEquiv_volume]
  rfl

theorem upstairsSection_invariant (g : TriangleGroup) (x : SpecialRegularUpstairs) :
    Pullback.pullbackLinear (familyMap specialRegularData g) x
      (upstairsSection (familyMap specialRegularData g x)) = upstairsSection x :=
  regularCoefficient_invariant g x

/-- The descended form in the already constructed native regular canonical bundle. -/
def regularSection (x : Threefold.SpecialRegularFamily) : Regular.bundle.Fiber x :=
  descendedWeightedSection regularCoefficient x

def regularSectionMap : Threefold.SpecialRegularFamily → Regular.bundle.TotalSpace :=
  descendedWeightedSectionMap regularCoefficient

@[simp] theorem regularSectionMap_proj (x : Threefold.SpecialRegularFamily) :
    (regularSectionMap x).proj = x := rfl

theorem regularSectionMap_holomorphic : ContMDiff I₃ Iᴷ ω regularSectionMap :=
  descendedWeightedSectionMap_holomorphic regularCoefficient regularCoefficient_holomorphic
    regularCoefficient_invariant

def regularHolomorphicSection : ContMDiffSection I₃ ℂ ω Regular.bundle.Fiber :=
  descendedWeightedHolomorphicSection regularCoefficient regularCoefficient_holomorphic
    regularCoefficient_invariant

@[simp] theorem regularHolomorphicSection_apply (x : Threefold.SpecialRegularFamily) :
    regularHolomorphicSection x = regularSection x := rfl

theorem regularSection_ne_zero (x : Threefold.SpecialRegularFamily) : regularSection x ≠ 0 :=
  descendedWeightedSection_ne_zero regularCoefficient regularCoefficient_invariant
    regularCoefficient_ne_zero x

/-- Pullback by the actual triangle quotient recovers `dt ∧ e/F` exactly. -/
theorem regularSection_pullback (x : SpecialRegularUpstairs) :
    Pullback.pullbackEquiv familyQuotient_isLocalDiffeomorph x
      (regularSection (familyQuotient x)) = upstairsSection x :=
  descendedWeightedSection_pullback regularCoefficient regularCoefficient_invariant x

theorem regularSection_unique
    (s : ∀ x : Threefold.SpecialRegularFamily, Regular.bundle.Fiber x)
    (hs : ∀ x, Pullback.pullbackEquiv familyQuotient_isLocalDiffeomorph x
      (s (familyQuotient x)) = upstairsSection x) : s = regularSection :=
  descendedWeightedSection_unique regularCoefficient regularCoefficient_invariant s hs

/-- The actual global canonical form on the full regular open locus. -/
def globalSection (y : regularLocus) : Threefold.Canonical.bundle.Fiber y.val :=
  globalWeightedSection regularCoefficient y

def globalSectionMap : regularLocus → Threefold.Canonical.bundle.TotalSpace :=
  globalWeightedSectionMap regularCoefficient

@[simp] theorem globalSectionMap_proj (y : regularLocus) :
    (globalSectionMap y).proj = y.val := rfl

theorem globalSectionMap_holomorphic : ContMDiff I₃ Iᴷ ω globalSectionMap :=
  globalWeightedSectionMap_holomorphic regularCoefficient regularCoefficient_holomorphic
    regularCoefficient_invariant

theorem globalSection_ne_zero (y : regularLocus) : globalSection y ≠ 0 :=
  globalWeightedSection_ne_zero regularCoefficient regularCoefficient_invariant
    regularCoefficient_ne_zero y

theorem globalSection_pullback (x : Threefold.SpecialRegularFamily) :
    Regular.pullbackEquiv x (globalSection (regularFamilyBiholomorph x)) = regularSection x :=
  globalWeightedSection_pullback regularCoefficient x

/-- The original upstairs family mapped into the actual global threefold. -/
def upstairsGlobalMap : SpecialRegularUpstairs → Threefold.Space :=
  regularFamilyInclusion ∘ familyQuotient

theorem upstairsGlobalMap_isLocalDiffeomorph :
    IsLocalDiffeomorph I₃ I₃ ω upstairsGlobalMap := by
  intro x
  exact (familyQuotient_isLocalDiffeomorph x).comp (K := I₃) (P := Threefold.Space)
    (regularFamilyInclusion_isLocalDiffeomorph (familyQuotient x))

/-- Exact recovery by the single actual upstairs-to-global differential. -/
theorem globalSection_pullback_to_upstairs (x : SpecialRegularUpstairs) :
    Pullback.pullbackEquiv upstairsGlobalMap_isLocalDiffeomorph x
      (globalSection (regularFamilyBiholomorph (familyQuotient x))) = upstairsSection x := by
  calc
    _ = Pullback.pullbackEquiv familyQuotient_isLocalDiffeomorph x
        (Regular.pullbackEquiv (familyQuotient x)
          (globalSection (regularFamilyBiholomorph (familyQuotient x)))) :=
      Pullback.pullbackEquiv_comp familyQuotient_isLocalDiffeomorph
        regularFamilyInclusion_isLocalDiffeomorph x _
    _ = Pullback.pullbackEquiv familyQuotient_isLocalDiffeomorph x
        (regularSection (familyQuotient x)) :=
      congrArg (Pullback.pullbackEquiv familyQuotient_isLocalDiffeomorph x)
        (globalSection_pullback (familyQuotient x))
    _ = upstairsSection x := regularSection_pullback x

/-- The global form has the asserted actual tangent-covector pullback. -/
theorem globalSection_intrinsic_pullback (x : SpecialRegularUpstairs) :
    (Threefold.Canonical.intrinsicEquiv (upstairsGlobalMap x)
      (globalSection (regularFamilyBiholomorph (familyQuotient x)))).compContinuousLinearMap
        (mfderiv I₃ I₃ upstairsGlobalMap x) = regularCoefficient x.1 • volume := by
  have h := congrArg (Atlas.intrinsicEquiv SpecialRegularUpstairs x)
    (globalSection_pullback_to_upstairs x)
  exact (Pullback.intrinsic_pullbackEquiv upstairsGlobalMap_isLocalDiffeomorph x
    (globalSection (regularFamilyBiholomorph (familyQuotient x)))).symm.trans
      (h.trans (upstairsSection_intrinsic x))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
