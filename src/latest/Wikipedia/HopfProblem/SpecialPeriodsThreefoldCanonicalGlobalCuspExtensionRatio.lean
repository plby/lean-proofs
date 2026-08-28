import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtensionRatioBasic

/-!
# A genuine holomorphic canonical ratio on the entire punctured cusp patch

The regular section is pulled into the original native cusp canonical
bundle by the proved bundle biholomorphism. Its coefficient in the actual
native volume trivialization defines the ratio. Thus holomorphicity is a
statement about the unchanged canonical bundle topology and charts, not
an assumption about division of scalar representatives of its fibres.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension

open ToricCharts CuspGeometry HolomorphicForms.Cusp

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance ratioNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance ratioGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The actual regular canonical section restricted to the full cusp-patch total space. -/
def globalSectionInPatch (y : puncturedNative) : Cusp.FullPatchTotalSpace :=
  ⟨GlobalRegular.globalSectionMap (puncturedRegularPoint y),
    (CuspGeometry.nativePatchBiholomorph y.val).property⟩

@[simp] theorem globalSectionInPatch_val (y : puncturedNative) :
    (globalSectionInPatch y).val = GlobalRegular.globalSectionMap (puncturedRegularPoint y) :=
  rfl

theorem globalSectionInPatch_holomorphic :
    ContMDiff I₃ ((IF).prod I₁) ω globalSectionInPatch := by
  have hh := GlobalRegular.globalSectionMap_holomorphic.comp puncturedRegularPoint_holomorphic
  intro y
  have he : ContMDiffAt I₃ ((IF).prod I₁) ω (Subtype.val ∘ globalSectionInPatch) y ↔
      ContMDiffAt I₃ ((IF).prod I₁) ω globalSectionInPatch y :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hh y)

/-- Genuine inverse differential transport into the native cusp canonical bundle. -/
def nativeSectionMap (y : puncturedNative) : Cusp.nativeBundle.TotalSpace :=
  Cusp.nativePatchTotalBiholomorph.symm (globalSectionInPatch y)

theorem nativeSectionMap_holomorphic :
    ContMDiff I₃ ((I₃).prod I₁) ω nativeSectionMap :=
  Cusp.nativePatchTotalBiholomorph.symm.contMDiff.comp globalSectionInPatch_holomorphic

/-- The transported vector is the actual differential pullback at the same native point. -/
theorem nativeSectionMap_eq (y : puncturedNative) :
    nativeSectionMap y =
      ⟨y.val, Cusp.inclusionPullback y.val
        (GlobalRegular.globalSection (puncturedRegularPoint y))⟩ := by
  apply Cusp.nativePatchTotalBiholomorph.injective
  change Cusp.nativePatchTotalBiholomorph
      (Cusp.nativePatchTotalBiholomorph.symm (globalSectionInPatch y)) = _
  rw [Cusp.nativePatchTotalBiholomorph.apply_symm_apply]
  apply Subtype.ext
  change (⟨CuspGeometry.inclusion y.val,
      GlobalRegular.globalSection (puncturedRegularPoint y)⟩ : bundle.TotalSpace) =
    ⟨CuspGeometry.inclusion y.val, (Cusp.inclusionPullback y.val).symm
      (Cusp.inclusionPullback y.val (GlobalRegular.globalSection (puncturedRegularPoint y)))⟩
  exact congrArg (fun v : bundle.Fiber (CuspGeometry.inclusion y.val) =>
    (⟨CuspGeometry.inclusion y.val, v⟩ : bundle.TotalSpace))
      ((Cusp.inclusionPullback y.val).symm_apply_apply
        (GlobalRegular.globalSection (puncturedRegularPoint y))).symm

/-- Coefficient in the original signed native volume trivialization. -/
def rawRatio (y : puncturedNative) : ℂ := Cusp.nativeVolumeCoordinate (nativeSectionMap y)

theorem rawRatio_holomorphic : ContMDiff I₃ I₁ ω rawRatio :=
  Cusp.nativeVolumeCoordinate_holomorphic.comp nativeSectionMap_holomorphic

theorem rawRatio_eq_nativeCoordinate (y : puncturedNative) :
    rawRatio y = Cusp.nativeVolumeCoordinate
      ⟨y.val, Cusp.inclusionPullback y.val
        (GlobalRegular.globalSection (puncturedRegularPoint y))⟩ :=
  congrArg Cusp.nativeVolumeCoordinate (nativeSectionMap_eq y)

/-- Equality in the genuine global canonical fibre over the original cusp inclusion. -/
theorem globalSection_eq_rawRatio_smul (y : puncturedNative) :
    GlobalRegular.globalSection (puncturedRegularPoint y) =
      rawRatio y • Cusp.volumeAlongInclusion y.val := by
  change id (α := ℂ) (GlobalRegular.globalSection (puncturedRegularPoint y)) =
    rawRatio y * id (α := ℂ) (Cusp.volumeAlongInclusion y.val)
  rw [rawRatio_eq_nativeCoordinate]
  calc
    _ = id (α := ℂ) ((Cusp.inclusionPullback y.val).symm
        (Cusp.inclusionPullback y.val
          (GlobalRegular.globalSection (puncturedRegularPoint y)))) :=
      ((Cusp.inclusionPullback y.val).symm_apply_apply _).symm
    _ = Cusp.nativeVolumeCoordinate
        ⟨y.val, Cusp.inclusionPullback y.val
          (GlobalRegular.globalSection (puncturedRegularPoint y))⟩ •
            id (α := ℂ) (Cusp.volumeAlongInclusion y.val) :=
      Cusp.inclusionPushforward_eq_volumeCoordinate y.val _

theorem rawRatio_ne_zero (y : puncturedNative) : rawRatio y ≠ 0 := by
  intro hzero
  have hs := globalSection_eq_rawRatio_smul y
  rw [hzero, zero_smul] at hs
  exact GlobalRegular.globalSection_ne_zero (puncturedRegularPoint y) hs

/-- A fibre equality with the nonzero original cusp volume determines this ratio uniquely. -/
theorem rawRatio_eq_of_eq_smul (y : puncturedNative) (c : ℂ)
    (hc : GlobalRegular.globalSection (puncturedRegularPoint y) =
      c • Cusp.volumeAlongInclusion y.val) : rawRatio y = c := by
  apply mul_right_cancel₀
    (show id (α := ℂ) (Cusp.volumeAlongInclusion y.val) ≠ 0 from
      Cusp.volumeAlongInclusion_ne_zero y.val)
  exact (globalSection_eq_rawRatio_smul y).symm.trans hc

/-- On the original logarithmic cover the ratio is exactly the previously computed scalar. -/
theorem rawRatio_logarithmic (x : LogDomain) :
    rawRatio (logPoint x) = GlobalCuspPullback.regularToCuspFactor x := by
  apply rawRatio_eq_of_eq_smul
  change id (α := ℂ) (GlobalRegular.globalSection (puncturedRegularPoint (logPoint x))) =
    GlobalCuspPullback.regularToCuspFactor x *
      id (α := ℂ) (Cusp.volumeAlongInclusion (localLogMap x))
  rw [puncturedRegularPoint_logPoint]
  exact GlobalCuspPullback.globalSection_eq_factor_smul_cuspVolume x

/-- Multiplication by the actual reciprocal sphere parameter normalizes the genuine ratio. -/
def normalizedRatio (y : puncturedNative) : ℂ := reciprocalParameter y * rawRatio y

theorem normalizedRatio_holomorphic : ContMDiff I₃ I₁ ω normalizedRatio :=
  reciprocalParameter_holomorphic.mul rawRatio_holomorphic

theorem normalizedRatio_ne_zero (y : puncturedNative) : normalizedRatio y ≠ 0 :=
  mul_ne_zero (reciprocalParameter_ne_zero y) (rawRatio_ne_zero y)

theorem normalizedRatio_logarithmic (x : LogDomain) :
    normalizedRatio (logPoint x) =
      GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere (globalLogMap x)) *
        GlobalCuspPullback.regularToCuspFactor x := by
  rw [normalizedRatio, reciprocalParameter_logarithmic, rawRatio_logarithmic]

/-- The normalized section equality still concerns the actual canonical fibre. -/
theorem reciprocal_smul_globalSection (y : puncturedNative) :
    reciprocalParameter y • GlobalRegular.globalSection (puncturedRegularPoint y) =
      normalizedRatio y • Cusp.volumeAlongInclusion y.val := by
  change reciprocalParameter y *
    id (α := ℂ) (GlobalRegular.globalSection (puncturedRegularPoint y)) =
      normalizedRatio y * id (α := ℂ) (Cusp.volumeAlongInclusion y.val)
  have hs : id (α := ℂ) (GlobalRegular.globalSection (puncturedRegularPoint y)) =
      rawRatio y * id (α := ℂ) (Cusp.volumeAlongInclusion y.val) :=
    globalSection_eq_rawRatio_smul y
  rw [hs, normalizedRatio, mul_assoc]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension
