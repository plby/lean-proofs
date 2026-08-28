import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameCore
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrameNative

/-!
# Constructed holomorphic frames in arbitrary original native bundles on `ℂ²`

The scalar-core section is carried into the original native fibres by the
existing analytic fibre-linear identification. This yields a genuine
`ContMDiffSection`, an everywhere nonzero frame, and a fibre-linear analytic
product diffeomorphism for the original topology and atlas.
-/

noncomputable section

open Set Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

open PeriodTorusLineBundleClassificationNative PeriodTorusLineBundleClassificationFrame

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (V : ComplexPlane₂ → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V Iℂ]

/-- A genuinely constructed holomorphic section of the actual original
native bundle, not a section included among its input fields. -/
def nativeHolomorphicSection : ContMDiffSection Iℂ ℂ ω V where
  toFun x := fiberIdentification V x (coreHolomorphicSection (data V) x)
  contMDiff_toFun := (toNative_holomorphic V Iℂ).comp
    (coreHolomorphicSection (data V)).contMDiff

theorem nativeHolomorphicSection_ne_zero (x : ComplexPlane₂) :
    nativeHolomorphicSection V x ≠ 0 := by
  intro hx
  have h := (fiberIdentification V x).injective (hx.trans (map_zero _).symm)
  exact coreHolomorphicSection_ne_zero (data V) x h

/-- The actual holomorphic section is the scalar correction of the actual
original native smooth frame. -/
theorem nativeHolomorphicSection_eq_correction (x : ComplexPlane₂) :
    nativeHolomorphicSection V x = correctionFactor (data V) x • nativeFrame V x := by
  change fiberIdentification V x (coreHolomorphicSection (data V) x) = _
  rw [coreHolomorphicSection_eq_correction, map_smul]
  rfl

theorem nativeHolomorphicSection_localCoefficient (i : ComplexPlane₂) {x : ComplexPlane₂}
    (hx : x ∈ (nativeTriv V i).baseSet) :
    (nativeTriv V i (TotalSpace.mk x (nativeHolomorphicSection V x))).2 =
      correctedCoefficient (data V) i x := by
  have he := congrArg Prod.snd
    (toNative_localTriv V i ⟨x, coreHolomorphicSection (data V) x⟩ hx)
  exact he.trans (coreHolomorphicSection_localCoefficient (data V) i hx)

/-- Every arbitrary native holomorphic line bundle on `ℂ²` has an actual
holomorphic nowhere-zero section, with no triviality or solver assumption. -/
theorem exists_native_holomorphic_nonzero_section :
    ∃ s : ContMDiffSection Iℂ ℂ ω V, ∀ x, s x ≠ 0 :=
  ⟨nativeHolomorphicSection V, nativeHolomorphicSection_ne_zero V⟩

/-- The actual original native total space is analytically the product,
using the existing native-to-core identification and constructed frame. -/
def nativeProductDiffeomorph :
    Diffeomorph ((Iℂ).prod I₁) ((Iℂ).prod I₁) (TotalSpace ℂ V) (ComplexPlane₂ × ℂ) ω :=
  (identification V Iℂ).diffeomorph.symm.trans (coreAnalyticTrivialization (data V)).diffeomorph

theorem nativeProductDiffeomorph_preserves_base (v : TotalSpace ℂ V) :
    (nativeProductDiffeomorph V v).1 = v.proj :=
  (coreAnalyticTrivialization (data V)).preserves_base (fromNative V v)

theorem nativeProductDiffeomorph_add (x : ComplexPlane₂) (v w : V x) :
    (nativeProductDiffeomorph V ⟨x, v + w⟩).2 =
      (nativeProductDiffeomorph V ⟨x, v⟩).2 +
        (nativeProductDiffeomorph V ⟨x, w⟩).2 := by
  change ((coreAnalyticTrivialization (data V)).diffeomorph
    ⟨x, (fiberIdentification V x).symm (v + w)⟩).2 = _
  rw [map_add]
  exact (coreAnalyticTrivialization (data V)).map_add x _ _

theorem nativeProductDiffeomorph_smul (x : ComplexPlane₂) (c : ℂ) (v : V x) :
    (nativeProductDiffeomorph V ⟨x, c • v⟩).2 =
      c • (nativeProductDiffeomorph V ⟨x, v⟩).2 := by
  change ((coreAnalyticTrivialization (data V)).diffeomorph
    ⟨x, (fiberIdentification V x).symm (c • v)⟩).2 = _
  rw [map_smul]
  exact (coreAnalyticTrivialization (data V)).map_smul x c _

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame
