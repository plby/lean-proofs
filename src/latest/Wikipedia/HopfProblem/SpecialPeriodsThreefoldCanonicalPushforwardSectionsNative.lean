import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalBundle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDirectImage

/-!
# Original canonical sections on actual threefold and base opens

These section types use the original alternating-cotangent canonical
bundle of the constructed threefold. Sections over a base open are
sections on its full actual inverse image under the sphere projection.
The scalar direct-image section type remains a separate function type.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

/-- Actual holomorphic sections of the original canonical bundle on an open. -/
abbrev Section (V : Opens Threefold.Space) :=
  NativeBundleSections.Section Threefold.Canonical.bundle IF V

/-- Actual canonical sections over the full inverse image of a sphere open. -/
abbrev PreimageSection (U : Opens RiemannSphere) := Section (Threefold.basePreimage U)

/-- The section's literal map into the original canonical total space. -/
def sectionMap {V : Opens Threefold.Space} (s : Section V) (x : V) :
    Threefold.Canonical.bundle.TotalSpace := ⟨(x : Threefold.Space), s x⟩

theorem sectionMap_holomorphic {V : Opens Threefold.Space} (s : Section V) :
    ContMDiff IF Iκ ω (sectionMap s) := s.contMDiff_toFun

@[simp] theorem sectionMap_proj {V : Opens Threefold.Space} (s : Section V) (x : V) :
    (sectionMap s x).proj = (x : Threefold.Space) := rfl

theorem section_ext {V : Opens Threefold.Space} {s t : Section V}
    (h : ∀ x, s x = t x) : s = t :=
  NativeBundleSections.Section.ext Threefold.Canonical.bundle IF h

/-- Literal restriction in the original canonical fibres. -/
def restrictSection {V W : Opens Threefold.Space} (h : V ≤ W) (s : Section W) : Section V :=
  NativeBundleSections.Section.restrict Threefold.Canonical.bundle IF h s

@[simp] theorem restrictSection_apply {V W : Opens Threefold.Space} (h : V ≤ W)
    (s : Section W) (x : V) : restrictSection h s x = s ⟨x.val, h x.property⟩ := rfl

@[simp] theorem restrictSection_refl {V : Opens Threefold.Space} (s : Section V) :
    restrictSection le_rfl s = s :=
  NativeBundleSections.Section.restrict_refl Threefold.Canonical.bundle IF s

@[simp] theorem restrictSection_restrict {U V W : Opens Threefold.Space}
    (hUV : U ≤ V) (hVW : V ≤ W) (s : Section W) :
    restrictSection hUV (restrictSection hVW s) = restrictSection (hUV.trans hVW) s :=
  NativeBundleSections.Section.restrict_restrict Threefold.Canonical.bundle IF hUV hVW s

/-- Base-open restriction is restriction to the literal full preimage. -/
def restrictPreimageSection {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) : PreimageSection U :=
  restrictSection (Threefold.basePreimage_mono h) s

@[simp] theorem restrictPreimageSection_apply {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) (x : Threefold.basePreimage U) :
    restrictPreimageSection h s x = s ⟨x.val, h x.property⟩ := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward
