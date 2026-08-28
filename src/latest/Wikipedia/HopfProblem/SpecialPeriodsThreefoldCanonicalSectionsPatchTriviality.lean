import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsPatches
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsTriviality

/-!
# A genuine canonical trivialization on the first full global patch

The actual small-filling canonical trivialization and the actual bundle
and base patch biholomorphisms give a product trivialization of the
original global canonical bundle on the entire first elliptic patch.
The inverse is scalar multiplication by the actual transported section.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] specialEllipticPieceChartedSpace Threefold.chartedSpace

local instance firstPatchTrivialityGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- A genuine product trivialization of the native global bundle on the
entire first elliptic patch, with all original topologies and atlases. -/
def firstPatchTrivialization :
    Diffeomorph Iᴷ Iᴷ (Threefold.Canonical.bundlePatch (some (some .three)))
      (Threefold.liftedPatch (some (some .three)) × ℂ) ω :=
  ((Elliptic.bundleBiholomorph .three).symm.trans smallThreeTrivialization).trans
    ((EllipticGeometry.nativePatchBiholomorph .three).prodCongr (Diffeomorph.refl I₁ ℂ ω))

theorem firstPatchTrivialization_projection
    (p : Threefold.Canonical.bundlePatch (some (some .three))) :
    (firstPatchTrivialization p).1 =
      Threefold.Canonical.bundlePatchProjection (some (some .three)) p := by
  change EllipticGeometry.nativePatchBiholomorph .three
    (((Elliptic.bundleBiholomorph .three).symm p).proj) = _
  have h : ((Elliptic.bundleBiholomorph .three).symm p).proj =
      (EllipticGeometry.nativePatchBiholomorph .three).symm
        (Threefold.Canonical.bundlePatchProjection (some (some .three)) p) :=
    Threefold.Canonical.patchBundleBiholomorph_symm_proj (some (some .three)) p
  rw [h, Diffeomorph.apply_symm_apply]

/-- The inverse is precisely scalar multiplication by the actual global
patch section, not a separately chosen scalar coordinate. -/
theorem firstPatchTrivialization_symm
    (y : Threefold.liftedPatch (some (some .three))) (c : ℂ) :
    (firstPatchTrivialization.symm (y, c) : Threefold.Canonical.bundle.TotalSpace) =
      ⟨y.val, c • patchSection .three y⟩ := by
  let x := (EllipticGeometry.nativePatchBiholomorph .three).symm y
  have hb : EllipticGeometry.inclusion .three x = y.val :=
    congrArg Subtype.val ((EllipticGeometry.nativePatchBiholomorph .three).apply_symm_apply y)
  have hs : id (α := ℂ) (sectionAlongInclusion .three x) =
      id (α := ℂ) (patchSection .three y) :=
    (Pullback.fiberTransport_apply hb (sectionAlongInclusion .three x)).symm
  have hf := congrArg (id (α := ℂ))
    ((Elliptic.patchPullback .three x).symm.map_smul c (smallSection .three x))
  have hf' : id (α := ℂ) ((Elliptic.patchPullback .three x).symm
        (c • smallSection .three x)) = id (α := ℂ) (c • patchSection .three y) :=
    hf.trans (congrArg (fun a : ℂ => c * a) hs)
  change (⟨EllipticGeometry.inclusion .three x,
    (Elliptic.patchPullback .three x).symm (c • smallSection .three x)⟩ :
      Threefold.Canonical.bundle.TotalSpace) = _
  exact congrArg₂ (fun (a : Threefold.Space) (v : ℂ) =>
    (⟨a, v⟩ : Threefold.Canonical.bundle.TotalSpace)) hb hf'

theorem firstPatchTrivialization_symm_one
    (y : Threefold.liftedPatch (some (some .three))) :
    (firstPatchTrivialization.symm (y, 1) : Threefold.Canonical.bundle.TotalSpace) =
      patchSectionMap .three y := by
  rw [firstPatchTrivialization_symm, one_smul]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
