import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPatchesHolomorphic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticCoordinates

/-!
# Native regular and elliptic canonical bundles over the full global patches

These are actual biholomorphisms of the previously constructed bundle
total spaces with the natural full open restrictions of the global
canonical bundle.  They preserve the actual base identifications and
are fibrewise inverse pullback by the actual inclusion derivative.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace specialRegularFamilyChartedSpace
  specialEllipticPieceChartedSpace

namespace Regular

/-- The earlier native regular canonical bundle is holomorphically
identified with the entire global regular restriction. -/
def bundleBiholomorph :
    Diffeomorph ((IF).prod I₁) ((IF).prod I₁)
      bundle.TotalSpace (Threefold.Canonical.bundlePatch none) ω :=
  Threefold.Canonical.patchBundleBiholomorph none

@[simp] theorem bundleBiholomorph_val (p : bundle.TotalSpace) :
    (bundleBiholomorph p : Threefold.Canonical.bundle.TotalSpace) = pushforward p := rfl

theorem bundleBiholomorph_projection (p : bundle.TotalSpace) :
    Threefold.Canonical.bundlePatchProjection none (bundleBiholomorph p) =
      regularFamilyBiholomorph p.proj := Subtype.ext rfl

end Regular

namespace Elliptic

open Wikipedia.HopfProblem.Elliptic

/-- The native ambient canonical bundle of each actual small elliptic
filling is biholomorphic to the full corresponding global restriction. -/
def bundleBiholomorph (j : Kind) :
    Diffeomorph ((IF).prod I₁) ((IF).prod I₁)
      (bundle j).TotalSpace (Threefold.Canonical.bundlePatch (some (some j))) ω :=
  Threefold.Canonical.patchBundleBiholomorph (some (some j))

@[simp] theorem bundleBiholomorph_val (j : Kind) (p : (bundle j).TotalSpace) :
    (bundleBiholomorph j p : Threefold.Canonical.bundle.TotalSpace) =
      ⟨EllipticGeometry.inclusion j p.proj, (patchPullback j p.proj).symm p.2⟩ := rfl

theorem bundleBiholomorph_projection (j : Kind) (p : (bundle j).TotalSpace) :
    Threefold.Canonical.bundlePatchProjection (some (some j)) (bundleBiholomorph j p) =
      EllipticGeometry.nativePatchBiholomorph j p.proj := Subtype.ext rfl

end Elliptic

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical
