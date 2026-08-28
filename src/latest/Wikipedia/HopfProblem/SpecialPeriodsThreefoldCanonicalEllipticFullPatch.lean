import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPieceBiholomorphs
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticRestrictionHolomorphic

/-!
# The original full elliptic canonical bundle on the actual global patch

Restricting the original ambient elliptic canonical bundle to the exact
source of the full parametrization gives a bundle biholomorphic to the
entire corresponding restriction of the global canonical bundle.  The
map is the inverse pullback by the actual full parametrization derivative.
Both total spaces retain their original open-submanifold bundle atlases.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace

/-- The genuine original full-filling canonical bundle, restricted to the
actual small domain, is biholomorphic to the full global elliptic restriction. -/
def fullBundlePatchBiholomorph (j : Kind) :
    Diffeomorph Iᴷ Iᴷ (fullBundleRestriction j)
      (Threefold.Canonical.bundlePatch (some (some j))) ω :=
  (restrictionBundleBiholomorph j).symm.trans (bundleBiholomorph j)

/-- The comparison covers the actual elliptic patch parametrization. -/
theorem fullBundlePatchBiholomorph_projection (j : Kind) (p : fullBundleRestriction j) :
    Threefold.Canonical.bundlePatchProjection (some (some j))
        (fullBundlePatchBiholomorph j p) =
      EllipticGeometry.nativePatchBiholomorph j (fullBundleRestrictionProjection j p) := by
  change Threefold.Canonical.bundlePatchProjection (some (some j))
      (bundleBiholomorph j ((restrictionBundleBiholomorph j).symm p)) = _
  rw [bundleBiholomorph_projection, restrictionBundleBiholomorph_symm_proj]

/-- The forward map uses the already constructed derivative pullbacks,
first on the actual open inclusion and then on the actual global inclusion. -/
theorem fullBundlePatchBiholomorph_val (j : Kind) (p : fullBundleRestriction j) :
    (fullBundlePatchBiholomorph j p : Threefold.Canonical.bundle.TotalSpace) =
      ⟨EllipticGeometry.inclusion j (fullBundleRestrictionProjection j p),
        (patchPullback j (fullBundleRestrictionProjection j p)).symm
          (restriction j (fullBundleRestrictionProjection j p) p.val.2)⟩ := by
  change (bundleBiholomorph j ((restrictionBundleBiholomorph j).symm p) :
    Threefold.Canonical.bundle.TotalSpace) = _
  rw [restrictionBundleBiholomorph_symm_apply, bundleBiholomorph_val]
  rfl

/-- The composed fibre map is exactly inverse pullback by the full
parametrization, by the native manifold chain rule. -/
theorem fullPatchPullback_symm_factorization (j : Kind) (x : SpecialEllipticPiece j)
    (v : (fullBundle j).Fiber x.val) :
    (patchPullback j x).symm (restriction j x v) =
      (fullPatchPullback j x.val (piece_mem_fullParametrization_source j x)).symm v := by
  have h := congrArg (fun L => id (α := ℂ) (L.symm (restriction j x v)))
    (patchPullback_factorization j x)
  change id (α := ℂ) ((patchPullback j x).symm (restriction j x v)) =
    id (α := ℂ)
      ((fullPatchPullback j x.val (piece_mem_fullParametrization_source j x)).symm
        ((restriction j x).symm (restriction j x v))) at h
  exact h.trans (congrArg (fun w => id (α := ℂ)
    ((fullPatchPullback j x.val (piece_mem_fullParametrization_source j x)).symm w))
      ((restriction j x).symm_apply_apply v))

/-- Literal forward formula on the original full-filling total space:
the base map and its canonical fibre map are the actual parametrization
and inverse differential pullback, respectively. -/
theorem fullBundlePatchBiholomorph_fullParametrization (j : Kind)
    (p : fullBundleRestriction j) :
    (fullBundlePatchBiholomorph j p : Threefold.Canonical.bundle.TotalSpace) =
      ⟨EllipticGeometry.fullParametrization j p.val.proj,
        (fullPatchPullback j p.val.proj
          (piece_mem_fullParametrization_source j (fullBundleRestrictionProjection j p))).symm
            p.val.2⟩ := by
  rw [fullBundlePatchBiholomorph_val]
  have hb := (EllipticGeometry.fullParametrization_apply j
    (fullBundleRestrictionProjection j p)).symm
  have hf := fullPatchPullback_symm_factorization j (fullBundleRestrictionProjection j p)
    p.val.2
  exact congrArg₂ (fun (x : Threefold.Space) (v : ℂ) =>
    (⟨x, v⟩ : Threefold.Canonical.bundle.TotalSpace)) hb hf

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic
