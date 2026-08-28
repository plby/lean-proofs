import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPatches
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackLocal

/-!
# Exact native frame compatibility on full gluing patches

The genuine global canonical frame in a chart inherited from a local
piece pulls back to that piece's genuine native canonical frame.  These
are equalities of actual bundle vectors, not just assigned coefficients.
The corresponding global-bundle-valued local sections are holomorphic.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace localPieceChartedSpace
  localPiece_nonempty localPiece_isManifold

local instance patchFramesGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- Pullback recovers the actual native canonical frame, with coefficient
exactly one in the matching local and glued charts. -/
theorem patchPullback_localFrame (i : Index) (a x : localPiece i)
    (hx : x ∈ (chartAt Model a).source) :
    patchPullback i x (patchLocalFrame i a x hx) =
      Atlas.localFrame (localPiece i) (achart Model a) ⟨x, hx⟩ := by
  apply (Atlas.coordinateEquiv (localPiece i) (achart Model a) hx).injective
  change Atlas.inCoordinates (localPiece i) (achart Model a) x
      (patchPullback i x (patchLocalFrame i a x hx)) =
    Atlas.inCoordinates (localPiece i) (achart Model a) x
      (Atlas.localFrame (localPiece i) (achart Model a) ⟨x, hx⟩)
  calc
    _ = (inCoordinates (patchChart i a) (Threefold.inclusion i x)
        (patchLocalFrame i a x hx)).compContinuousLinearMap
          (Pullback.chartDerivative (Threefold.inclusion i) (achart Model a)
            (patchChart i a) x) :=
      Pullback.inCoordinates_pullbackEquiv (inclusion_isLocalDiffeomorph i)
        (achart Model a) (patchChart i a) hx (inclusion_mem_patchChart_source i a x hx)
        (patchLocalFrame i a x hx)
    _ = volume := patchLocalFrame_pullback i a x hx
    _ = _ := (Atlas.localFrame_inCoordinates (localPiece i) (achart Model a) ⟨x, hx⟩).symm

/-- The inverse comparison sends the entire native frame vector to the
matching frame of the actual global canonical bundle. -/
theorem patchPushforward_localFrame (i : Index) (a x : localPiece i)
    (hx : x ∈ (chartAt Model a).source) :
    patchPushforward i
      ⟨x, Atlas.localFrame (localPiece i) (achart Model a) ⟨x, hx⟩⟩ =
        ⟨Threefold.inclusion i x, patchLocalFrame i a x hx⟩ := by
  rw [← patchPullback_localFrame i a x hx]
  simp only [patchPushforward, ContinuousLinearEquiv.symm_apply_apply]

abbrev patchFrameDomain (i : Index) (a : localPiece i) :
    TopologicalSpace.Opens (localPiece i) :=
  ⟨(chartAt Model a).source, (chartAt Model a).open_source⟩

/-- The actual piece inclusion, restricted to the matching global chart source. -/
def patchFramePoint (i : Index) (a : localPiece i) (x : patchFrameDomain i a) :
    Atlas.chartSource Threefold.Space (patchChart i a) :=
  ⟨Threefold.inclusion i x.val, inclusion_mem_patchChart_source i a x.val x.property⟩

theorem patchFramePoint_holomorphic (i : Index) (a : localPiece i) :
    ContMDiff IF IF ω (patchFramePoint i a) := by
  have h : IsLocalDiffeomorph IF IF ω
      (fun x : patchFrameDomain i a => Threefold.inclusion i x.val) := by
    intro x
    exact (isLocalDiffeomorph_subtypeVal IF (patchFrameDomain i a) x).comp
      (K := IF) (P := Threefold.Space) (inclusion_isLocalDiffeomorph i x.val)
  exact (isLocalDiffeomorph_codRestrictOpens IF IF h
    (Atlas.chartSource Threefold.Space (patchChart i a))
    (fun x => inclusion_mem_patchChart_source i a x.val x.property)).contMDiff

/-- The matching local frame as a map into the native global bundle. -/
def patchLocalFrameSection (i : Index) (a : localPiece i)
    (x : patchFrameDomain i a) : bundle.TotalSpace :=
  ⟨Threefold.inclusion i x.val, patchLocalFrame i a x.val x.property⟩

theorem patchLocalFrameSection_holomorphic (i : Index) (a : localPiece i) :
    ContMDiff IF ((IF).prod I₁) ω (patchLocalFrameSection i a) :=
  (Atlas.localFrameSection_holomorphic Threefold.Space (patchChart i a)).comp
    (patchFramePoint_holomorphic i a)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical
