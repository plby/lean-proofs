import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingGlobalOverlap
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupMarkedInclusion

/-!
# Actual elliptic attaching paths in the regular family and the glued space

The literal small-overlap identification compares the logarithmic
attaching paths with the zero section and the original positive period
column loops.  All basepoint adjustments here are casts by proved
equalities of points of the glued space.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Elliptic.LogGauge EllipticFilling TrianglePeriodFamily CuspUniformization

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The actual whole-piece inclusion as a continuous map. -/
def attachingPieceInclusionMap (j : Kind) : C(LocalSpace j, Threefold.Space) :=
  ⟨inclusion j, inclusion_continuous j⟩

/-- The original gluing relation identifies the two actual overlap points. -/
theorem inclusion_eq_regular_overlap (j : Kind) (x : LocalSpace j)
    (hx : x ∈ (specialEllipticOverlap j).source) :
    inclusion j x = regularFamilyInclusionMap (specialEllipticOverlap j x) := by
  change gluingData.inclusion (some (some j)) x =
    gluingData.inclusion none (specialEllipticOverlap j x)
  exact (gluingData.inclusion_eq_iff (some (some j)) none x _).mpr ⟨hx, rfl⟩

theorem attachingLoop_mem_overlap (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    attachingLoop j s₀ hs₀ hr t ∈ (specialEllipticOverlap j).source := by
  rw [specialEllipticOverlap_source]
  exact projectionToBase_attachingLoop_mem_regular j s₀ hs₀ hr t

theorem attachingFibreLoop_mem_overlap (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    attachingFibreLoop j s₀ hs₀ hr w t ∈ (specialEllipticOverlap j).source := by
  rw [specialEllipticOverlap_source]
  exact projectionToBase_attachingFibreLoop_mem_regular j s₀ hs₀ hr w t

/-- The quotient of the actual upstairs elliptic trajectory closes at fibre zero. -/
theorem attachingRegularPoint_one_eq (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    (Dsp).quotient (attachingUpstairsPoint j s₀ hs₀ 1, 0) =
      (Dsp).quotient (attachingUpstairsPoint j s₀ hs₀ 0, 0) := by
  calc
    _ = specialEllipticOverlap j (attachingLoop j s₀ hs₀ hr 1) :=
      (specialEllipticOverlap_attachingLoop j s₀ hs₀ hr 1).symm
    _ = specialEllipticOverlap j (attachingLoop j s₀ hs₀ hr 0) :=
      congrArg (specialEllipticOverlap j) (attachingLoop j s₀ hs₀ hr).target
    _ = _ := specialEllipticOverlap_attachingLoop j s₀ hs₀ hr 0

/-- The actual regular-family zero-section loop obtained from the logarithmic gauge. -/
def attachingRegularLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    Path ((Dsp).fundamentalGroupBasepoint (attachingUpstairsPoint j s₀ hs₀ 0))
      ((Dsp).fundamentalGroupBasepoint (attachingUpstairsPoint j s₀ hs₀ 0)) where
  toFun t := (Dsp).quotient (attachingUpstairsPoint j s₀ hs₀ t, 0)
  continuous_toFun := (Dsp).quotient_continuous.comp
    ((attachingUpstairsPoint_continuous j s₀ hs₀).prodMk continuous_const)
  source' := rfl
  target' := attachingRegularPoint_one_eq j s₀ hs₀ hr

@[simp] theorem attachingRegularLoop_apply (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    attachingRegularLoop j s₀ hs₀ hr t =
      (Dsp).quotient (attachingUpstairsPoint j s₀ hs₀ t, 0) := rfl

/-- The original regular-base loop beneath this literal zero-section loop. -/
def attachingRegularBaseLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    Path (triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0))
      (triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ 0)) :=
  (attachingRegularLoop j s₀ hs₀ hr).map (Dsp).projection_continuous

@[simp] theorem attachingRegularBaseLoop_apply (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    attachingRegularBaseLoop j s₀ hs₀ hr t =
      triangleRegularProject (attachingUpstairsPoint j s₀ hs₀ t) := rfl

theorem attachingRegularLoop_eq_zeroSection (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    attachingRegularLoop j s₀ hs₀ hr =
      (attachingRegularBaseLoop j s₀ hs₀ hr).map (Dsp).zeroSection_continuous := by
  ext t
  rfl

/-- Its compact-base formula is the original inverse chart and clockwise root power. -/
theorem attachingRegularBaseLoop_compact (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    regularInclusion (attachingRegularBaseLoop j s₀ hs₀ hr t) =
      (punctureChart (some j)).symm
        (exponential (s₀ - ((t : ℝ) : ℂ) / (j.order : ℂ)) ^ j.order) := by
  have h := specialEllipticOverlap_base j (attachingLoop j s₀ hs₀ hr t)
    (attachingLoop_mem_overlap j s₀ hs₀ hr t)
  rw [specialEllipticOverlap_attachingLoop] at h
  exact h.trans (projectionToBase_attachingLoop j s₀ hs₀ hr t)

/-- The actual gluing makes the attaching basepoint exactly a regular fibre zero. -/
theorem attachingGlobalBasepoint_eq (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    inclusion j (attachingBasepoint j s₀ hs₀ hr) =
      regularFamilyInclusionMap
        ((Dsp).fundamentalGroupBasepoint (attachingUpstairsPoint j s₀ hs₀ 0)) := by
  exact (inclusion_eq_regular_overlap j (attachingLoop j s₀ hs₀ hr 0)
    (attachingLoop_mem_overlap j s₀ hs₀ hr 0)).trans
      (congrArg regularFamilyInclusionMap (specialEllipticOverlap_attachingLoop j s₀ hs₀ hr 0))

/-- Include the actual meridian, casting only by its proved gluing basepoint equality. -/
def includedAttachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    Path (regularFamilyInclusionMap
      ((Dsp).fundamentalGroupBasepoint (attachingUpstairsPoint j s₀ hs₀ 0)))
      (regularFamilyInclusionMap
        ((Dsp).fundamentalGroupBasepoint (attachingUpstairsPoint j s₀ hs₀ 0))) :=
  ((attachingLoop j s₀ hs₀ hr).map (inclusion_continuous j)).cast
    (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm
    (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm

theorem includedAttachingLoop_eq_regular (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    includedAttachingLoop j s₀ hs₀ hr =
      (attachingRegularLoop j s₀ hs₀ hr).map regularFamilyInclusionMap.continuous := by
  ext t
  exact (inclusion_eq_regular_overlap j (attachingLoop j s₀ hs₀ hr t)
    (attachingLoop_mem_overlap j s₀ hs₀ hr t)).trans
      (congrArg regularFamilyInclusionMap (specialEllipticOverlap_attachingLoop j s₀ hs₀ hr t))

/-- Include the actual positive fibre loop with the same proved basepoint equality. -/
def includedAttachingFibreLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (w : Lattice) :
    Path (regularFamilyInclusionMap
      ((Dsp).fundamentalGroupBasepoint (attachingUpstairsPoint j s₀ hs₀ 0)))
      (regularFamilyInclusionMap
        ((Dsp).fundamentalGroupBasepoint (attachingUpstairsPoint j s₀ hs₀ 0))) :=
  ((attachingFibreLoop j s₀ hs₀ hr w).map (inclusion_continuous j)).cast
    (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm
    (attachingGlobalBasepoint_eq j s₀ hs₀ hr).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
