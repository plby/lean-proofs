import Wikipedia.HopfProblem.SpecialPeriodsThreefoldBase

/-!
# Closed coordinate supports in the actual compactified triangle base

A closed round disc strictly inside a selected filling radius gives a
compact, closed subset of the original filling patch.  The support uses
the actual inverse puncture chart and the existing compactification
topology.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open SpecialPeriods SpecialPeriods.Threefold

/-- The closed support obtained from the original inverse puncture chart. -/
def coordinateClosedSupport (_C : BaseCover) (i : Puncture) (R : ℝ) :
    Set TriangleCompactifiedOrbitSpace :=
  (punctureChart i).symm '' Metric.closedBall 0 R

/-- A closed coordinate disc below the selected radius is compact in the
actual compactified triangle base. -/
theorem coordinateClosedSupport_isCompact (C : BaseCover) (i : Puncture) (R : ℝ)
    (hR : R < C.radius i) : IsCompact (coordinateClosedSupport C i R) := by
  exact (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
    ((punctureChart i).continuousOn_symm.mono
      ((Metric.closedBall_subset_ball hR).trans (C.coordinateBall_subset_target i)))

/-- The original Hausdorff topology makes the coordinate support closed. -/
theorem coordinateClosedSupport_isClosed (C : BaseCover) (i : Puncture) (R : ℝ)
    (hR : R < C.radius i) : IsClosed (coordinateClosedSupport C i R) :=
  (coordinateClosedSupport_isCompact C i R hR).isClosed

/-- The closed support lies in the actual selected filling patch. -/
theorem coordinateClosedSupport_subset_fillingPatch
    (C : BaseCover) (i : Puncture) (R : ℝ) (hR : R < C.radius i) :
    coordinateClosedSupport C i R ⊆ (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace) := by
  rintro x ⟨z, hz, rfl⟩
  exact C.inverse_mem_fillingPatch i (Metric.closedBall_subset_ball hR hz)

/-- Membership is the literal closed norm bound in the original chart. -/
theorem mem_coordinateClosedSupport (C : BaseCover) (i : Puncture) (R : ℝ)
    (hR : R < C.radius i) (x : TriangleCompactifiedOrbitSpace) :
    x ∈ coordinateClosedSupport C i R ↔
      x ∈ (punctureChart i).source ∧ ‖punctureChart i x‖ ≤ R := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have ht := C.coordinateBall_subset_target i (Metric.closedBall_subset_ball hR hz)
    refine ⟨(punctureChart i).map_target ht, ?_⟩
    rw [(punctureChart i).right_inv ht]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  · rintro ⟨hx, hnorm⟩
    refine ⟨punctureChart i x, ?_, (punctureChart i).left_inv hx⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
