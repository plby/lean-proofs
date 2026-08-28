import Wikipedia.SmoothSixDPoincare.MorseSurgerySmoothExterior

/-!
# The actual handle range on the lower level is the old surgery piece

This identifies the geometric avoidance condition used by common-exterior
transport with the domain on which the recorded exterior maps are smooth.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

theorem mem_handleRange_iff_mem_oldPiece (x : d.LowerLevel) :
    x.val ∈ range (d.chart.attachingHandleMap d.radius d.radius_pos d.block) ↔
      x ∈ range d.surgery.oldPiece := by
  constructor
  · rintro ⟨z, hz⟩
    have hneg : ‖z.1.val‖ = 1 :=
      (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block z).mp
        (by rw [hz]; exact x.property.le)
    let u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates :=
      ⟨z.1.val, mem_sphere_zero_iff_norm.mpr hneg⟩
    let v : PuncturedHandle.UnitBall d.chart.PositiveCoordinates :=
      ⟨z.2.val, mem_closedBall_zero_iff.mp z.2.property⟩
    refine ⟨(u, v), Subtype.ext ?_⟩
    rw [d.oldPiece_eq]
    change d.chart.attachingHandleMap d.radius d.radius_pos d.block
      (d.chart.handleBallCoordinates (PuncturedHandle.sphereToBall u, v)) = x.val
    have heq : d.chart.handleBallCoordinates (PuncturedHandle.sphereToBall u, v) = z :=
      Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    rw [heq]
    exact hz
  · rintro ⟨z, hz⟩
    refine ⟨d.chart.handleBallCoordinates (PuncturedHandle.sphereToBall z.1, z.2), ?_⟩
    exact (d.oldPiece_eq z).symm.trans (congrArg Subtype.val hz)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
