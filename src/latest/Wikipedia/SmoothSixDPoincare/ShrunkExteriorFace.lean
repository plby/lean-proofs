import Wikipedia.SmoothSixDPoincare.ShrunkSurgeryBoundary
import Wikipedia.SmoothSixDPoincare.SurgeryExteriorTransport

/-!
# Moving a boundary-contact disk thickening to the original lower level

The entire thickening lies in the common exterior of the refined surgery.
Its transported map is a closed embedding. The old-piece intersection is
computed with both original normal and positive-sphere coordinates retained.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization

open PuncturedHandle

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup W]
  {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p} {s η : ℝ}
  (R : d.ShrunkSurgeryRealization s)

open Classical in
/-- Exact tube incidence and the full native boundary formula construct a
lower-level closed disk thickening with its complete old-piece overlap. -/
theorem exists_lowerExteriorMap (hs : 0 < s) (hs₁ : s < 1)
    (ψ : W → UnitSphere d.chart.PositiveCoordinates)
    (g : C(closedBall (0 : d.chart.NegativeCoordinates) s × closedBall (0 : W) η,
      d.UpperLevel)) (hg : IsClosedEmbedding g)
    (hcontact : ∀ z, g z ∈ d.closedBeltTube s ↔ z.1.val ∈ sphere 0 s)
    (hboundary : ∀ z, z.1.val ∈ sphere 0 s → (g z : M) =
      d.chart.splitChart.symm (d.chart.beltRawCoordinates d.radius (ψ z.2.val, z.1.val))) :
    ∃ L : C(closedBall (0 : d.chart.NegativeCoordinates) s × closedBall (0 : W) η,
        d.LowerLevel),
      IsClosedEmbedding L ∧
      (∀ z, ∃ r, R.surgery.newExterior r = g z ∧ R.surgery.oldExterior r = L z) ∧
      ∀ z (p : UnitSphere d.chart.NegativeCoordinates × UnitBall d.chart.PositiveCoordinates),
        L z = d.surgery.oldPiece p ↔
          z.1.val ∈ sphere 0 s ∧ s • p.1.val = z.1.val ∧ p.2.val = (ψ z.2.val).val := by
  have hge : ∀ z, g z ∈ range R.surgery.newExterior := by
    intro z
    apply R.mem_newExterior_of_tube_boundary
    intro hz
    have hnorm : ‖z.1.val‖ = s := mem_sphere_zero_iff_norm.mp ((hcontact z).mp hz)
    let u : UnitSphere d.chart.NegativeCoordinates := ⟨s⁻¹ • z.1.val, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs), hnorm, inv_mul_cancel₀ hs.ne']⟩
    refine ⟨u, ψ z.2.val, ?_⟩
    have hu : s • u.val = z.1.val := smul_inv_smul₀ hs.ne' z.1.val
    rw [hu]
    exact hboundary z ((hcontact z).mp hz)
  let L := R.surgery.transportExterior g hge
  refine ⟨L, R.surgery.transportExterior_isClosedEmbedding g hge hg, ?_, ?_⟩
  · intro z
    exact ⟨R.surgery.exteriorCoordinates g hge z,
      R.surgery.newExterior_exteriorCoordinates g hge z, rfl⟩
  · intro z p
    change R.surgery.transportExterior g hge z = R.surgery.oldPiece p ↔ _
    rw [R.surgery.transportExterior_oldPiece_iff]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have htube : g z ∈ d.closedBeltTube s := by
        rw [← R.newPiece_range, hq]
        exact mem_range_self (newBoundary q)
      have hz := (hcontact z).mp htube
      have hsq : ‖s • q.1.val‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs,
          mem_sphere_zero_iff_norm.mp q.1.property, mul_one]
        exact hs₁.le
      let u : UnitBall d.chart.NegativeCoordinates := ⟨s • q.1.val, hsq⟩
      let w : UnitBall d.chart.NegativeCoordinates :=
        ⟨z.1.val, (mem_closedBall_zero_iff.mp z.1.property).trans hs₁.le⟩
      have heq : d.beltClosedDiskMap (u, q.2) = d.beltClosedDiskMap (w, ψ z.2.val) := by
        apply Subtype.ext
        exact (R.newPiece_boundary_coe q.1 q.2).symm.trans
          ((congrArg (fun y : d.UpperLevel => (y : M)) hq.symm).trans (hboundary z hz))
      have hpair := d.beltClosedDiskMap_isClosedEmbedding.injective heq
      refine ⟨hz, ?_, ?_⟩
      · exact congrArg (fun t : UnitBall d.chart.NegativeCoordinates ×
          UnitSphere d.chart.PositiveCoordinates => t.1.val) hpair
      · exact congrArg (fun t : UnitBall d.chart.NegativeCoordinates ×
          UnitSphere d.chart.PositiveCoordinates => t.2.val) hpair
    · rintro ⟨hz, hnormal, hpositive⟩
      refine ⟨(p.1, ψ z.2.val), ?_, Prod.ext rfl (Subtype.ext hpositive)⟩
      apply Subtype.ext
      change (g z : M) = (R.surgery.newPiece (sphereToBall p.1, ψ z.2.val) : M)
      rw [R.newPiece_boundary_coe, hnormal]
      exact hboundary z hz

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization
