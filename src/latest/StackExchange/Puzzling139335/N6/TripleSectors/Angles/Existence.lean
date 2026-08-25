import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Germ
import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Representation
import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Representation.Width

/-! Angular certificates derived from actual Jordan boundary branches. -/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.Angles

open LocalSector

/-- A Jordan region in the first quadrant with two straight local branches
has the complete actual-ray angular certificate used in the trisection proof.
No angle or filled-sector premise occurs in this existence theorem. -/
theorem nonempty_raySectorGerm
    {P : Set Plane} (hP : IsJordanRegion P)
    (hquadrant : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1)
    (hcount : HasStraightBranchCount (frontier P) 0 2) :
    Nonempty (RaySectorGerm P) := by
  obtain ⟨a, b, ha, hb, haq, hbq, hdet, haSeg, hbSeg, _, hgerm, s, hs, hinterior⟩ :=
    exists_local_openSector_of_straightBranchCount hP hquadrant hcount
  obtain ⟨α, hα, haeq⟩ := exists_firstQuadrant_angle ha haq.1 haq.2
  obtain ⟨β, hβ, hbeq⟩ := exists_firstQuadrant_angle hb hbq.1 hbq.2
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hαβ : α < β := angle_lt_of_det_pos hα hβ haeq hbeq hdet
  obtain ⟨r, hr, hboundary⟩ := hgerm
  let g : AngularGerm P := angularGermOfTwoRays hα hβ hαβ hr hs hdet.le
    hboundary hinterior
    (fun _ hθ _ ht => smul_ray_mem_openSector_iff han hbn ht hα hβ hθ haeq hbeq)
    (fun _ hθ _ ht => by
      simpa only [leftForm_apply, rightForm_apply, mem_Icc] using
        smul_ray_mem_closedSector_iff han hbn ht hα hβ hθ haeq hbeq)
  refine ⟨{
    toAngularGerm := g
    left := a
    right := b
    left_ne_zero := ha
    right_ne_zero := hb
    det_pos := hdet
    left_eq := haeq
    right_eq := hbeq
    left_segment := haSeg
    right_segment := hbSeg
    boundary_germ := ⟨r, hr, hboundary⟩
    angle_eq_width := ?_
  }⟩
  change InnerProductGeometry.angle a b = β - α
  exact angle_eq_sub han hbn hα hβ hαβ.le haeq hbeq

end Puzzling139335.N6.TripleSectors.Angles
