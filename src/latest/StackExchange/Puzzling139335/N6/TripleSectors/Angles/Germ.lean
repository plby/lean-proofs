import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Family
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Connecting actual two-ray boundary data to angular data. -/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.Angles

open LocalSector

noncomputable section

/-- Angular data together with its two actual, nonzero boundary segments.
This is a derived certificate; its existence is proved from the Jordan
boundary's two straight local branches.
-/
structure RaySectorGerm (P : Set Plane) extends AngularGerm P where
  left : Plane
  right : Plane
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  det_pos : 0 < det left right
  left_eq : left = ‖left‖ • ThreeCorners.ray lower
  right_eq : right = ‖right‖ • ThreeCorners.ray upper
  left_segment : segment ℝ 0 left ⊆ frontier P
  right_segment : segment ℝ 0 right ⊆ frontier P
  boundary_germ : SameBoundaryGerm (frontier P)
    (segment ℝ 0 left ∪ segment ℝ 0 right) 0
  angle_eq_width : InnerProductGeometry.angle left right = upper - lower

namespace RaySectorGerm

variable {P : Set Plane}

theorem normalized_left_eq (g : RaySectorGerm P) :
    ‖g.left‖⁻¹ • g.left = ThreeCorners.ray g.lower := by
  calc
    ‖g.left‖⁻¹ • g.left = ‖g.left‖⁻¹ • (‖g.left‖ • ThreeCorners.ray g.lower) :=
      congrArg (fun x : Plane => ‖g.left‖⁻¹ • x) g.left_eq
    _ = ThreeCorners.ray g.lower := by
      rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr g.left_ne_zero), one_smul]

theorem normalized_right_eq (g : RaySectorGerm P) :
    ‖g.right‖⁻¹ • g.right = ThreeCorners.ray g.upper := by
  calc
    ‖g.right‖⁻¹ • g.right = ‖g.right‖⁻¹ • (‖g.right‖ • ThreeCorners.ray g.upper) :=
      congrArg (fun x : Plane => ‖g.right‖⁻¹ • x) g.right_eq
    _ = ThreeCorners.ray g.upper := by
      rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr g.right_ne_zero), one_smul]

end RaySectorGerm

/-- Region membership is controlled by the closed sector, since a region
point is either interior or on its actual frontier. -/
theorem nonnegative_forms_of_local_piece
    {P : Set Plane} {a b x : Plane} {r s : ℝ}
    (hdet : 0 ≤ det a b)
    (hboundary : ball (0 : Plane) r ∩ frontier P =
      ball (0 : Plane) r ∩ (segment ℝ 0 a ∪ segment ℝ 0 b))
    (hinterior : ball (0 : Plane) s ∩ interior P =
      ball (0 : Plane) s ∩ openSector a b)
    (hxr : x ∈ ball (0 : Plane) r) (hxs : x ∈ ball (0 : Plane) s)
    (hxP : x ∈ P) : 0 ≤ leftForm a x ∧ 0 ≤ rightForm b x := by
  by_cases hxi : x ∈ interior P
  · have hxsector := ((Set.ext_iff.mp hinterior x).mp ⟨hxs, hxi⟩).2
    exact ⟨hxsector.1.le, (rightForm_apply b x).symm ▸ hxsector.2.le⟩
  · have hxf : x ∈ frontier P := ⟨subset_closure hxP, hxi⟩
    have hxseg := ((Set.ext_iff.mp hboundary x).mp ⟨hxr, hxf⟩).2
    have hforms := forms_of_mem_segment_union hdet hxseg
    exact ⟨hforms.1, hforms.2.1⟩

/-- The concrete angular-coordinate equalities can be combined with the
already proved actual boundary/interior germs. -/
def angularGermOfTwoRays
    {P : Set Plane} {a b : Plane} {α β r s : ℝ}
    (hα : α ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hβ : β ∈ Icc (0 : ℝ) (Real.pi / 2)) (hαβ : α < β)
    (hr : 0 < r) (hs : 0 < s) (hdet : 0 ≤ det a b)
    (hboundary : ball (0 : Plane) r ∩ frontier P =
      ball (0 : Plane) r ∩ (segment ℝ 0 a ∪ segment ℝ 0 b))
    (hinterior : ball (0 : Plane) s ∩ interior P =
      ball (0 : Plane) s ∩ openSector a b)
    (hopen : ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2), ∀ t : ℝ, 0 < t →
      (t • ThreeCorners.ray θ ∈ openSector a b ↔ θ ∈ Ioo α β))
    (hclosed : ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2), ∀ t : ℝ, 0 < t →
      (0 ≤ leftForm a (t • ThreeCorners.ray θ) ∧
        0 ≤ rightForm b (t • ThreeCorners.ray θ) ↔ θ ∈ Icc α β)) :
    AngularGerm P where
  lower := α
  upper := β
  lower_nonneg := hα.1
  upper_le := hβ.2
  lower_lt_upper := hαβ
  radius := min r s
  radius_pos := lt_min hr hs
  interior_ray_iff θ hθ t ht htr := by
    have hxs : t • ThreeCorners.ray θ ∈ ball (0 : Plane) s :=
      positive_smul_ray_mem_ball ht (htr.trans_le (min_le_right _ _))
    have hlocal : t • ThreeCorners.ray θ ∈ interior P ↔
        t • ThreeCorners.ray θ ∈ openSector a b := by
      constructor
      · intro hx
        exact ((Set.ext_iff.mp hinterior _).mp ⟨hxs, hx⟩).2
      · intro hx
        exact ((Set.ext_iff.mp hinterior _).mpr ⟨hxs, hx⟩).2
    exact hlocal.trans (hopen θ hθ t ht)
  piece_ray_imp θ hθ t ht htr hxP := by
    have hxr : t • ThreeCorners.ray θ ∈ ball (0 : Plane) r :=
      positive_smul_ray_mem_ball ht (htr.trans_le (min_le_left _ _))
    have hxs : t • ThreeCorners.ray θ ∈ ball (0 : Plane) s :=
      positive_smul_ray_mem_ball ht (htr.trans_le (min_le_right _ _))
    exact (hclosed θ hθ t ht).mp
      (nonnegative_forms_of_local_piece hdet hboundary hinterior hxr hxs hxP)

end

end Puzzling139335.N6.TripleSectors.Angles
