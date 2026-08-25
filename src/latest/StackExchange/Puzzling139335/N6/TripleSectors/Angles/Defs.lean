import StackExchange.Puzzling139335.N6.TripleSectors.LocalSector
import StackExchange.Puzzling139335.ThreeCorners.Rays

/-! Angular data derived from an actual filled boundary sector. -/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.Angles

/-- A local angular description of a region at the square's origin.

The interior is tested on short positive rays.  Region membership implies
membership in the closed angular interval; this also controls its boundary.
The subsequent existence theorem derives this data from actual Jordan germs.
-/
structure AngularGerm (P : Set Plane) where
  lower : ℝ
  upper : ℝ
  lower_nonneg : 0 ≤ lower
  upper_le : upper ≤ Real.pi / 2
  lower_lt_upper : lower < upper
  radius : ℝ
  radius_pos : 0 < radius
  interior_ray_iff : ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2),
    ∀ t : ℝ, 0 < t → t < radius →
      (t • ThreeCorners.ray θ ∈ interior P ↔ θ ∈ Ioo lower upper)
  piece_ray_imp : ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2),
    ∀ t : ℝ, 0 < t → t < radius →
      t • ThreeCorners.ray θ ∈ P → θ ∈ Icc lower upper

namespace AngularGerm

variable {P : Set Plane}

theorem lower_mem (g : AngularGerm P) : g.lower ∈ Icc (0 : ℝ) (Real.pi / 2) :=
  ⟨g.lower_nonneg, g.lower_lt_upper.le.trans g.upper_le⟩

theorem upper_mem (g : AngularGerm P) : g.upper ∈ Icc (0 : ℝ) (Real.pi / 2) :=
  ⟨g.lower_nonneg.trans g.lower_lt_upper.le, g.upper_le⟩

theorem width_pos (g : AngularGerm P) : 0 < g.upper - g.lower :=
  sub_pos.mpr g.lower_lt_upper

end AngularGerm

end Puzzling139335.N6.TripleSectors.Angles
