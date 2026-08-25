import StackExchange.Puzzling139335.AcuteCorner.Defs
import Mathlib.Analysis.Convex.Topology

/-!
# Closures of the two strict diagonal cones

The boundary rays, including the vertex, are limits of points of the strict
cone. The proof uses an open segment from a fixed strict interior point and
does not assume any regularity of a tile boundary.
-/

open Set

namespace Puzzling139335.DoubleCorner

/-- The open cone between the positive horizontal ray and the positive diagonal. -/
def strictCone45 : Set Plane := {p | 0 < p 1 ∧ p 1 < p 0}

/-- The closed cone between the positive diagonal and the positive vertical ray. -/
def upperCone45 : Set Plane := {p | 0 ≤ p 0 ∧ p 0 ≤ p 1}

/-- The open cone between the positive diagonal and the positive vertical ray. -/
def strictUpperCone45 : Set Plane := {p | 0 < p 0 ∧ p 0 < p 1}

theorem isOpen_strictCone45 : IsOpen strictCone45 :=
  (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).inter
    (isOpen_lt (EuclideanSpace.proj 1).continuous (EuclideanSpace.proj 0).continuous)

theorem isOpen_strictUpperCone45 : IsOpen strictUpperCone45 :=
  (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
    (isOpen_lt (EuclideanSpace.proj 0).continuous (EuclideanSpace.proj 1).continuous)

private theorem closure_strict_coord_cone (i j : Fin 2) (hij : i ≠ j) :
    closure {p : Plane | 0 < p i ∧ p i < p j} =
      {p : Plane | 0 ≤ p i ∧ p i ≤ p j} := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro p hp
      exact ⟨hp.1.le, hp.2.le⟩
    · exact (isClosed_le continuous_const (EuclideanSpace.proj i).continuous).inter
        (isClosed_le (EuclideanSpace.proj i).continuous (EuclideanSpace.proj j).continuous)
  · intro p hp
    let q : Plane := EuclideanSpace.single i 1 + EuclideanSpace.single j 2
    have hqi : q i = 1 := by simp [q, hij]
    have hqj : q j = 2 := by simp [q, hij.symm]
    have hseg : openSegment ℝ q p ⊆ {v : Plane | 0 < v i ∧ v i < v j} := by
      rintro v ⟨a, b, ha, hb, _hab, rfl⟩
      change 0 < a * q i + b * p i ∧ a * q i + b * p i < a * q j + b * p j
      rw [hqi, hqj]
      have hbi : 0 ≤ b * p i := mul_nonneg hb.le hp.1
      have hbij : b * p i ≤ b * p j := mul_le_mul_of_nonneg_left hp.2 hb.le
      constructor <;> linarith
    exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ q p))

/-- Closing the strict lower cone adds precisely its two boundary rays. -/
theorem closure_strictCone45 : closure strictCone45 = AcuteCorner.cone45 :=
  closure_strict_coord_cone 1 0 (by decide)

/-- Closing the strict upper cone adds precisely its two boundary rays. -/
theorem closure_strictUpperCone45 : closure strictUpperCone45 = upperCone45 :=
  closure_strict_coord_cone 0 1 (by decide)

end Puzzling139335.DoubleCorner
