import StackExchange.Puzzling139335.PlaneIsometries
import Mathlib.Analysis.Convex.Segment

/-!
# Three distinct radial segments under a small positive rotation

The horizontal segment and its first two rotated images meet pairwise only
at the origin.  These are actual set intersections; no boundary or convex
hull assumption is used here.
-/

open Set

namespace Puzzling139335.DoubleCorner

open PlaneIsometries

/-- The coordinate bounds of a segment along the positive horizontal axis. -/
theorem bottom_segment_coordinates {t : ℝ} {x : Plane} (ht : 0 ≤ t)
    (hx : x ∈ segment ℝ (0 : Plane) !₂[t, 0]) :
    0 ≤ x 0 ∧ x 0 ≤ t ∧ x 1 = 0 := by
  rw [segment_eq_image] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hu0 : 0 ≤ u * t := mul_nonneg hu.1 ht
  have hu1 : u * t ≤ t := by nlinarith [hu.2]
  simpa using And.intro hu0 (And.intro hu1 (rfl : (0 : ℝ) = 0))

/-- Three radial segments obtained by iterating a positive rotation have
pairwise intersection contained in the origin.  The angle bound `s < c`
matches the geometric application; positive cosine and sine already suffice
for these intersection statements. -/
theorem bottom_rotation_trio_intersections
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {t c s : ℝ}
    (ht : 0 < t) (hc : 0 < c) (hs : 0 < s) (_hsc : s < c)
    (he : ∀ x, e x = directCoordinates c s 0 x) :
    (segment ℝ (0 : Plane) !₂[t, 0] ∩
      e '' segment ℝ (0 : Plane) !₂[t, 0] ⊆ ({0} : Set Plane)) ∧
    (segment ℝ (0 : Plane) !₂[t, 0] ∩
      e '' (e '' segment ℝ (0 : Plane) !₂[t, 0]) ⊆ ({0} : Set Plane)) ∧
    (e '' segment ℝ (0 : Plane) !₂[t, 0] ∩
      e '' (e '' segment ℝ (0 : Plane) !₂[t, 0]) ⊆ ({0} : Set Plane)) := by
  let A : Set Plane := segment ℝ (0 : Plane) !₂[t, 0]
  have hcoord {x : Plane} (hx : x ∈ A) : x 1 = 0 :=
    (bottom_segment_coordinates ht.le hx).2.2
  have he0 : e 0 = 0 := by
    rw [he]
    apply plane_ext <;> simp [directCoordinates]
  have he1 (x : Plane) (hx : x 1 = 0) : (e x) 1 = s * x 0 := by
    rw [he]
    simp [directCoordinates, hx]
  have he21 (x : Plane) (hx : x 1 = 0) : (e (e x)) 1 = (2 * c * s) * x 0 := by
    rw [he (e x), he x]
    simp [directCoordinates, hx]
    ring
  have hAB : A ∩ e '' A ⊆ ({0} : Set Plane) := by
    rintro x ⟨hx, y, hy, rfl⟩
    have hy1 : y 1 = 0 := hcoord hy
    have hprod : s * y 0 = 0 := (he1 y hy1).symm.trans (hcoord hx)
    have hy0 : y 0 = 0 := (mul_eq_zero.mp hprod).resolve_left hs.ne'
    have hyzero : y = 0 := plane_ext hy0 hy1
    change e y = 0
    rw [hyzero, he0]
  have hAC : A ∩ e '' (e '' A) ⊆ ({0} : Set Plane) := by
    rintro x ⟨hx, _, ⟨y, hy, rfl⟩, rfl⟩
    have hy1 : y 1 = 0 := hcoord hy
    have hprod : (2 * c * s) * y 0 = 0 := (he21 y hy1).symm.trans (hcoord hx)
    have hcoef : 0 < 2 * c * s := mul_pos (mul_pos (by norm_num) hc) hs
    have hy0 : y 0 = 0 := (mul_eq_zero.mp hprod).resolve_left hcoef.ne'
    have hyzero : y = 0 := plane_ext hy0 hy1
    change e (e y) = 0
    rw [hyzero, he0, he0]
  refine ⟨hAB, hAC, ?_⟩
  rintro x ⟨⟨y, hy, rfl⟩, z, hz, hzy⟩
  have hzy' : z = y := e.injective hzy
  have hyB : y ∈ e '' A := hzy' ▸ hz
  have hy0 : y = 0 := mem_singleton_iff.mp (hAB ⟨hy, hyB⟩)
  change e y = 0
  rw [hy0, he0]

end Puzzling139335.DoubleCorner
