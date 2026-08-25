import StackExchange.Puzzling139335.N5Facet.Aligned
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.PlaneIsometries

/-!
# The reflected incoming-aligned contradiction for actual plane sets

The two displayed images are vertical reflections of each other and have
the same minimum height.  Diagonal invariance of their actual union then
determines that height from its rightmost contact.  The source's actual
outgoing-arm endpoint contradicts the resulting support value.
-/

open Set

namespace Puzzling139335.N5.AlignedFace

/-- Plane-set form of the proved reflected aligned scalar obstruction.
Every support bound is derived from actual source/image containment. -/
theorem reflection_impossible
    {P : Set Plane} {R D : Plane → Plane} {c s h k b : ℝ}
    (hP : P ⊆ unitSquare) (hA : corner 0 ∈ P)
    (hfit : R '' P ∪ D '' P ⊆ unitSquare)
    (hTR : Schoenflies.Plane.mk 1 1 ∈ R '' P ∪ D '' P)
    (hRy : ∀ p, R p 1 = 1 - (c * h + s * k) + c * p 0 + s * p 1)
    (hD : ∀ p, D p = Schoenflies.Plane.mk (1 + b - R p 0) (R p 1))
    (hstable : ∀ p ∈ R '' P ∪ D '' P,
      ReflectionSeparation.diagonal p ∈ R '' P ∪ D '' P)
    (hunit : c ^ 2 + s ^ 2 = 1) (hc : 0 < c) (hs : 0 < s)
    (hz : 0 < c * k - s * h)
    (hendpoint : Schoenflies.Plane.mk
      (h - (1 - b) * c) (k - (1 - b) * s) ∈ P) : False := by
  let V := R '' P ∪ D '' P
  let ρ : Plane → Plane := fun p => Schoenflies.Plane.mk (1 + b - p 0) (p 1)
  have hreflect : ∀ p ∈ V, ρ p ∈ V := by
    rintro p (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inr ⟨x, hx, hD x⟩
    · refine Or.inl ⟨x, hx, ?_⟩
      rw [hD x]
      apply PlaneIsometries.plane_ext
      · change R x 0 = 1 + b - (1 + b - R x 0)
        ring
      · rfl
  have hRmin {p : Plane} (hp : p ∈ P) :
      1 - (c * h + s * k) ≤ R p 1 := by
    rw [hRy]
    have hx := mul_nonneg hc.le (hP hp).1.1
    have hy := mul_nonneg hs.le (hP hp).2.1
    linarith
  have hminimum : ∀ p ∈ V, 1 - (c * h + s * k) ≤ p 1 := by
    rintro p (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact hRmin hx
    · rw [hD x]
      exact hRmin hx
  have hya : R (corner 0) 1 = 1 - (c * h + s * k) := by
    rw [hRy]
    norm_num [corner, Fin.ext_iff]
  exact N5Facet.reflected_aligned_impossible
    V (fun p => p 0) (fun p => p 1) ReflectionSeparation.diagonal ρ
    (b := b) (c := c) (s := s) (h := h) (k := k) (L := 1 - b)
    hstable hreflect ReflectionSeparation.diagonal_apply_zero
    ReflectionSeparation.diagonal_apply_one (fun _ => rfl)
    (fun p hp => (hfit hp).1.2)
    (r := Schoenflies.Plane.mk 1 1) (a := R (corner 0))
    hTR rfl (Or.inl (mem_image_of_mem R hA)) hminimum hya
    hunit hs hz rfl (hP hendpoint).1.1

end Puzzling139335.N5.AlignedFace
