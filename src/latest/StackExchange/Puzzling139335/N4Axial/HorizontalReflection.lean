import StackExchange.Puzzling139335.N4OuterPair.Remainder
import StackExchange.Puzzling139335.CentralNonRotation.FixedImage
import StackExchange.Puzzling139335.CentralNonRotation.SquareTranslationAxis.BoundedTranslation

/-!
# Excluding a horizontal reflection between the middle pieces

A nonempty compact set invariant under the square's horizontal reflection
cannot be invariant under a second parallel reflection with a different axis.
Their composition would give a nonzero translation preserving that set.
Applying this to the actual middle union forces the congruence to fix the center.
-/

open Set

namespace Puzzling139335.N4Axial

/-- A horizontal reflection preserving a compact nonempty set already invariant
under reflection in the square's midline has that same axis. -/
theorem horizontal_reflection_parameter_eq_one
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (b : ℝ)
    (hg : ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = b - p 1)
    {V : Set Plane} (hV : IsCompact V) (hVne : V.Nonempty)
    (hH : ReflectionSeparation.horizontal '' V = V) (hgV : g '' V = V) :
    b = 1 := by
  let w : Plane := !₂[0, b - 1]
  have hcompose (p : Plane) : g (ReflectionSeparation.horizontal p) = p + w := by
    ext i
    fin_cases i
    · change (g (ReflectionSeparation.horizontal p)) 0 = p 0 + 0
      rw [(hg _).1, ReflectionSeparation.horizontal_apply_zero, add_zero]
    · change (g (ReflectionSeparation.horizontal p)) 1 = p 1 + (b - 1)
      rw [(hg _).2, ReflectionSeparation.horizontal_apply_one]
      ring
  have htranslation : ∀ p ∈ V, p + w ∈ V := by
    intro p hp
    rw [← hcompose]
    have hHp : ReflectionSeparation.horizontal p ∈ V :=
      hH ▸ mem_image_of_mem ReflectionSeparation.horizontal hp
    exact hgV ▸ mem_image_of_mem g hHp
  have hw := CentralNonRotation.translation_eq_zero_of_isCompact V hV hVne w htranslation
  have hy := congrArg (fun p : Plane => p 1) hw
  change b - 1 = 0 at hy
  linarith

end Puzzling139335.N4Axial

namespace Puzzling139335.N4OuterPair.Configuration

variable {d : SquareDissection}

/-- A horizontal reflection exchanging the middle pieces is necessarily the
square's horizontal reflection. The protected-center assumption is not needed. -/
theorem middle_horizontal_reflection_parameter_eq_one
    (h : N4OuterPair.Configuration d) (g : Plane ≃ᵃⁱ[ℝ] Plane) (b : ℝ)
    (hg : ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = b - p 1)
    (himage : g '' d.piece 2 = d.piece 3) : b = 1 := by
  have hgg (p : Plane) : g (g p) = p := by
    ext i
    fin_cases i
    · exact ((hg (g p)).1).trans (hg p).1
    · change (g (g p)) 1 = p 1
      rw [(hg _).2, (hg p).2]
      ring
  have hback : g '' d.piece 3 = d.piece 2 := by
    rw [← himage, image_image]
    change (fun p => g (g p)) '' d.piece 2 = d.piece 2
    simp only [hgg, image_id']
  have hgV : g '' (d.piece 2 ∪ d.piece 3) = d.piece 2 ∪ d.piece 3 := by
    rw [image_union, himage, hback, union_comm]
  exact N4Axial.horizontal_reflection_parameter_eq_one g b hg
    ((d.jordan 2).isCompact.union (d.jordan 3).isCompact)
    ((d.jordan 2).nonempty.mono subset_union_left) h.middle_union_reflected hgV

/-- The middle-piece congruence cannot be reflection in any horizontal line
when one piece contains a neighborhood of the square's center. -/
theorem false_of_middle_horizontal_reflection
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (b : ℝ)
    (hg : ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = b - p 1)
    (himage : g '' d.piece 2 = d.piece 3) : False := by
  have hb := h.middle_horizontal_reflection_parameter_eq_one g b hg himage
  have hfix : g squareCenter = squareCenter := by
    ext i
    fin_cases i
    · exact (hg squareCenter).1
    · change (g squareCenter) 1 = squareCenter 1
      rw [(hg squareCenter).2, hb]
      norm_num
  have hdis : Disjoint (interior (d.piece 2)) (interior (g '' d.piece 2)) := by
    rw [himage]
    exact d.disjoint_interiors (by decide)
  have hnot := CentralNonRotation.not_mem_interiors_of_fixed (d.piece 2) g hfix hdis
  rw [himage] at hnot
  exact (h.center_in_middle hc).elim hnot.1 hnot.2

end Puzzling139335.N4OuterPair.Configuration
