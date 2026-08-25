import StackExchange.Puzzling139335.N4Axial.Dihedral
import StackExchange.Puzzling139335.N4Axial.VerticalAlgebra

/-!
# Vertical translations cannot relate the protected middle pair

The original four-piece density identity gives horizontal invariance of the
sum of the two middle densities. Integrable cancellation then identifies
the translated middle tile with the horizontal reflection of the other.
No topological assumption on their union is used.
-/

open Set MeasureTheory

namespace Puzzling139335.N4OuterPair.Configuration

variable {d : SquareDissection}

/-- A nonzero vertical translation between the two middle pieces forces
their actual images under horizontal reflection to agree. -/
theorem middle_reflected_of_vertical_translation
    (h : Configuration d) (g : Plane ≃ᵃⁱ[ℝ] Plane) (t : ℝ) (ht : t ≠ 0)
    (hg : ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = p 1 + t)
    (himage : g '' d.piece 2 = d.piece 3) :
    ReflectionSeparation.horizontal '' d.piece 2 = d.piece 3 := by
  let v : Plane := !₂[0, t + t]
  have hv : v ≠ 0 := by
    intro hv
    have hone := congrArg (fun p : Plane => p 1) hv
    change t + t = 0 at hone
    exact ht (by linarith)
  exact h.middle_reflected_of_dihedral_translation_square g v hv
    (N4Axial.vertical_translation_square g t hg)
    (N4Axial.horizontal_conjugates_vertical_translation g t hg) himage

/-- In the normalized outer-pair configuration, no vertical translation can
send one middle tile to the other while a tile protects the square center. -/
theorem false_of_middle_vertical_translation
    (h : Configuration d) (hc : d.HasProtectedCenter)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (t : ℝ)
    (hg : ∀ p, (g p) 0 = p 0 ∧ (g p) 1 = p 1 + t)
    (himage : g '' d.piece 2 = d.piece 3) : False := by
  by_cases ht : t = 0
  · have hfix : g squareCenter = squareCenter := by
      apply PlaneIsometries.plane_ext
      · exact (hg squareCenter).1
      · simpa only [ht, add_zero] using (hg squareCenter).2
    have hnot := d.center_not_mem_fixed_pair (by decide : (2 : Fin 4) ≠ 3)
      g himage hfix
    exact (h.center_in_middle hc).elim hnot.1 hnot.2
  · have himageH := h.middle_reflected_of_vertical_translation g t ht hg himage
    have hnot := d.center_not_mem_fixed_pair (by decide : (2 : Fin 4) ≠ 3)
      ReflectionSeparation.horizontal himageH ReflectionSeparation.horizontal_center
    exact (h.center_in_middle hc).elim hnot.1 hnot.2

end Puzzling139335.N4OuterPair.Configuration
