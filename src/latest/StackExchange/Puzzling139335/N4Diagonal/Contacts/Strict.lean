import StackExchange.Puzzling139335.N4Midline.Contacts.Strict

/-!
# Strict facing contacts in the diagonal model

When the two diagonal parameters have a strict gap smaller than a
quarter-turn, each facing coordinate can reach level one only at the
opposite supporting vertex. These statements use the actual set and do
not require any convexity assumption.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

noncomputable section

theorem ray_add_pi (θ : ℝ) : ray (θ + Real.pi) = -ray θ := by
  calc
    ray (θ + Real.pi) = ray ((θ + Real.pi / 2) + Real.pi / 2) := by
      congr 1
      ring
    _ = perpRay (θ + Real.pi / 2) := N4Midline.ray_add_pi_div_two _
    _ = -ray θ := N4Midline.perp_add_pi_div_two _

theorem perp_add_pi (θ : ℝ) : perpRay (θ + Real.pi) = -perpRay θ := by
  calc
    perpRay (θ + Real.pi) = perpRay ((θ + Real.pi / 2) + Real.pi / 2) := by
      congr 1
      ring
    _ = -ray (θ + Real.pi / 2) := N4Midline.perp_add_pi_div_two _
    _ = -perpRay θ := by rw [N4Midline.ray_add_pi_div_two]

/-- The facing coordinate at the first vertex can contact level one
only at the last vertex when the diagonal angle gap is strict. -/
theorem first_contact_subset_last_corner {P : Set Plane} {p q : Plane} {θ β : ℝ}
    (hconeQ : P ⊆ supportCone q (β + Real.pi))
    (hbound : inner ℝ (perpRay θ) (q - p) ≤ 1)
    (hgaplo : 0 < β - θ) (hgaphigh : β - θ < Real.pi / 2) :
    N4Midline.levelOneContact P p (perpRay θ) ⊆ {q} := by
  have hcontact := N4Midline.first_contact_subset_last_corner
    (B := p) (C := q) (θ := θ + Real.pi / 2) (φ := β + Real.pi)
    hconeQ (by simpa only [N4Midline.ray_add_pi_div_two] using hbound)
    (by linarith) (by linarith)
  simpa only [N4Midline.ray_add_pi_div_two] using hcontact

/-- The facing coordinate at the last vertex can contact level one
only at the first vertex when the diagonal angle gap is strict. -/
theorem last_contact_subset_first_corner {P : Set Plane} {p q : Plane} {θ β : ℝ}
    (hconeP : P ⊆ supportCone p (θ + Real.pi / 2))
    (hbound : inner ℝ (-perpRay β) (p - q) ≤ 1)
    (hgaplo : 0 < β - θ) (hgaphigh : β - θ < Real.pi / 2) :
    N4Midline.levelOneContact P q (-perpRay β) ⊆ {p} := by
  have hcontact := N4Midline.last_contact_subset_first_corner
    (B := p) (C := q) (θ := θ + Real.pi / 2) (φ := β + Real.pi)
    hconeP (by simpa only [perp_add_pi] using hbound)
    (by linarith) (by linarith)
  simpa only [perp_add_pi] using hcontact

end

end Puzzling139335.N4Diagonal
