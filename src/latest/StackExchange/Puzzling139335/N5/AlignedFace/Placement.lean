import StackExchange.Puzzling139335.N5.AlignedFace.RowClassification
import StackExchange.Puzzling139335.N5.AlignedFace.IntervalMatching

/-!
# Exact aligned placements from actual top-contact intervals

The common top row first gives the same vertical translation.  Matching
the actual interval endpoints then determines the horizontal displacement
or reflection axis and proves equality of the two top-contact lengths.
-/

open Set

namespace Puzzling139335.N5.AlignedFace

open PlaneIsometries

/-- Exact top contacts determine both the aligned placement and their
common length.  No source-face length is assumed in the hypotheses. -/
theorem placement_of_top_intervals
    {P : Set Plane} (eR eD : Plane ≃ᵃⁱ[ℝ] Plane) {u v c s b m : ℝ}
    (hRform : ∀ p : Plane, eR p =
      !₂[u - s * p 0 + c * p 1, v + c * p 0 + s * p 1])
    (hD10 : linearMatrix eD 1 0 = c) (hD11 : linearMatrix eD 1 1 = s)
    (hRfit : eR '' P ⊆ unitSquare) (hDfit : eD '' P ⊆ unitSquare)
    (hbm : b < m) (hm1 : m < 1)
    (hRtop : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ eR '' P ↔ m ≤ x ∧ x ≤ 1)
    (hDtop : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ eD '' P ↔ b ≤ x ∧ x ≤ m) :
    2 * m = 1 + b ∧
      ((∀ p : Plane, eD p = !₂[(eR p) 0 - (1 - m), (eR p) 1]) ∨
       (∀ p : Plane, eD p = !₂[1 + b - (eR p) 0, (eR p) 1])) := by
  have hRtop' : ∃ p ∈ P, (eR p) 1 = 1 := by
    obtain ⟨p, hp, hpeq⟩ := (hRtop 1).mpr ⟨hm1.le, le_rfl⟩
    exact ⟨p, hp, congrArg (fun q : Plane => q 1) hpeq⟩
  have hDtop' : ∃ p ∈ P, (eD p) 1 = 1 := by
    obtain ⟨p, hp, hpeq⟩ := (hDtop b).mpr ⟨le_rfl, hbm.le⟩
    exact ⟨p, hp, congrArg (fun q : Plane => q 1) hpeq⟩
  rcases exists_aligned_affine_form_of_top_contacts eR eD hRform hD10 hD11
      hRfit hDfit hRtop' hDtop' with ⟨δ, hδ⟩ | ⟨κ, hκ⟩
  · have hx (p : Plane) : eD p 0 = eR p 0 + δ := by rw [hδ p]; rfl
    have hy (p : Plane) : eD p 1 = eR p 1 := by rw [hδ p]; rfl
    obtain ⟨hδm, _, hequal⟩ :=
      translation_interval_matching hbm hm1 hRtop hDtop hx hy
    refine ⟨hequal, Or.inl ?_⟩
    intro p
    rw [hδ p, hδm]
    apply plane_ext
    · change eR p 0 + (m - 1) = eR p 0 - (1 - m)
      ring
    · rfl
  · have hx (p : Plane) : eD p 0 = κ - eR p 0 := by rw [hκ p]; rfl
    have hy (p : Plane) : eD p 1 = eR p 1 := by rw [hκ p]; rfl
    obtain ⟨_, hκb, hequal⟩ :=
      reflection_interval_matching hbm hm1 hRtop hDtop hx hy
    refine ⟨hequal, Or.inr ?_⟩
    intro p
    simpa only [hκb] using hκ p

/-- In the notation of the dissection, the incoming contact length `T`
equals the fourth piece's top gap `j`, and the remaining side length is
twice either one. -/
theorem contact_lengths_of_top_intervals
    {P : Set Plane} (eR eD : Plane ≃ᵃⁱ[ℝ] Plane) {u v c s b m : ℝ}
    (hRform : ∀ p : Plane, eR p =
      !₂[u - s * p 0 + c * p 1, v + c * p 0 + s * p 1])
    (hD10 : linearMatrix eD 1 0 = c) (hD11 : linearMatrix eD 1 1 = s)
    (hRfit : eR '' P ⊆ unitSquare) (hDfit : eD '' P ⊆ unitSquare)
    (hbm : b < m) (hm1 : m < 1)
    (hRtop : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ eR '' P ↔ m ≤ x ∧ x ≤ 1)
    (hDtop : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ eD '' P ↔ b ≤ x ∧ x ≤ m) :
    1 - m = m - b ∧ 1 - b = 2 * (1 - m) := by
  have hequal := (placement_of_top_intervals eR eD hRform hD10 hD11
    hRfit hDfit hbm hm1 hRtop hDtop).1
  constructor <;> linarith only [hequal]

end Puzzling139335.N5.AlignedFace
