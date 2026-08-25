import StackExchange.Puzzling139335.N4TwoOneOne.Orientation
import StackExchange.Puzzling139335.Transform

/-!
# Removing the singleton orientation choice

Reflection of the whole square, followed by interchange of the two singleton
labels, reverses the source congruence's parity. Thus every actual normalized
corner configuration reduces to the coordinate data used by the geometric
obstruction, while preserving the protected-center property.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

open ReflectionSeparation PlaneIsometries

noncomputable section

def mirror (d : SquareDissection) : SquareDissection :=
  (d.map vertical vertical_image_unitSquare).reindex (Equiv.swap 1 2)

@[simp] theorem mirror_piece_zero (d : SquareDissection) :
    (mirror d).piece 0 = vertical '' d.piece 0 := by
  simp [mirror, SquareDissection.reindex, Equiv.swap_apply_def]

@[simp] theorem mirror_piece_one (d : SquareDissection) :
    (mirror d).piece 1 = vertical '' d.piece 2 := by
  simp [mirror, SquareDissection.reindex]

@[simp] theorem mirror_piece_two (d : SquareDissection) :
    (mirror d).piece 2 = vertical '' d.piece 1 := by
  simp [mirror, SquareDissection.reindex]

@[simp] theorem mirror_piece_three (d : SquareDissection) :
    (mirror d).piece 3 = vertical '' d.piece 3 := by
  simp [mirror, SquareDissection.reindex, Equiv.swap_apply_def]

@[simp] theorem mirror_hasProtectedCenter (d : SquareDissection) :
    (mirror d).HasProtectedCenter ↔ d.HasProtectedCenter := by
  simp [mirror]

def mirrorCorner : Fin 4 → Fin 4 := ![1, 0, 3, 2]

theorem vertical_corner (k : Fin 4) : vertical (corner k) = corner (mirrorCorner k) := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    norm_num [mirrorCorner, corner, Fin.ext_iff]

theorem vertical_image_vertical (P : Set Plane) : vertical '' (vertical '' P) = P := by
  simp only [image_image, vertical_involutive, image_id']

theorem Configuration.reflected_configuration {d : SquareDissection} (h : Configuration d) :
    Configuration (mirror d) := by
  constructor
  · rw [mirror_piece_zero]
    have hm := mem_image_of_mem vertical h.bottom_right
    simpa [vertical_corner, mirrorCorner] using hm
  · rw [mirror_piece_zero]
    have hm := mem_image_of_mem vertical h.bottom_left
    simpa [vertical_corner, mirrorCorner] using hm
  · rw [mirror_piece_one]
    have hm := mem_image_of_mem vertical h.top_left
    simpa [vertical_corner, mirrorCorner] using hm
  · rw [mirror_piece_two]
    have hm := mem_image_of_mem vertical h.top_right
    simpa [vertical_corner, mirrorCorner] using hm
  · intro k hk
    rw [mirror_piece_one] at hk
    obtain ⟨p, hp, hpk⟩ := hk
    have hpre : corner (mirrorCorner k) ∈ d.piece 2 := by
      have heq := congrArg vertical hpk
      rw [vertical_involutive, vertical_corner] at heq
      exact heq ▸ hp
    have hidx := h.left_singleton _ hpre
    fin_cases k <;> simp_all [mirrorCorner, Fin.ext_iff]
  · intro k hk
    rw [mirror_piece_two] at hk
    obtain ⟨p, hp, hpk⟩ := hk
    have hpre : corner (mirrorCorner k) ∈ d.piece 1 := by
      have heq := congrArg vertical hpk
      rw [vertical_involutive, vertical_corner] at heq
      exact heq ▸ hp
    have hidx := h.right_singleton _ hpre
    fin_cases k <;> simp_all [mirrorCorner, Fin.ext_iff]
  · intro k hk
    rw [mirror_piece_three] at hk
    obtain ⟨p, hp, hpk⟩ := hk
    have heq := congrArg vertical hpk
    rw [vertical_involutive, vertical_corner] at heq
    exact h.cornerless (mirrorCorner k) (heq ▸ hp)
  · rw [mirror_piece_one, mirror_piece_two, vertical_image_vertical, h.reflected]

theorem Configuration.mirrored_right_image {d : SquareDissection}
    (h : Configuration d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 1) :
    (vertical.trans e) '' (mirror d).piece 0 = (mirror d).piece 1 := by
  rw [mirror_piece_zero, mirror_piece_one, ← h.reflected, vertical_image_vertical]
  calc
    (vertical.trans e) '' (vertical '' d.piece 0) = e '' d.piece 0 := by
      simp only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_def,
        vertical_involutive]
    _ = d.piece 1 := he

theorem direct_form_after_vertical (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (hform : ∀ p, e p = reversingCoordinates c s (e 0) p) :
    ∀ p, (vertical.trans e) p =
      directCoordinates (-c) (-s) ((vertical.trans e) 0) p := by
  intro p
  change e (vertical p) = directCoordinates (-c) (-s) (e (vertical 0)) p
  rw [hform (vertical p), hform (vertical 0)]
  ext i
  fin_cases i <;> simp [reversingCoordinates, directCoordinates] <;> ring

/-- Every actual reflected-singleton configuration has a coordinate
normalization; the possible global reflection preserves all hypotheses. -/
theorem Configuration.exists_sourceData {d : SquareDissection}
    (h : Configuration d) :
    ∃ d' : SquareDissection, Configuration d' ∧
      (d'.HasProtectedCenter ↔ d.HasProtectedCenter) ∧
      ∃ θ u v : ℝ, SourceData d' θ u v := by
  obtain ⟨e, he⟩ := d.congruent 0 1
  obtain ⟨c, s, hcs, hform | hform⟩ := affine_coordinate_classification e
  · have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by simpa only [neg_sq] using hcs
    have hform' : ∀ p, e p = directCoordinates c (-(-s)) (e 0) p := by
      simpa only [neg_neg] using hform
    obtain ⟨θ, u, v, hdata, _⟩ := h.sourceData_of_direct e he hcs' hform'
    exact ⟨d, h, Iff.rfl, θ, u, v, hdata⟩
  · have hcs' : (-c) ^ 2 + s ^ 2 = 1 := by simpa only [neg_sq] using hcs
    obtain ⟨θ, u, v, hdata, _⟩ := h.reflected_configuration.sourceData_of_direct
      (vertical.trans e) (h.mirrored_right_image e he) hcs'
      (direct_form_after_vertical e hform)
    exact ⟨mirror d, h.reflected_configuration, mirror_hasProtectedCenter d, θ, u, v, hdata⟩

end

end Puzzling139335.N4TwoOneOne
