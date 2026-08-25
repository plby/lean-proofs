import StackExchange.Puzzling139335.N4HalfLeg.Defs
import StackExchange.Puzzling139335.Transform

/-!
# Interchanging the two outer side legs

Vertical reflection is applied to every actual piece. It preserves the
horizontal outer-pair relation and exchanges the two bottom corners.
-/

open Set

namespace Puzzling139335.N4HalfLeg

open ReflectionSeparation

noncomputable section

theorem vertical_corner (j : Fin 4) : vertical (corner j) = corner (1 - j) := by
  fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [corner, Fin.ext_iff, Fin.sub_def]

theorem horizontal_vertical_commute (x : Plane) :
    horizontal (vertical x) = vertical (horizontal x) := by
  ext i
  fin_cases i <;> simp

/-- The vertically reflected actual dissection has the same outer-pair
configuration, without changing any piece index. -/
def reflectedConfiguration {d : SquareDissection} (h : N4OuterPair.Configuration d) :
    N4OuterPair.Configuration (d.map vertical vertical_image_unitSquare) where
  bottom_left := by
    change corner 0 ∈ vertical '' d.piece 0
    exact ⟨corner 1, h.bottom_right, by
      rw [vertical_corner]
      norm_num⟩
  bottom_right := by
    change corner 1 ∈ vertical '' d.piece 0
    exact ⟨corner 0, h.bottom_left, by
      rw [vertical_corner]
      norm_num⟩
  reflected := by
    change horizontal '' (vertical '' d.piece 0) = vertical '' d.piece 1
    calc
      horizontal '' (vertical '' d.piece 0) = vertical '' (horizontal '' d.piece 0) := by
        rw [image_image, image_image]
        congr 1
        funext x
        exact horizontal_vertical_commute x
      _ = vertical '' d.piece 1 := by rw [h.reflected]
  middle_cornerless := by
    intro i hi j hj
    change corner j ∈ vertical '' d.piece i at hj
    obtain ⟨p, hp, hpj⟩ := hj
    have hmem : vertical (corner j) ∈ d.piece i := by
      rw [← hpj, vertical_involutive]
      exact hp
    rw [vertical_corner] at hmem
    exact h.middle_cornerless i hi (1 - j) hmem

theorem reflectedConfiguration_protected {d : SquareDissection}
    (hc : d.HasProtectedCenter) :
    (d.map vertical vertical_image_unitSquare).HasProtectedCenter :=
  (d.map_hasProtectedCenter vertical vertical_image_unitSquare).mpr hc

theorem left_halfleg_mem_of_right {d : SquareDissection}
    (h : Schoenflies.Plane.mk 1 (1 / 2) ∈ d.piece 0) :
    Schoenflies.Plane.mk 0 (1 / 2) ∈
      (d.map vertical vertical_image_unitSquare).piece 0 := by
  change Schoenflies.Plane.mk 0 (1 / 2) ∈ vertical '' d.piece 0
  refine ⟨Schoenflies.Plane.mk 1 (1 / 2), h, ?_⟩
  ext i
  fin_cases i <;> norm_num

end

end Puzzling139335.N4HalfLeg
