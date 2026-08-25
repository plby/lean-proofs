import StackExchange.Puzzling139335.N4Diagonal.Placements

/-!
# Reflecting the whole normalized configuration

The anti-diagonal reflection interchanges the two repeated copies and
fixes the two singleton square corners. Applying it to the whole tiling
therefore changes both singleton placement parities while leaving the
prototype, its supporting frames, and all coverage hypotheses intact.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ReflectionSeparation

noncomputable section

theorem antiDiagonal_corner (j : Fin 4) :
    antiDiagonal (corner j) = corner (2 - j) := by
  fin_cases j <;> ext i <;> fin_cases i <;> norm_num [corner, Fin.ext_iff, Fin.sub_def]

theorem antiDiagonal_corner_fixed (j : Fin 4) (hj : j = 1 ∨ j = 3) :
    antiDiagonal (corner j) = corner j := by
  rcases hj with rfl | rfl <;> ext i <;> fin_cases i <;>
    norm_num [corner, Fin.ext_iff]

theorem antiDiagonal_image_image (P : Set Plane) :
    antiDiagonal '' (antiDiagonal '' P) = P := by
  rw [image_image]
  simp only [antiDiagonal_involutive, image_id']

theorem mem_antiDiagonal_image_iff {P : Set Plane} {x : Plane} :
    x ∈ antiDiagonal '' P ↔ antiDiagonal x ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [antiDiagonal_involutive] using hy
  · intro hx
    exact ⟨antiDiagonal x, hx, antiDiagonal_involutive x⟩

theorem trans_antiDiagonal_image (e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    (e.trans antiDiagonal) '' P = antiDiagonal '' (e '' P) := by
  rw [image_image]
  rfl

theorem only_corner_antiDiagonal_image {P : Set Plane} {j : Fin 4}
    (hj : j = 1 ∨ j = 3) (honly : ∀ k, corner k ∈ P → k = j) :
    ∀ k, corner k ∈ antiDiagonal '' P → k = j := by
  intro k hk
  have hmem := mem_antiDiagonal_image_iff.mp hk
  rw [antiDiagonal_corner] at hmem
  have hkj := honly (2 - k) hmem
  have hp : antiDiagonal (corner k) = corner j := by
    rw [antiDiagonal_corner, hkj]
  have hp' := congrArg antiDiagonal hp
  rw [antiDiagonal_involutive, antiDiagonal_corner_fixed j hj] at hp'
  exact corner_injective hp'

theorem pieces_reflected (P : Set Plane) (e f : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 4) :
    pieces P (e.trans antiDiagonal) (f.trans antiDiagonal) i =
      antiDiagonal '' pieces P e f (Equiv.swap 0 2 i) := by
  fin_cases i <;>
    simp [pieces, Equiv.swap_apply_def, image_image, antiDiagonal_involutive]

namespace Model

/-- Apply the anti-diagonal reflection to all four actual copies, and
exchange the names of the two repeated copies. -/
def reflect (m : Model) : Model :=
  { m with
    e := m.e.trans antiDiagonal
    f := m.f.trans antiDiagonal
    first_subset := by
      rw [trans_antiDiagonal_image]
      rintro _ ⟨x, hx, rfl⟩
      exact antiDiagonal_mem_unitSquare.mpr (m.first_subset hx)
    last_subset := by
      rw [trans_antiDiagonal_image]
      rintro _ ⟨x, hx, rfl⟩
      exact antiDiagonal_mem_unitSquare.mpr (m.last_subset hx)
    first_corner := by
      change antiDiagonal (m.e m.p) = corner m.firstCorner
      rw [m.first_corner, antiDiagonal_corner_fixed m.firstCorner m.firstCorner_one_or_three]
    last_corner := by
      change antiDiagonal (m.f m.q) = corner m.lastCorner
      rw [m.last_corner, antiDiagonal_corner_fixed m.lastCorner m.lastCorner_one_or_three]
    first_only_corner := by
      rw [trans_antiDiagonal_image]
      exact only_corner_antiDiagonal_image m.firstCorner_one_or_three m.first_only_corner
    last_only_corner := by
      rw [trans_antiDiagonal_image]
      exact only_corner_antiDiagonal_image m.lastCorner_one_or_three m.last_only_corner
    cover := by
      intro x hx
      have hx' := antiDiagonal_mem_unitSquare.mpr hx
      rcases m.cover (antiDiagonal x) hx' with hp | hq | he | hf
      · exact Or.inr (Or.inl (mem_antiDiagonal_image_iff.mpr hp))
      · exact Or.inl (by simpa only [antiDiagonal_involutive] using
          mem_antiDiagonal_image_iff.mp hq)
      · exact Or.inr (Or.inr (Or.inl (by
          rw [trans_antiDiagonal_image]
          exact mem_antiDiagonal_image_iff.mpr he)))
      · exact Or.inr (Or.inr (Or.inr (by
          rw [trans_antiDiagonal_image]
          exact mem_antiDiagonal_image_iff.mpr hf)))
    disjoint := by
      intro i j hij
      rw [pieces_reflected, pieces_reflected]
      exact RectangularHull.disjoint_interiors_image_homeomorph
        (m.disjoint ((Equiv.swap (0 : Fin 4) 2).injective.ne hij))
        antiDiagonal.toHomeomorph }

theorem reflect_first_form (m : Model)
    (hform : ∀ x, m.e x = firstMinus m.firstCorner m.p m.θ x) :
    ∀ x, m.reflect.e x = firstPlus m.reflect.firstCorner m.reflect.p m.reflect.θ x := by
  intro x
  change antiDiagonal (m.e x) = firstPlus m.firstCorner m.p m.θ x
  rw [hform, firstMinus, antiDiagonal_involutive]

theorem reflect_first_center_iff (m : Model) :
    squareCenter ∈ interior (m.reflect.e '' m.reflect.P) ↔
      squareCenter ∈ interior (m.e '' m.P) := by
  change squareCenter ∈ interior ((m.e.trans antiDiagonal) '' m.P) ↔ _
  rw [trans_antiDiagonal_image]
  simpa only [antiDiagonal_center] using
    (mem_interior_image_affineIsometry antiDiagonal (P := m.e '' m.P)
      (p := squareCenter))

theorem reflect_last_center_iff (m : Model) :
    squareCenter ∈ interior (m.reflect.f '' m.reflect.P) ↔
      squareCenter ∈ interior (m.f '' m.P) := by
  change squareCenter ∈ interior ((m.f.trans antiDiagonal) '' m.P) ↔ _
  rw [trans_antiDiagonal_image]
  simpa only [antiDiagonal_center] using
    (mem_interior_image_affineIsometry antiDiagonal (P := m.f '' m.P)
      (p := squareCenter))

end Model

end

end Puzzling139335.N4Diagonal
