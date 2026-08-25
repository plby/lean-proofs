import StackExchange.Puzzling139335.N4Diagonal.Transpose.Coordinates

/-!
# Images under coordinate transposition

The transpose conjugates the actual placement isometries and exchanges the
two singleton copies. The identities below concern their actual images,
including the reflected prototype.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ReflectionSeparation

noncomputable section

theorem diagonal_image_image (P : Set Plane) :
    diagonal '' (diagonal '' P) = P := by
  rw [image_image]
  simp only [diagonal_involutive, image_id']

theorem mem_diagonal_image_iff {P : Set Plane} {x : Plane} :
    x ∈ diagonal '' P ↔ diagonal x ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [diagonal_involutive] using hy
  · intro hx
    exact ⟨diagonal x, hx, diagonal_involutive x⟩

/-- Conjugating an actual placement by the coordinate transpose. -/
def transposeIsometry (e : Plane ≃ᵃⁱ[ℝ] Plane) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (diagonal.trans e).trans diagonal

@[simp] theorem transposeIsometry_apply (e : Plane ≃ᵃⁱ[ℝ] Plane) (x : Plane) :
    transposeIsometry e x = diagonal (e (diagonal x)) := rfl

theorem transposeIsometry_image (e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    transposeIsometry e '' (diagonal '' P) = diagonal '' (e '' P) := by
  simp only [image_image, transposeIsometry_apply,
    diagonal_involutive]

theorem antiDiagonal_diagonal_image (P : Set Plane) :
    antiDiagonal '' (diagonal '' P) = diagonal '' (antiDiagonal '' P) := by
  simp only [image_image, diagonal_antiDiagonal_commute]

theorem only_corner_diagonal_image {P : Set Plane} {j : Fin 4}
    (honly : ∀ k, corner k ∈ P → k = j) :
    ∀ k, corner k ∈ diagonal '' P → k = -j := by
  intro k hk
  have hmem := mem_diagonal_image_iff.mp hk
  rw [diagonal_corner] at hmem
  have hkj := honly (-k) hmem
  simpa only [neg_neg] using congrArg Neg.neg hkj

theorem pieces_transposed (P : Set Plane) (e f : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 4) :
    pieces (diagonal '' P) (transposeIsometry f) (transposeIsometry e) i =
      diagonal '' pieces P e f (Equiv.swap 1 3 i) := by
  fin_cases i <;>
    simp [pieces, Equiv.swap_apply_def, transposeIsometry_image,
      antiDiagonal_diagonal_image]

end

end Puzzling139335.N4Diagonal
