import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic

/-!
# Relabeling a pair of dissection pieces

Any two distinct piece indices can be placed first in a permutation of the
four pieces. The remaining indices then avoid both chosen pieces.
-/

namespace Puzzling139335.RectangularHull

/-- Relabel two distinct pieces as pieces `0` and `1`. -/
theorem exists_piece_relabeling {i j : Fin 4} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  have hτ0 : τ 0 = i := Equiv.swap_apply_left _ _
  have hi : i ≠ τ 1 := by
    rw [← hτ0]
    exact τ.injective.ne (by decide)
  refine ⟨τ.trans (Equiv.swap (τ 1) j), ?_, ?_⟩
  · change Equiv.swap (τ 1) j (τ 0) = i
    rw [hτ0, Equiv.swap_apply_of_ne_of_ne hi hij]
  · exact Equiv.swap_apply_left _ _

/-- An index other than `0` and `1` avoids both distinguished pieces. -/
theorem piece_relabeling_ne {σ : Equiv.Perm (Fin 4)} {i j : Fin 4}
    (h0 : σ 0 = i) (h1 : σ 1 = j) {k : Fin 4}
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) : σ k ≠ i ∧ σ k ≠ j := by
  constructor
  · intro h
    exact hk0 (σ.injective (h.trans h0.symm))
  · intro h
    exact hk1 (σ.injective (h.trans h1.symm))

/-- The last two indices avoid both pieces placed first by the relabeling. -/
theorem piece_relabeling_middle_ne {σ : Equiv.Perm (Fin 4)} {i j : Fin 4}
    (h0 : σ 0 = i) (h1 : σ 1 = j) {k : Fin 4}
    (hk : k = 2 ∨ k = 3) : σ k ≠ i ∧ σ k ≠ j := by
  rcases hk with rfl | rfl
  · exact piece_relabeling_ne h0 h1 (by decide) (by decide)
  · exact piece_relabeling_ne h0 h1 (by decide) (by decide)

end Puzzling139335.RectangularHull
