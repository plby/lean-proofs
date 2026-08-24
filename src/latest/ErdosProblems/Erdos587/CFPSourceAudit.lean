import Mathlib

/-!
An auxiliary projection-index inference in the proof labelled
`lem:stable-implies-span` in arXiv:2311.01416v1 cannot be used as written.
The kernel of `(x,y) ↦ x+y mod M` has index `M`, while both coordinate
projections are surjective. This is not a counterexample to the CFP theorem.
-/

namespace Erdos587.CFP

def diagonalResidueHom (M : ℕ) : ℤ × ℤ →+ ZMod M where
  toFun p := (p.1 : ZMod M) + (p.2 : ZMod M)
  map_zero' := by simp
  map_add' p q := by
    change ((p.1 + q.1 : ℤ) : ZMod M) + ((p.2 + q.2 : ℤ) : ZMod M) = _
    push_cast
    abel

theorem diagonalResidueHom_surjective (M : ℕ) [NeZero M] :
    Function.Surjective (diagonalResidueHom M) := by
  intro z
  refine ⟨((z.val : ℤ), 0), ?_⟩
  simp [diagonalResidueHom]

theorem diagonal_kernel_index (M : ℕ) [NeZero M] :
    (diagonalResidueHom M).ker.index = M := by
  rw [AddSubgroup.index_ker,
    (diagonalResidueHom M).range_eq_top_of_surjective (diagonalResidueHom_surjective M),
    AddSubgroup.card_top]
  simp

theorem diagonal_kernel_fst_surjective (M : ℕ) :
    Function.Surjective (fun x : (diagonalResidueHom M).ker => x.val.1) := by
  intro z
  refine ⟨⟨(z, -z), ?_⟩, rfl⟩
  change (z : ZMod M) + ((-z : ℤ) : ZMod M) = 0
  simp

theorem diagonal_kernel_snd_surjective (M : ℕ) :
    Function.Surjective (fun x : (diagonalResidueHom M).ker => x.val.2) := by
  intro z
  refine ⟨⟨(-z, z), ?_⟩, rfl⟩
  change ((-z : ℤ) : ZMod M) + (z : ZMod M) = 0
  simp

theorem exists_index_with_surjective_coordinate_projections (M : ℕ) (hM : 0 < M) :
    ∃ Γ : AddSubgroup (ℤ × ℤ), Γ.index = M ∧
      Function.Surjective (fun x : Γ => x.val.1) ∧
      Function.Surjective (fun x : Γ => x.val.2) := by
  letI : NeZero M := ⟨by omega⟩
  exact ⟨(diagonalResidueHom M).ker, diagonal_kernel_index M,
    diagonal_kernel_fst_surjective M, diagonal_kernel_snd_surjective M⟩

end Erdos587.CFP
