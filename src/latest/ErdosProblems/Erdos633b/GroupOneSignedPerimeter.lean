import ErdosProblems.Erdos633b.OrientedLengthCancellation
import ErdosProblems.Erdos633b.GroupOneColoring
import ErdosProblems.Erdos633b.SignedTrianglePerimeter

/-! The group-1 direction coloring yields an actual signed-perimeter
identity with a nonzero integer signed tile count of absolute value at most n. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

def paritySign (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem paritySign_unit (x : ZMod 2) : paritySign x = 1 ∨ paritySign x = -1 := by
  unfold paritySign
  split_ifs <;> simp

theorem paritySign_add_one (x : ZMod 2) : paritySign (x + 1) = -paritySign x := by
  revert x
  decide

theorem abs_paritySign (x : ZMod 2) : |paritySign x| = 1 := by
  rcases paritySign_unit x with h | h <;> simp only [h, abs_one, abs_neg]

namespace Tiling

theorem exists_groupOne_signed_perimeter {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) :
    ∃ c : Fin n → ℤ, ∃ ε : Fin 3 → ℤ,
      (∀ a, c a = 1 ∨ c a = -1) ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∑ a, c a) ≠ 0 ∧ |∑ a, c a| ≤ (n : ℤ) ∧
      ((∑ a, c a : ℤ) : ℝ) * (∑ j : Fin 3, d.tile.side j) =
        ∑ i : Fin 3, (ε i : ℝ) * T.side i := by
  obtain ⟨f, hf, ht, _⟩ := d.tile.exists_groupOne_direction_color hrel hirr
  let w : Real.Angle → ℝ := fun x => paritySign (f x)
  let c (a : Fin n) : ℤ := paritySign
    (f ((d.tile.move (d.place a)).positiveEdgeDirection o u 0))
  let ε (i : Fin 3) : ℤ := paritySign (f (T.positiveEdgeDirection o u i))
  have hodd (x : Real.Angle) : w (x + (Real.pi : Real.Angle)) = -w x := by
    simp only [w, hf, paritySign_add_one, Int.cast_neg]
  have hc (a : Fin n) (j : Fin 3) :
      w ((d.tile.move (d.place a)).positiveEdgeDirection o u j) = (c a : ℝ) := by
    dsimp only [w, c]
    congr 2
    apply Triangle.positive_edge_color _ o hu f hf
    intro x k
    simpa only [Triangle.angle_move] using ht x k
  have he := d.oriented_edge_length_cancellation o hu w hodd
  simp_rw [hc] at he
  simp_rw [← Finset.sum_mul] at he
  rw [← Finset.mul_sum] at he
  have hsum : ((∑ a, c a : ℤ) : ℝ) * (∑ j : Fin 3, d.tile.side j) =
      ∑ i : Fin 3, (ε i : ℝ) * T.side i := by
    simpa only [Int.cast_sum, w, ε, mul_comm] using he
  have hunit (a : Fin n) : c a = 1 ∨ c a = -1 := paritySign_unit _
  have hε (i : Fin 3) : ε i = 1 ∨ ε i = -1 := paritySign_unit _
  refine ⟨c, ε, hunit, hε, ?_, ?_, hsum⟩
  · intro hz
    rw [hz, Int.cast_zero, zero_mul] at hsum
    exact T.signed_side_sum_ne_zero ε hε hsum.symm
  · calc
      |∑ a, c a| ≤ ∑ a : Fin n, |c a| := Finset.abs_sum_le_sum_abs _ _
      _ = (n : ℤ) := by simp only [c, abs_paritySign, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end Tiling
end Erdos633b
