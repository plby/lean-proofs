import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductDiagonal

/-!
# Linear equations for the squared coordinates of a diagonal preimage

Conjugating the diagonal relation eliminates the real norm term. Whenever
the resulting coefficient is nonzero, the squared coordinate is determined.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

def diagonalCoefficient (d t : ℂ) : ℂ := d ^ 3 + star t * d ^ 2 - t * d - 1

def diagonalNumerator (d t : ℂ) : ℂ := t * d ^ 3 - star t * d

theorem squared_coordinate_elimination (x d t : ℂ) (hu : d * star d = 1)
    (hp : x ^ 2 = d * star x ^ 2)
    (he : d = star t - t * x ^ 2 + 2 * d * (Complex.normSq x : ℂ) - star x ^ 2) :
    diagonalCoefficient d t * x ^ 2 = diagonalNumerator d t := by
  have hstar : star d = t - star t * star x ^ 2 +
      2 * star d * (Complex.normSq x : ℂ) - x ^ 2 := by
    simpa [Complex.star_def] using congrArg star he
  unfold diagonalCoefficient diagonalNumerator
  linear_combination d ^ 3 * hstar - d * he +
    (2 * d ^ 2 * (Complex.normSq x : ℂ) - d ^ 2) * hu +
    (star t * d ^ 2 - 1) * hp

theorem diagonal_squared_coordinate (z : UnitSphere) (d : Fin 3 → ℂ)
    (hd : (symmetricMap z).val.val = Matrix.diagonal d) (r : Fin 3) :
    diagonalCoefficient (d r) (squareSum z.val) * z.val r ^ 2 =
      diagonalNumerator (d r) (squareSum z.val) :=
  squared_coordinate_elimination _ _ _ (diagonal_entry_unitary z d hd r)
    (diagonal_phase_equation z d hd r) (diagonal_square_norm_relation z d hd r)

theorem diagonal_squared_coordinate_eq (z : UnitSphere) (d : Fin 3 → ℂ)
    (hd : (symmetricMap z).val.val = Matrix.diagonal d) (r : Fin 3)
    (hc : diagonalCoefficient (d r) (squareSum z.val) ≠ 0) :
    z.val r ^ 2 = diagonalNumerator (d r) (squareSum z.val) /
      diagonalCoefficient (d r) (squareSum z.val) := by
  apply (eq_div_iff hc).mpr
  rw [mul_comm]
  exact diagonal_squared_coordinate z d hd r

theorem diagonal_same_squared_coordinate (z w : UnitSphere) (d : Fin 3 → ℂ)
    (hz : (symmetricMap z).val.val = Matrix.diagonal d)
    (hw : (symmetricMap w).val.val = Matrix.diagonal d)
    (ht : squareSum z.val = squareSum w.val) (r : Fin 3)
    (hc : diagonalCoefficient (d r) (squareSum z.val) ≠ 0) : z.val r ^ 2 = w.val r ^ 2 := by
  apply mul_left_cancel₀ hc
  rw [diagonal_squared_coordinate z d hz r, ht, diagonal_squared_coordinate w d hw r]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
