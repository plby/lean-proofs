import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessPieces

/-!
# Euler sums of the original star-cover terms

Rationalization commutes with the finite products of actual piece and
overlap homology groups.  The regular term and every overlap have Euler
sum zero.  The two original elliptic pieces have Euler sum zero, and the
original fixed-radius cusp piece has Euler sum two.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

open SingularMayerVietoris

/-- The rational dimension of the literal product of the three overlap groups. -/
theorem starOverlapRationalHomology_finrank (n : ℕ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] StarOverlapHomology n) =
      ∑ i : Puncture, Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (RegularOverlap i) n) := by
  have : ∀ i : Puncture, Module.Finite ℤ (SingularHomology (RegularOverlap i) n) :=
    fun i => overlapHomology_finite i n
  exact rational_finrank_pi_int (fun i : Puncture => SingularHomology (RegularOverlap i) n)

/-- The rational dimension of the literal product of the three filling groups. -/
theorem starFillingRationalHomology_finrank (n : ℕ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] StarFillingHomology n) =
      ∑ i : Puncture,
        Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some i)) n) := by
  have : ∀ i : Puncture, Module.Finite ℤ (SingularHomology (localPiece (some i)) n) :=
    fun i => fillingHomology_finite i n
  exact rational_finrank_pi_int (fun i : Puncture => SingularHomology (localPiece (some i)) n)

/-- The rational dimension of the actual middle term of the star sequence. -/
theorem starPairRationalHomology_finrank (n : ℕ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] StarPairHomology n) =
      Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology SpecialRegularFamily n) +
        ∑ i : Puncture,
          Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some i)) n) := by
  have := regularHomology_finite n
  have := starFillingHomology_finite n
  rw [rational_finrank_prod_int
    (SingularHomology SpecialRegularFamily n) (StarFillingHomology n)]
  rw [starFillingRationalHomology_finrank]

/-- Every genuine overlap is an actual mapping torus, so their combined
Euler sum is zero. -/
theorem starOverlapRationalHomology_euler_of_le {N : ℕ} (hN : 6 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℚ (ℚ ⊗[ℤ] StarOverlapHomology n) : ℤ)) = 0 := by
  simp only [starOverlapRationalHomology_finrank, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [overlapRationalHomology_euler_of_le _ hN, Finset.sum_const_zero]

/-- The two elliptic contributions vanish and the genuine cusp contribution is two. -/
theorem fillingRationalHomology_euler_sum {N : ℕ} (hN : 5 ≤ N) :
    (∑ i : Puncture, ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some i)) n) : ℤ)) = 2 := by
  rw [Fintype.sum_option]
  simp only [ellipticPieceRationalHomology_euler_of_le _ hN,
    cuspPieceRationalHomology_euler_of_le hN, Finset.sum_const_zero, add_zero]

/-- Euler sum of the literal regular-plus-fillings term. -/
theorem starPairRationalHomology_euler_of_le {N : ℕ} (hN : 6 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℚ (ℚ ⊗[ℤ] StarPairHomology n) : ℤ)) = 2 := by
  simp only [starPairRationalHomology_finrank, Nat.cast_add, Nat.cast_sum,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [regularRationalHomology_euler_of_le hN, zero_add, Finset.sum_comm]
  exact fillingRationalHomology_euler_sum (by omega)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
