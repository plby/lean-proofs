import ErdosProblems.Erdos1148.BoundedLatticeVectors
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # A polynomial bound on the number of bounded lattice-vector candidates -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_lattice_vector_candidates_card_bound {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∃ V : Finset (ℤ × ℤ), (V.card : ℝ) ≤ (4 * A * (R + 1) + 3) ^ 2 ∧
      ∀ (g : SL(2, ℝ)), (∀ i j : Fin 2, |g i j| ≤ A) → ∀ u v : ℤ,
        modularVectorLengthSq g u v ≤ R → (u, v) ∈ V := by
  let B := 2 * A * (R + 1)
  let M : ℤ := ⌈B⌉
  let I := Finset.Icc (-M) M
  let V := I ×ˢ I
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hM : 0 ≤ M := Int.ceil_nonneg hB
  have hcard : (I.card : ℝ) = 2 * (M : ℝ) + 1 := by
    have h := Int.card_Icc_of_le (-M) M (show -M ≤ M + 1 by omega)
    have h' : (I.card : ℝ) = (M : ℝ) + 1 - -(M : ℝ) := by exact_mod_cast h
    linarith
  have hbound : (I.card : ℝ) ≤ 2 * B + 3 := by
    rw [hcard]
    have hceil : (M : ℝ) < B + 1 := Int.ceil_lt_add_one B
    linarith
  refine ⟨V, ?_, ?_⟩
  · calc
      _ = (I.card : ℝ) ^ 2 := by
        dsimp only [V]
        rw [Finset.card_product, Nat.cast_mul, pow_two]
      _ ≤ (2 * B + 3) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hbound 2
      _ = _ := by dsimp only [B]; ring
  · intro g hg u v hshort
    obtain ⟨hu, hv⟩ := int_coordinates_le_of_lattice_lengthSq g hA hR hg u v hshort
    have hu' : |u| ≤ M := by exact_mod_cast hu.trans (Int.le_ceil B)
    have hv' : |v| ≤ M := by exact_mod_cast hv.trans (Int.le_ceil B)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp hu'), Finset.mem_Icc.mpr (abs_le.mp hv')⟩

end Erdos1148.DukeArithmetic
