import ErdosProblems.Erdos1148.LatticeVectorAction
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval

/-! # Bounded lattice vectors have bounded integral coordinates -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma modularVector_recover (g : SL(2, ℝ)) (u v : ℤ) :
    ((u : ℝ), (v : ℝ)) =
      (g 0 0 * (modularVector g u v).1 + g 0 1 * (modularVector g u v).2,
        g 1 0 * (modularVector g u v).1 + g 1 1 * (modularVector g u v).2) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  apply Prod.ext
  · simp only [modularVector, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination -(u : ℝ) * hdet
  · simp only [modularVector, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination -(v : ℝ) * hdet

theorem int_coordinates_le_of_lattice_lengthSq (g : SL(2, ℝ)) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hg : ∀ i j : Fin 2, |g i j| ≤ A) (u v : ℤ)
    (hshort : modularVectorLengthSq g u v ≤ R) :
    |(u : ℝ)| ≤ 2 * A * (R + 1) ∧ |(v : ℝ)| ≤ 2 * A * (R + 1) := by
  have hx : |(modularVector g u v).1| ≤ R + 1 := by
    dsimp only [modularVectorLengthSq] at hshort
    nlinarith [sq_abs (modularVector g u v).1, sq_nonneg (modularVector g u v).2,
      sq_nonneg (|(modularVector g u v).1| - 1)]
  have hy : |(modularVector g u v).2| ≤ R + 1 := by
    dsimp only [modularVectorLengthSq] at hshort
    nlinarith [sq_abs (modularVector g u v).2, sq_nonneg (modularVector g u v).1,
      sq_nonneg (|(modularVector g u v).2| - 1)]
  have hbound (i : Fin 2) : |g i 0 * (modularVector g u v).1 +
      g i 1 * (modularVector g u v).2| ≤ 2 * A * (R + 1) := by
    calc
      _ ≤ |g i 0| * |(modularVector g u v).1| +
          |g i 1| * |(modularVector g u v).2| := by
        simpa only [abs_mul] using abs_add_le
          (g i 0 * (modularVector g u v).1) (g i 1 * (modularVector g u v).2)
      _ ≤ A * (R + 1) + A * (R + 1) := add_le_add
        (mul_le_mul (hg i 0) hx (abs_nonneg _) hA)
        (mul_le_mul (hg i 1) hy (abs_nonneg _) hA)
      _ = _ := by ring
  have hrec := modularVector_recover g u v
  have hu := congrArg Prod.fst hrec
  have hv := congrArg Prod.snd hrec
  dsimp only at hu hv
  rw [hu, hv]
  exact ⟨hbound 0, hbound 1⟩

theorem finite_lattice_vectors_of_entry_bound {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    Set.Finite {p : ℤ × ℤ | ∃ g : SL(2, ℝ), (∀ i j : Fin 2, |g i j| ≤ A) ∧
      modularVectorLengthSq g p.1 p.2 ≤ R} := by
  let B : ℝ := 2 * A * (R + 1)
  apply ((Set.finite_Icc (-⌈B⌉) ⌈B⌉).prod (Set.finite_Icc (-⌈B⌉) ⌈B⌉)).subset
  rintro ⟨u, v⟩ ⟨g, hg, hshort⟩
  obtain ⟨hu, hv⟩ := int_coordinates_le_of_lattice_lengthSq g hA hR hg u v hshort
  have hu' : |u| ≤ ⌈B⌉ := by exact_mod_cast hu.trans (Int.le_ceil B)
  have hv' : |v| ≤ ⌈B⌉ := by exact_mod_cast hv.trans (Int.le_ceil B)
  exact ⟨abs_le.mp hu', abs_le.mp hv'⟩

end Erdos1148.DukeArithmetic
