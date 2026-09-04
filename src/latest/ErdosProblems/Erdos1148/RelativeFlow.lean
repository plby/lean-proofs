import ErdosProblems.Erdos1148.RealFlow
import ErdosProblems.Erdos1148.FlowVolume

/-!
# Close pairs of real diagonal-flow trajectories

Entrywise closeness gives both a short interval of possible integral mixed
coefficients and a uniform area bound for each fixed relative matrix.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma diagonalFlow_relative_matrix (g : SL(2, ℝ)) (t s : ℝ) :
    ((diagonalFlow (-t) * g * diagonalFlow s : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![g 0 0 * Real.exp ((s - t) / 2), g 0 1 * Real.exp (-((s + t) / 2));
         g 1 0 * Real.exp ((s + t) / 2), g 1 1 * Real.exp ((t - s) / 2)] := by
  change (diagonalFlow (-t)).1 * g.1 * (diagonalFlow s).1 = _
  have hexp (a b c : ℝ) : Real.exp a * b * Real.exp c = b * Real.exp (a + c) := by
    rw [Real.exp_add]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, diagonalFlow,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul,
      add_zero, zero_add] <;>
    rw [hexp] <;>
    congr 2 <;> ring

def EntryCloseOne (η : ℝ) (g : SL(2, ℝ)) : Prop :=
  |g 0 0 - 1| ≤ η ∧ |g 0 1| ≤ η ∧ |g 1 0| ≤ η ∧ |g 1 1 - 1| ≤ η

def closeDiagonalFlowTimes (g : SL(2, ℝ)) (η : ℝ) : Set (Fin 2 → ℝ) :=
  {x | EntryCloseOne η (diagonalFlow (-(x 0)) * g * diagonalFlow (x 1))}

lemma closeDiagonalFlowTimes_subset (g : SL(2, ℝ)) (η : ℝ) :
    closeDiagonalFlowTimes g η ⊆ closeFlowTimes (g 0 0) (g 0 1) (g 1 0) η := by
  intro x hx
  have hmat := diagonalFlow_relative_matrix g (x 0) (x 1)
  change |((diagonalFlow (-(x 0)) * g * diagonalFlow (x 1) : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 1| ≤ η ∧ _ at hx
  change CloseFlowCoordinates (g 0 0) (g 0 1) (g 1 0) η
    ((x 1 - x 0) / 2) ((x 1 + x 0) / 2)
  rw [hmat] at hx
  exact ⟨hx.1, hx.2.1, hx.2.2.1⟩

lemma entryCloseOne_offDiagonal_product {η : ℝ} {g : SL(2, ℝ)}
    (h : EntryCloseOne η g) : |g 0 1 * g 1 0| ≤ η ^ 2 := by
  have hη : 0 ≤ η := (abs_nonneg _).trans h.2.1
  rw [abs_mul, pow_two]
  exact mul_le_mul h.2.1 h.2.2.1 (abs_nonneg _) hη

lemma entryCloseOne_pairing_bound {d ℓ : ℤ} (hd : 0 < d) {η : ℝ}
    {g : SL(2, ℝ)} (hg : EntryCloseOne η g)
    (hpair : (ℓ : ℝ) = (d : ℝ) * (2 + 4 * g 0 1 * g 1 0)) :
    |(ℓ : ℝ) - 2 * (d : ℝ)| ≤ 4 * (d : ℝ) * η ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heq : (ℓ : ℝ) - 2 * (d : ℝ) = (4 * (d : ℝ)) * (g 0 1 * g 1 0) := by
    linear_combination hpair
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 4 * (d : ℝ))]
  exact mul_le_mul_of_nonneg_left (entryCloseOne_offDiagonal_product hg) (by positivity)

theorem volume_closeDiagonalFlowTimes_le {d ℓ : ℤ} (hd : 0 < d) (hℓ : ℓ ≠ 2 * d)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2) (g : SL(2, ℝ))
    (hpair : (ℓ : ℝ) = (d : ℝ) * (2 + 4 * g 0 1 * g 1 0)) :
    volume (closeDiagonalFlowTimes g η) ≤
      ENNReal.ofReal (8 * η * Real.log (4 * (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact (measure_mono (closeDiagonalFlowTimes_subset g η)).trans
    (volume_closeFlowTimes_le hdR hη0 hη
      (offDiagonal_product_lower_bound hd hℓ _ _ hpair))

end Erdos1148.DukeArithmetic
