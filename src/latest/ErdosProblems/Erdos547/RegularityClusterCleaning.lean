import ErdosProblems.Erdos547.RegularityRowCleaning

/-!
# Cleaning an ordinary regularity partition
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {A : Finset V} (P : Finpartition A)

open scoped Classical in
theorem sum_nonUniform_rows (ε : ℝ) :
    (∑ X ∈ P.parts, (P.parts.filter (fun Y ↦ X ≠ Y ∧ ¬ G.IsUniform ε X Y)).card) =
      (P.nonUniforms G ε).card := by
  classical
  have he : ((P.parts ×ˢ P.parts).filter (fun p ↦ p.1 ≠ p.2 ∧ ¬ G.IsUniform ε p.1 p.2)) =
      P.nonUniforms G ε := by
    ext p
    simp only [Finpartition.nonUniforms, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
    tauto
  rw [← he]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

open scoped Classical in
theorem exists_cluster_clean_subfamily (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hP : P.IsUniform G (δ ^ 2)) :
    ∃ J ⊆ P.parts, ((P.parts \ J).card : ℝ) ≤ δ * P.parts.card ∧
      (P.parts.card : ℝ) ≤ 2 * J.card ∧
      ∀ X ∈ J, ((J.filter (fun Y ↦ X ≠ Y ∧ ¬ G.IsUniform (δ ^ 2) X Y)).card : ℝ) ≤
        2 * δ * J.card := by
  classical
  apply exists_row_clean_subfamily P.parts (fun X Y ↦ X ≠ Y ∧ ¬ G.IsUniform (δ ^ 2) X Y)
    δ hδ hδhalf
  have hcard : P.parts.card * (P.parts.card - 1) ≤ P.parts.card ^ 2 := by
    have hh := Nat.mul_le_mul_left P.parts.card (Nat.sub_le P.parts.card 1)
    nlinarith only [hh]
  have hcard' : ((P.parts.card * (P.parts.card - 1) : ℕ) : ℝ) ≤ (P.parts.card : ℝ) ^ 2 := by
    exact_mod_cast hcard
  calc
    _ = ((P.nonUniforms G (δ ^ 2)).card : ℝ) := by exact_mod_cast sum_nonUniform_rows G P (δ ^ 2)
    _ ≤ ((P.parts.card * (P.parts.card - 1) : ℕ) : ℝ) * δ ^ 2 := hP
    _ ≤ δ ^ 2 * (P.parts.card : ℝ) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hcard' (sq_nonneg δ)
      nlinarith only [hh]

end Erdos547

#print axioms Erdos547.exists_cluster_clean_subfamily
