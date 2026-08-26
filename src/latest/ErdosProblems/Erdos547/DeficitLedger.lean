import ErdosProblems.Erdos547.DeficitSaturation

/-!
# Accounting for deficits on a reachable set and across a deleted cut
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
theorem avoiding_deficit_ledger (R W X U good : Finset V) (s n f loss deficit : V → ℝ)
    (hW : W ⊆ R) (hn : ∀ u, 0 ≤ n u) (hl : ∀ u, 0 ≤ loss u)
    (hcap : ∀ u, s u + n u ≤ 1)
    (hpoint : ∀ u ∈ goodᶜ, deficit u ≤
      (if u ∈ R \ W then 1 - s u - n u else 0) +
      (if u ∈ X then 1 else 0) + (if u ∈ U then loss u else 0))
    (hcut : (∑ u ∈ U, loss u) ≤ ∑ u ∈ W, (n u - f u)) :
    (∑ u ∈ goodᶜ, deficit u) ≤
      (R.card : ℝ) + X.card - (∑ u ∈ R, s u) - ∑ u ∈ W, f u := by
  classical
  let charge (u : V) := (if u ∈ R \ W then 1 - s u - n u else 0) +
    (if u ∈ X then (1 : ℝ) else 0) + (if u ∈ U then loss u else 0)
  have hc (u : V) : 0 ≤ charge u := by
    dsimp [charge]
    apply add_nonneg
    · apply add_nonneg
      · split_ifs <;> linarith [hcap u]
      · split_ifs <;> norm_num
    · split_ifs <;> first | exact hl u | exact le_rfl
  have hsum : (∑ u ∈ goodᶜ, deficit u) ≤
      (∑ u ∈ R \ W, (1 - s u - n u)) + (X.card : ℝ) + ∑ u ∈ U, loss u := by
    calc
      _ ≤ ∑ u ∈ goodᶜ, charge u := Finset.sum_le_sum hpoint
      _ ≤ ∑ u, charge u := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun u _ _ ↦ hc u)
      _ = _ := by simp only [charge, Finset.sum_add_distrib, Finset.sum_ite_mem_eq]; simp
  have hrest : (∑ u ∈ R \ W, (1 - s u - n u)) ≤
      ((R \ W).card : ℝ) - ∑ u ∈ R \ W, s u := by
    calc
      _ ≤ ∑ u ∈ R \ W, (1 - s u) := Finset.sum_le_sum fun u _ ↦ sub_le_self _ (hn u)
      _ = _ := by simp [Finset.sum_sub_distrib]
  have hcovered : (∑ u ∈ W, (n u - f u)) ≤
      (W.card : ℝ) - (∑ u ∈ W, s u) - ∑ u ∈ W, f u := by
    calc
      _ ≤ ∑ u ∈ W, (1 - s u - f u) := Finset.sum_le_sum fun u _ ↦ by
        linarith [hcap u]
      _ = _ := by simp [Finset.sum_sub_distrib]
  have hcR : ((R \ W).card : ℝ) + W.card = R.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hW
  have hsR : (∑ u ∈ R \ W, s u) + (∑ u ∈ W, s u) = ∑ u ∈ R, s u := by
    exact Finset.sum_sdiff hW
  linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.avoiding_deficit_ledger
