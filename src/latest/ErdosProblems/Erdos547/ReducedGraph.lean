import ErdosProblems.Erdos547.EquitableRegularPartition
import ErdosProblems.Erdos547.WeightedHost

/-!
# The density-weighted reduced graph
-/

noncomputable section

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (ε d : ℝ)

def reducedDensity (X Y : Finset V) : ℝ :=
  if X ≠ Y ∧ G.IsUniform ε X Y ∧ d ≤ (G.edgeDensity X Y : ℝ)
    then (G.edgeDensity X Y : ℝ) else 0

theorem reducedDensity_nonneg (X Y : Finset V) : 0 ≤ reducedDensity G ε d X Y := by
  unfold reducedDensity
  split_ifs
  · exact_mod_cast G.edgeDensity_nonneg X Y
  · exact le_rfl

theorem reducedDensity_le_one (X Y : Finset V) : reducedDensity G ε d X Y ≤ 1 := by
  unfold reducedDensity
  split_ifs
  · exact_mod_cast G.edgeDensity_le_one X Y
  · norm_num

theorem density_le_reducedDensity (hd : 0 ≤ d) (X Y : Finset V) :
    (G.edgeDensity X Y : ℝ) ≤ reducedDensity G ε d X Y + d +
      (if X = Y then 1 else 0) + (if X ≠ Y ∧ ¬ G.IsUniform ε X Y then 1 else 0) := by
  classical
  have hlow := reducedDensity_nonneg G ε d X Y
  have hone : (G.edgeDensity X Y : ℝ) ≤ 1 := by exact_mod_cast G.edgeDensity_le_one X Y
  by_cases heq : X = Y
  · subst Y
    simp only [reducedDensity, ne_eq, not_true_eq_false, false_and, if_false,
      if_true, add_zero, zero_add]
    linarith
  by_cases hr : G.IsUniform ε X Y
  · by_cases hden : d ≤ (G.edgeDensity X Y : ℝ)
    · simpa [reducedDensity, heq, hr, hden] using
        (le_add_of_nonneg_right hd : (G.edgeDensity X Y : ℝ) ≤ _)
    · have hh : (G.edgeDensity X Y : ℝ) < d := lt_of_not_ge hden
      simp only [if_neg heq, hr, not_true_eq_false, and_false, if_false, add_zero]
      linarith
  · simp only [if_neg heq, if_pos (And.intro heq hr), add_zero]
    linarith

namespace EquitableRegularPartition

variable {G ε} (P : EquitableRegularPartition G ε)

def reducedGraph (d : ℝ) : SimpleGraph ↥P.clusters where
  Adj X Y := X.val ≠ Y.val ∧ G.IsUniform ε X.val Y.val ∧
    d ≤ (G.edgeDensity X.val Y.val : ℝ)
  symm := by
    constructor
    intro X Y h
    exact ⟨Ne.symm h.1, h.2.1.symm, by rw [G.edgeDensity_comm]; exact h.2.2⟩
  loopless := by
    constructor
    intro X h
    exact h.1 rfl

def reducedWeights (d : ℝ) : DPRS.EdgeWeights (P.reducedGraph d) where
  weight X Y := reducedDensity G ε d X.val Y.val
  nonnegative X Y := reducedDensity_nonneg G ε d X.val Y.val
  at_most_one X Y := reducedDensity_le_one G ε d X.val Y.val
  supported X Y h := by
    change ¬ (X.val ≠ Y.val ∧ G.IsUniform ε X.val Y.val ∧
      d ≤ (G.edgeDensity X.val Y.val : ℝ)) at h
    simp only [reducedDensity, if_neg h]

theorem sum_density_le_reduced_degree (hd : 0 ≤ d) (X : ↥P.clusters) :
    (∑ Y : ↥P.clusters, (G.edgeDensity X.val Y.val : ℝ)) ≤
      (P.reducedWeights d).degree X + 1 + (ε + d) * P.clusters.card := by
  classical
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ↥P.clusters))
    (fun Y _ ↦ density_le_reducedDensity G ε d hd X.val Y.val)
  have hdiag : (∑ Y : ↥P.clusters, (if X.val = Y.val then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_coe_sort P.clusters (fun Y ↦ if X.val = Y then (1 : ℝ) else 0)]
    simp [X.property]
  have hbad : (∑ Y : ↥P.clusters,
      (if X.val ≠ Y.val ∧ ¬ G.IsUniform ε X.val Y.val then (1 : ℝ) else 0)) =
      ((P.clusters.filter (fun Y ↦ X.val ≠ Y ∧ ¬ G.IsUniform ε X.val Y)).card : ℝ) := by
    rw [Finset.sum_coe_sort P.clusters
      (fun Y ↦ if X.val ≠ Y ∧ ¬ G.IsUniform ε X.val Y then (1 : ℝ) else 0)]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, apply_ite,
      Nat.cast_one, Nat.cast_zero]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, hdiag, hbad] at hs
  have hb := P.irregular_bound X.val X.property
  change (∑ Y : ↥P.clusters, (G.edgeDensity X.val Y.val : ℝ)) ≤
    (∑ Y : ↥P.clusters, reducedDensity G ε d X.val Y.val) + 1 +
      (ε + d) * P.clusters.card
  nlinarith only [hs, hb]

end EquitableRegularPartition

end Erdos547

#print axioms Erdos547.EquitableRegularPartition.sum_density_le_reduced_degree
