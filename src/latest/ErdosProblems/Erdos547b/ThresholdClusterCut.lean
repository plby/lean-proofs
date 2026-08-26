/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Section6Dichotomy

/-! # Lift a thresholded crossing count, retaining the low-density pairs -/

open scoped SimpleGraph BigOperators Classical
noncomputable section
namespace Erdos547b.ZhaoThresholdClusterCut

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoSection6Dichotomy

theorem card_interedges_le_density_bound
    {V : Type*} [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (A B : Finset V) (τ : ℝ) (hden : (H.edgeDensity A B : ℝ) ≤ τ) :
    ((H.interedges A B).card : ℝ) ≤ τ * A.card * B.card := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · have hprod : (0 : ℝ) < (A.card : ℝ) * B.card := by
        exact mul_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast hB.card_pos)
      rw [H.edgeDensity_def] at hden
      push_cast at hden
      have h := (div_le_iff₀ hprod).mp hden
      simpa only [mul_assoc] using h
    · have hB0 := Finset.not_nonempty_iff_eq_empty.mp hB
      subst B
      simp [SimpleGraph.interedges_def]
  · have hA0 := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [SimpleGraph.interedges_def]

theorem thresholded_clusterUnion_crossing_le
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (P : ClusterAssignment V I) (H : SimpleGraph V) (R : SimpleGraph I)
    [DecidableRel H.Adj] [DecidableRel R.Adj]
    (A B : Finset I) (N : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hcluster : ∀ i, (clusterVertices P i).card ≤ N)
    (hlow : ∀ i j, ¬R.Adj i j →
      (H.edgeDensity (clusterVertices P i) (clusterVertices P j) : ℝ) ≤ τ) :
    ((H.interedges (clusterUnion P A) (clusterUnion P B)).card : ℝ) ≤
      ((R.interedges A B).card + τ * A.card * B.card) * (N : ℝ) ^ 2 := by
  let block : I × I → Finset (V × V) := fun ij =>
    H.interedges (clusterVertices P ij.1) (clusterVertices P ij.2)
  have hunion : H.interedges (clusterUnion P A) (clusterUnion P B) =
      (A ×ˢ B).biUnion block := by
    exact H.interedges_biUnion A B (clusterVertices P) (clusterVertices P)
  have hblock (ij : I × I) : ((block ij).card : ℝ) ≤
      (if R.Adj ij.1 ij.2 then (N : ℝ) ^ 2 else 0) + τ * (N : ℝ) ^ 2 := by
    have hc : ((clusterVertices P ij.1).card : ℝ) * (clusterVertices P ij.2).card ≤ (N : ℝ) ^ 2 := by
      have hn := Nat.mul_le_mul (hcluster ij.1) (hcluster ij.2)
      simpa only [pow_two, Nat.cast_mul] using (show
        (((clusterVertices P ij.1).card * (clusterVertices P ij.2).card : ℕ) : ℝ) ≤
          ((N * N : ℕ) : ℝ) from by exact_mod_cast hn)
    by_cases h : R.Adj ij.1 ij.2
    · rw [if_pos h]
      have hb : ((block ij).card : ℝ) ≤ (N : ℝ) ^ 2 := by
        have he : ((block ij).card : ℝ) ≤
            ((clusterVertices P ij.1).card : ℝ) * (clusterVertices P ij.2).card := by
          exact_mod_cast H.card_interedges_le_mul (clusterVertices P ij.1) (clusterVertices P ij.2)
        exact he.trans hc
      exact hb.trans (le_add_of_nonneg_right (mul_nonneg hτ (sq_nonneg _)))
    · rw [if_neg h, zero_add]
      have hb := card_interedges_le_density_bound H (clusterVertices P ij.1)
        (clusterVertices P ij.2) τ (hlow ij.1 ij.2 h)
      exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc hτ)
  have hsum : (∑ ij ∈ A ×ˢ B, if R.Adj ij.1 ij.2 then (N : ℝ) ^ 2 else 0) =
      (R.interedges A B).card * (N : ℝ) ^ 2 := by
    rw [← Finset.sum_filter]
    simp only [← R.interedges_def, Finset.sum_const, nsmul_eq_mul]
  calc
    ((H.interedges (clusterUnion P A) (clusterUnion P B)).card : ℝ) =
        (((A ×ˢ B).biUnion block).card : ℝ) := by rw [hunion]
    _ ≤ ∑ ij ∈ A ×ˢ B, ((block ij).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : ((A ×ˢ B).biUnion block).card ≤ ∑ ij ∈ A ×ˢ B, (block ij).card)
    _ ≤ ∑ ij ∈ A ×ˢ B, ((if R.Adj ij.1 ij.2 then (N : ℝ) ^ 2 else 0) + τ * (N : ℝ) ^ 2) :=
      Finset.sum_le_sum (fun ij _ => hblock ij)
    _ = ((R.interedges A B).card + τ * A.card * B.card) * (N : ℝ) ^ 2 := by
      rw [Finset.sum_add_distrib, hsum]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.cast_mul]
      ring

end Erdos547b.ZhaoThresholdClusterCut

#print axioms Erdos547b.ZhaoThresholdClusterCut.card_interedges_le_density_bound
#print axioms Erdos547b.ZhaoThresholdClusterCut.thresholded_clusterUnion_crossing_le
