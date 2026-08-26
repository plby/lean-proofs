import ErdosProblems.Erdos547.RegularPartitionAssembly
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

/-!
# Equitable regularity with a bound on every cluster's exceptional partners
-/

namespace Erdos547

open SimpleGraph

universe u

theorem eventually_equitable_regular_partition (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (l : ℕ) (hl : 1 ≤ l) : ∃ M n₀ : ℕ,
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → ∃ P : EquitableRegularPartition G ε,
        l ≤ P.clusters.card ∧ P.clusters.card ≤ M := by
  classical
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by dsimp [δ]; linarith only [hεone]
  have hδε : 2 * δ ≤ ε := by dsimp [δ]; linarith only [hε]
  have hslice : 2 * δ ^ 2 ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left hεone hε.le
    dsimp [δ]
    nlinarith only [hh, hε.le]
  let M := SzemerediRegularity.bound (δ ^ 2) (2 * l)
  let n₀ := max (2 * l) (Nat.ceil ((M : ℝ) / δ))
  refine ⟨M, n₀, ?_⟩
  intro V instV instEq G instAdj hn
  have hlV : 2 * l ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hceil : Nat.ceil ((M : ℝ) / δ) ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hdiv : (M : ℝ) / δ ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hM : (M : ℝ) ≤ δ * Fintype.card V := by
    have hh := (div_le_iff₀ hδ).mp hdiv
    nlinarith only [hh]
  obtain ⟨P, hequip, hlow, hhigh, hreg⟩ := szemeredi_regularity G (sq_pos_of_pos hδ) hlV
  have ht : 1 ≤ P.parts.card := by omega
  have hsmall : (P.parts.card : ℝ) ≤ δ * Fintype.card V :=
    (show (P.parts.card : ℝ) ≤ M by exact_mod_cast hhigh).trans hM
  obtain ⟨Q, hQlow, hQhigh⟩ := regular_partition_of_uniform G δ ε hδ hδhalf hδε hslice hεone
    P hequip hreg ht hsmall
  exact ⟨Q, by omega, hQlow.trans hhigh⟩

end Erdos547

#print axioms Erdos547.eventually_equitable_regular_partition
