/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open MeasureTheory
open scoped Topology unitInterval

namespace Erdos745

noncomputable def criticalEdgeProbability (n : ℕ) : unitInterval :=
  if hn : n = 0 then 0 else
    ⟨(1 : ℝ) / n, unitInterval.div_mem (by positivity) (Nat.cast_nonneg n)
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn))⟩

noncomputable def criticalRandomGraph (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (criticalEdgeProbability n)

noncomputable def componentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Multiset ℕ := by
  classical
  exact (Finset.univ : Finset G.ConnectedComponent).val.map fun C ↦ C.supp.ncard

noncomputable def rankedComponentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : List ℕ :=
  (componentOrders G).sort (· ≥ ·)

noncomputable def secondLargestComponentOrder {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  (rankedComponentOrders G).getD 1 0

noncomputable def criticalProbability (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (criticalRandomGraph n).real {G | P G}

noncomputable def edgeProbability (lam : ℝ) (n : ℕ) : unitInterval :=
  ⟨max 0 (min 1 (lam / n)), le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩

noncomputable def randomGraph (lam : ℝ) (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (edgeProbability lam n)

noncomputable def probability (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (randomGraph lam n).real {G | P G}

theorem erdos_745_supercritical (lam : ℝ) (hlam : 1 < lam) (A : ℝ)
    (hA : 1 / (lam - 1 - Real.log lam) < A) :
    Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1) := by
  sorry

theorem erdos_745 :
    ∀ ε : ℝ, 0 < ε → ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        1 - ε ≤ criticalProbability n (fun G ↦
          c * (n : ℝ) ^ (2 / 3 : ℝ) ≤ (secondLargestComponentOrder G : ℝ) ∧
          (secondLargestComponentOrder G : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) := by
  sorry

theorem erdos745_noncritical_asymptotic (lam : ℝ) (hlam : 0 < lam) (hne : lam ≠ 1) :
    ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      |(secondLargestComponentOrder G : ℝ) / Real.log (n : ℝ) -
        1 / (lam - 1 - Real.log lam)| < ε)) Filter.atTop (𝓝 1) := by
  sorry

theorem erdos745_noncritical (lam : ℝ) (hlam : 0 < lam) (hne : lam ≠ 1) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      c * Real.log (n : ℝ) ≤ (secondLargestComponentOrder G : ℝ) ∧
        (secondLargestComponentOrder G : ℝ) ≤ C * Real.log (n : ℝ))) Filter.atTop (𝓝 1) := by
  sorry

end Erdos745
