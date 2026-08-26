import ErdosProblems.Erdos547.MatchingCompactness

/-!
# Compact optimization of fractional matchings with closed constraints
-/

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def feasibleFractional : Set (V → V → ℝ) := {f |
  (∀ u v, f u v = f v u) ∧ (∀ u v, 0 ≤ f u v) ∧
  (∀ u v, ¬ G.Adj u v → f u v = 0) ∧ ∀ u, ∑ v, f u v ≤ 1}

theorem isClosed_feasibleFractional : IsClosed (feasibleFractional G) := by
  have hs : IsClosed {f : V → V → ℝ | ∀ u v, f u v = f v u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_eq (by fun_prop) (by fun_prop)
  have hz : IsClosed {f : V → V → ℝ | ∀ u v, 0 ≤ f u v} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_le continuous_const (by fun_prop)
  have ha : IsClosed {f : V → V → ℝ | ∀ u v, ¬ G.Adj u v → f u v = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (by fun_prop) continuous_const
  have hc : IsClosed {f : V → V → ℝ | ∀ u, ∑ v, f u v ≤ 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_le (by fun_prop) continuous_const
  exact hs.inter (hz.inter (ha.inter hc))

theorem isCompact_feasibleFractional : IsCompact (feasibleFractional G) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ _ : V ↦ (0 : ℝ))
    (fun _ _ : V ↦ (1 : ℝ)))).of_isClosed_subset (isClosed_feasibleFractional G)
  intro f hf
  let μ : FractionalMatching G := ⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
  exact ⟨hf.2.1, μ.weight_le_one⟩

theorem exists_maximizing_fractional_with_constraints (P : Set (V → V → ℝ))
    (hP : IsClosed P) (hne : ∃ μ : FractionalMatching G, μ.weight ∈ P)
    (objective : (V → V → ℝ) → ℝ) (hc : Continuous objective) :
    ∃ μ : FractionalMatching G, μ.weight ∈ P ∧
      ∀ ν : FractionalMatching G, ν.weight ∈ P → objective ν.weight ≤ objective μ.weight := by
  have hcomp : IsCompact (feasibleFractional G ∩ P) :=
    (isCompact_feasibleFractional G).inter_right hP
  obtain ⟨μ₀, hμ₀⟩ := hne
  have hnonempty : (feasibleFractional G ∩ P).Nonempty :=
    ⟨μ₀.weight, ⟨μ₀.symmetric, μ₀.nonnegative, μ₀.supported, μ₀.capacity⟩, hμ₀⟩
  obtain ⟨f, hf, hmax⟩ := hcomp.exists_isMaxOn hnonempty hc.continuousOn
  let μ : FractionalMatching G := ⟨f, hf.1.1, hf.1.2.1, hf.1.2.2.1, hf.1.2.2.2⟩
  exact ⟨μ, hf.2, fun ν hν ↦ hmax ⟨⟨ν.symmetric, ν.nonnegative, ν.supported, ν.capacity⟩, hν⟩⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_maximizing_fractional_with_constraints
