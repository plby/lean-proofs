import ErdosProblems.Erdos547.SkewMatching
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Existence of optimal fractional allocations

The feasible arc weights form a nonempty compact set in a finite product of
real intervals. Thus every continuous objective attains a maximum. No
optimization oracle or extra axiom is used.
-/

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (γ : ℝ)

/-- The unbundled feasible set for the skew allocations. -/
def feasibleSkew : Set (V → V → ℝ) := {w |
  (∀ u v, 0 ≤ w u v) ∧
  (∀ u v, ¬ G.Adj u v → w u v = 0) ∧
  ∀ u, (∑ v, w u v) + γ * (∑ v, w v u) ≤ 1 + γ}

theorem isClosed_feasibleSkew : IsClosed (feasibleSkew G γ) := by
  have hnonnegative : IsClosed {w : V → V → ℝ | ∀ u v, 0 ≤ w u v} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const (by fun_prop)
  have hsupported : IsClosed {w : V → V → ℝ | ∀ u v, ¬ G.Adj u v → w u v = 0} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro _
    exact isClosed_eq (by fun_prop) continuous_const
  have hcapacity : IsClosed {w : V → V → ℝ |
      ∀ u, (∑ v, w u v) + γ * (∑ v, w v u) ≤ 1 + γ} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro u
    exact isClosed_le (by fun_prop) continuous_const
  exact hnonnegative.inter (hsupported.inter hcapacity)

theorem isCompact_feasibleSkew (hγ : 0 ≤ γ) : IsCompact (feasibleSkew G γ) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ _ : V ↦ (0 : ℝ))
    (fun _ _ : V ↦ 1 + γ))).of_isClosed_subset (isClosed_feasibleSkew G γ)
  intro w hw
  let σ : SkewMatching G γ := ⟨hγ, w, hw.1, hw.2.1, hw.2.2⟩
  exact ⟨hw.1, fun u v ↦ σ.weight_le_denominator u v⟩

theorem feasibleSkew_nonempty (hγ : 0 ≤ γ) : (feasibleSkew G γ).Nonempty := by
  refine ⟨fun _ _ ↦ 0, ?_⟩
  change (∀ u v : V, (0 : ℝ) ≤ 0) ∧ (∀ u v, ¬ G.Adj u v → (0 : ℝ) = 0) ∧ _
  refine ⟨fun _ _ ↦ le_rfl, fun _ _ _ ↦ rfl, ?_⟩
  intro u
  simp only [Finset.sum_const_zero, mul_zero, add_zero]
  linarith

/-- A continuous objective has a maximizing feasible skew allocation. -/
theorem exists_maximizing_skew (hγ : 0 ≤ γ) (objective : (V → V → ℝ) → ℝ)
    (hobjective : Continuous objective) :
    ∃ σ : SkewMatching G γ, ∀ τ : SkewMatching G γ, objective τ.weight ≤ objective σ.weight := by
  obtain ⟨w, hw, hmax⟩ := (isCompact_feasibleSkew G γ hγ).exists_isMaxOn
    (feasibleSkew_nonempty G γ hγ) hobjective.continuousOn
  let σ : SkewMatching G γ := ⟨hγ, w, hw.1, hw.2.1, hw.2.2⟩
  refine ⟨σ, fun τ ↦ ?_⟩
  exact hmax ⟨τ.nonnegative, τ.supported, τ.capacity⟩

/-- In particular, maximum total weight is attained. -/
theorem exists_maximum_weight_skew (hγ : 0 ≤ γ) :
    ∃ σ : SkewMatching G γ, ∀ τ : SkewMatching G γ, τ.total ≤ σ.total := by
  exact exists_maximizing_skew G γ hγ (fun w ↦ ∑ u, ∑ v, w u v) (by fun_prop)

/-- A second continuous objective can break ties among maximizers of the
first. This is the two-stage optimality used for refined matching choices. -/
theorem exists_maximizing_skew_with_tiebreak (hγ : 0 ≤ γ)
    (first second : (V → V → ℝ) → ℝ) (hfirst : Continuous first) (hsecond : Continuous second) :
    ∃ σ : SkewMatching G γ,
      (∀ τ : SkewMatching G γ, first τ.weight ≤ first σ.weight) ∧
      ∀ τ : SkewMatching G γ, first τ.weight = first σ.weight →
        second τ.weight ≤ second σ.weight := by
  have hcompact := isCompact_feasibleSkew G γ hγ
  obtain ⟨w₀, hw₀, hmax₀⟩ := hcompact.exists_isMaxOn
    (feasibleSkew_nonempty G γ hγ) hfirst.continuousOn
  let optimal := feasibleSkew G γ ∩ {w | first w = first w₀}
  have hclosed : IsClosed optimal :=
    (isClosed_feasibleSkew G γ).inter (isClosed_eq hfirst continuous_const)
  have hcompact' : IsCompact optimal := hcompact.of_isClosed_subset hclosed (fun _ h ↦ h.1)
  have hnonempty : optimal.Nonempty := ⟨w₀, hw₀, rfl⟩
  obtain ⟨w₁, hw₁, hmax₁⟩ := hcompact'.exists_isMaxOn hnonempty hsecond.continuousOn
  let σ : SkewMatching G γ := ⟨hγ, w₁, hw₁.1.1, hw₁.1.2.1, hw₁.1.2.2⟩
  refine ⟨σ, ?_, ?_⟩
  · intro τ
    change first τ.weight ≤ first w₁
    rw [hw₁.2]
    exact hmax₀ ⟨τ.nonnegative, τ.supported, τ.capacity⟩
  · intro τ hτ
    apply hmax₁
    exact ⟨⟨τ.nonnegative, τ.supported, τ.capacity⟩, hτ.trans hw₁.2⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_maximizing_skew
#print axioms Erdos547.DPRS.exists_maximizing_skew_with_tiebreak
