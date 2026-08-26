import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Erdős Problem 745: exact model and component statistics

The problem page asks about `G(n, 1 / n)`.  That is the centre of the critical
window, not the supercritical model `G(n, λ / n)`, `λ > 1`, treated by
Komlós--Sulyok--Szemerédi.  At the literal parameter the second-largest
component has order `n ^ (2 / 3)` in probability (Aldous's critical random
graph theorem), so the logarithmic assertion printed on the problem page is
false.

This file uses Mathlib's exact binomial random-graph measure and fixes the
component statistic and asymptotic statements needed for the literal problem.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology unitInterval

namespace Erdos745

/-- The exact edge probability `1 / n`, with the irrelevant empty graph case
set to probability zero. -/
noncomputable def criticalEdgeProbability (n : ℕ) : unitInterval :=
  if hn : n = 0 then 0 else
    ⟨(1 : ℝ) / n, unitInterval.div_mem (by positivity) (Nat.cast_nonneg n)
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn))⟩

@[simp] theorem criticalEdgeProbability_zero : criticalEdgeProbability 0 = 0 := by
  simp [criticalEdgeProbability]

@[simp] theorem coe_criticalEdgeProbability {n : ℕ} (hn : n ≠ 0) :
    (criticalEdgeProbability n : ℝ) = 1 / n := by
  simp [criticalEdgeProbability, hn]

/-- The law of the literal random graph in Problem 745. -/
noncomputable def criticalRandomGraph (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (criticalEdgeProbability n)

instance (n : ℕ) : IsProbabilityMeasure (criticalRandomGraph n) := by
  unfold criticalRandomGraph
  infer_instance

/-- Exact mass of a labelled graph in the critical model. -/
theorem criticalRandomGraph_real_singleton {n : ℕ} (hn : n ≠ 0)
    (G : SimpleGraph (Fin n)) :
    (criticalRandomGraph n).real {G} =
      (1 / (n : ℝ)) ^ G.edgeSet.ncard *
        (1 - 1 / (n : ℝ)) ^ (n.choose 2 - G.edgeSet.ncard) := by
  rw [MeasureTheory.measureReal_def, criticalRandomGraph,
    SimpleGraph.binomialRandom_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_pow]
  simp [coe_criticalEdgeProbability hn]

/-- The multiset of orders of the connected components of a finite graph. -/
noncomputable def componentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Multiset ℕ := by
  classical
  exact (Finset.univ : Finset G.ConnectedComponent).val.map fun C ↦ C.supp.ncard

/-- Component orders sorted in decreasing order. -/
noncomputable def rankedComponentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : List ℕ :=
  (componentOrders G).sort (· ≥ ·)

/-- The order of the largest component, with value zero for the empty graph. -/
noncomputable def largestComponentOrder {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  (rankedComponentOrders G).getD 0 0

/-- The order of the second-largest component, with value zero if fewer than
two components exist.  Ties are retained because the list contains one entry
per connected component. -/
noncomputable def secondLargestComponentOrder {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  (rankedComponentOrders G).getD 1 0

/-- The exact probability of a graph event in the critical model. -/
noncomputable def criticalProbability (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (criticalRandomGraph n).real {G | P G}

@[simp] theorem criticalProbability_true (n : ℕ) :
    criticalProbability n (fun _ ↦ True) = 1 := by
  simp [criticalProbability, MeasureTheory.measureReal_def]

@[simp] theorem criticalProbability_false (n : ℕ) :
    criticalProbability n (fun _ ↦ False) = 0 := by
  simp [criticalProbability]

theorem criticalProbability_nonneg (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) :
    0 ≤ criticalProbability n P := by
  exact measureReal_nonneg

theorem criticalProbability_le_one (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) :
    criticalProbability n P ≤ 1 := by
  exact measureReal_le_one

theorem criticalProbability_mono {n : ℕ}
    {P Q : SimpleGraph (Fin n) → Prop} (h : ∀ G, P G → Q G) :
    criticalProbability n P ≤ criticalProbability n Q := by
  apply measureReal_mono (h₂ := by finiteness)
  intro G hG
  exact h G hG

/-- Every event is measurable because the labelled graph sample space is
finite and `edgeSet` is a measurable embedding. -/
theorem measurableSet_graphEvent {n : ℕ} (s : Set (SimpleGraph (Fin n))) :
    MeasurableSet s := by
  rw [← SimpleGraph.measurableEmbedding_edgeSet.measurableSet_image]
  exact (Set.toFinite (SimpleGraph.edgeSet '' s)).measurableSet

/-- The two-event Bonferroni lower bound in the exact critical model. -/
theorem criticalProbability_inter_ge (n : ℕ)
    (P Q : SimpleGraph (Fin n) → Prop) :
    criticalProbability n P + criticalProbability n Q - 1 ≤
      criticalProbability n (fun G ↦ P G ∧ Q G) := by
  let s : Set (SimpleGraph (Fin n)) := {G | P G}
  let t : Set (SimpleGraph (Fin n)) := {G | Q G}
  have ht : MeasurableSet t := measurableSet_graphEvent t
  have hadd := measureReal_union_add_inter (μ := criticalRandomGraph n)
    (s := s) (t := t) ht
  have hle : (criticalRandomGraph n).real (s ∪ t) ≤ 1 := measureReal_le_one
  change (criticalRandomGraph n).real s + (criticalRandomGraph n).real t - 1 ≤
    (criticalRandomGraph n).real (s ∩ t)
  linarith

/-- A family of events holds with high probability in `G(n, 1 / n)`. -/
def WithHighProbability
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n ↦ criticalProbability n (P n)) atTop (𝓝 1)

/-- `Xₙ = Θ_P(aₙ)`: for every error tolerance there are fixed positive lower
and upper constants trapping `Xₙ / aₙ` with asymptotic probability at least
`1 - ε`. -/
def IsThetaInProbability (X : (n : ℕ) → SimpleGraph (Fin n) → ℝ)
    (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ criticalProbability n (fun G ↦ c * a n ≤ X n G ∧ X n G ≤ C * a n)

/-- The deterministic critical scale. -/
noncomputable def criticalScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (2 / 3 : ℝ)

/-- Real-valued second-largest component order. -/
noncomputable def secondOrder (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  secondLargestComponentOrder G

/-- Lower tightness away from zero at the critical scale. -/
def CriticalLowerTightness : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ criticalProbability n (fun G ↦ c * criticalScale n ≤ secondOrder n G)

/-- Upper tightness at the critical scale. -/
def CriticalUpperTightness : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ criticalProbability n (fun G ↦ secondOrder n G ≤ C * criticalScale n)

/-- The two one-sided critical estimates assemble into `Θ_P(n^(2/3))`. -/
theorem criticalSecondLargestScaling_of_tightness
    (hlower : CriticalLowerTightness) (hupper : CriticalUpperTightness) :
    IsThetaInProbability secondOrder criticalScale := by
  intro ε hε
  obtain ⟨c, hc, hcprob⟩ := hlower (ε / 2) (by positivity)
  obtain ⟨C, hC, hCprob⟩ := hupper (ε / 2) (by positivity)
  let c' := min c (C / 2)
  have hc' : 0 < c' := lt_min hc (by positivity)
  have hc'C : c' < C :=
    (min_le_right c (C / 2)).trans_lt (by linarith)
  refine ⟨c', C, hc', hc'C, ?_⟩
  filter_upwards [hcprob, hCprob] with n hnLower hnUpper
  let A : SimpleGraph (Fin n) → Prop :=
    fun G ↦ c' * criticalScale n ≤ secondOrder n G
  let B : SimpleGraph (Fin n) → Prop :=
    fun G ↦ secondOrder n G ≤ C * criticalScale n
  have hscale : 0 ≤ criticalScale n := by
    unfold criticalScale
    positivity
  have hmono :
      criticalProbability n (fun G ↦ c * criticalScale n ≤ secondOrder n G) ≤
        criticalProbability n A := by
    apply criticalProbability_mono
    intro G hG
    exact (mul_le_mul_of_nonneg_right (min_le_left c (C / 2)) hscale).trans hG
  have hA : 1 - ε / 2 ≤ criticalProbability n A := hnLower.trans hmono
  have hAB := criticalProbability_inter_ge n A B
  change 1 - ε ≤ criticalProbability n (fun G ↦ A G ∧ B G)
  have hB : 1 - ε / 2 ≤ criticalProbability n B := hnUpper
  linarith

/-- The literal resolution statement: the second-largest component at
`p = 1 / n` has critical order `n^(2/3)`. -/
def CriticalSecondLargestScaling : Prop :=
  IsThetaInProbability secondOrder criticalScale

/-- The two one-sided estimates are exactly equivalent to the critical
`Θ_P` statement. -/
theorem criticalSecondLargestScaling_iff_tightness :
    CriticalSecondLargestScaling ↔
      CriticalLowerTightness ∧ CriticalUpperTightness := by
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨c, C, hc, _hcC, hprob⟩ := h ε hε
      refine ⟨c, hc, ?_⟩
      filter_upwards [hprob] with n hn
      exact hn.trans (criticalProbability_mono fun G hG ↦ hG.1)
    · intro ε hε
      obtain ⟨c, C, _hc, hcC, hprob⟩ := h ε hε
      refine ⟨C, (lt_trans (by positivity) hcC), ?_⟩
      filter_upwards [hprob] with n hn
      exact hn.trans (criticalProbability_mono fun G hG ↦ hG.2)
  · rintro ⟨hlower, hupper⟩
    exact criticalSecondLargestScaling_of_tightness hlower hupper

end Erdos745
