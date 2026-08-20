import ErdosProblems.Erdos746.Sprinkling
import ErdosProblems.Erdos746.AdaptiveCounting
import ErdosProblems.Erdos746.FiniteConditioning
import ErdosProblems.Erdos746.ThresholdAssembly
import ErdosProblems.Erdos746.Connectivity

/-!
# From conditioned sprinkling to the exact threshold layer

This file completes the finite random-ordering argument.  It identifies an
ordered continuation after a fixed prefix with the adaptive sampling tree,
uses the deterministic booster-hit bound for every non-Hamiltonian terminal
graph, and averages the conditional estimates over all base prefixes.
-/

namespace Erdos746

noncomputable section

/-! ## Identifying continuations with fresh adaptive histories -/

/-- An edge unused by a prefix is exactly an edge remaining in the adaptive
alphabet before any continuation edge has been exposed. -/
def unusedEdgeEquivRemaining {n m : ℕ} (p : EdgePrefix n m) :
    UnusedEdge p ≃
      remaining (sprinklingAmbient (edgePrefixSet p)) ([] : List (Edge n)) where
  toFun e := ⟨e.1, by
    rw [mem_remaining_iff]
    exact ⟨by simp [sprinklingAmbient, e.2], by simp⟩⟩
  invFun e := ⟨e.1, by
    have he := (mem_remaining_iff.mp e.2).1
    simpa [sprinklingAmbient] using he⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

/-- Reinterpret an ordered continuation as a fresh continuation in the
adaptive alphabet. -/
def edgeContinuationEquivFresh {n m R : ℕ} (p : EdgePrefix n m) :
    EdgeContinuation p R ≃
      FreshContinuation (sprinklingAmbient (edgePrefixSet p)) [] R :=
  Equiv.embeddingCongr (Equiv.refl (Fin R)) (unusedEdgeEquivRemaining p)

@[simp]
theorem freshContinuationHistory_edgeContinuationEquivFresh
    {n m R : ℕ} (p : EdgePrefix n m) (c : EdgeContinuation p R) :
    freshContinuationHistory (edgeContinuationEquivFresh p c) =
      continuationHistory c := by
  unfold freshContinuationHistory continuationHistory
  apply List.ofFn_congr
  rfl

/-- The graph-process hit counter is the generic adaptive hit counter with
the graph-process booster predicate. -/
theorem graphProcessHitCountFrom_eq_boosterHitCountFrom {n : ℕ}
    (base : Finset (Edge n)) (hist tail : List (Edge n)) :
    graphProcessHitCountFrom base hist tail =
      boosterHitCountFrom (graphProcessBoosters base) hist tail := by
  induction tail generalizing hist with
  | nil => rfl
  | cons e tail ih =>
      simp only [graphProcessHitCountFrom_cons, boosterHitCountFrom_cons]
      rw [ih]

/-! ## Conditional failure estimate -/

/-- For a connected quarter-two-expanding base prefix, the fraction of
ordered continuations whose terminal graph is non-Hamiltonian is bounded by
the adaptive sprinkling error. -/
theorem edgeContinuation_nonHamiltonian_probability_le
    {n m R : ℕ} (hn : 8 ≤ n) (p : EdgePrefix n m)
    (hexpander :
      (graphOfEdges (edgePrefixSet p)).IsTwoExpanderUpTo (n / 4))
    (hR : R ≤ edgeCount n - m) :
    uniformProbability (fun c : EdgeContinuation p R ↦
      ¬(graphAfterHistory (edgePrefixSet p) (continuationHistory c)).IsHamiltonian) ≤
      Real.exp (((n - 1 : ℕ) : ℝ) -
        (1 / 16 : ℝ) * (R : ℝ) * (1 - Real.exp (-1))) := by
  let ambient := sprinklingAmbient (edgePrefixSet p)
  let boosters := graphProcessBoosters (edgePrefixSet p)
  have hconnected : (graphOfEdges (edgePrefixSet p)).Connected :=
    SimpleGraph.IsTwoExpanderUpTo.connected_fin_quarter hn _ hexpander
  have hh : SamplingHorizon ambient [] R := by
    constructor
    · simp [AdmissibleHistory]
    · simpa [ambient] using hR
  rw [uniformProbability_equiv (edgeContinuationEquivFresh p)]
  calc
    uniformProbability (fun c : FreshContinuation ambient [] R ↦
        ¬(graphAfterHistory (edgePrefixSet p)
          (continuationHistory ((edgeContinuationEquivFresh p).symm c))).IsHamiltonian) ≤
        uniformProbability (fun c : FreshContinuation ambient [] R ↦
          boosterLowerTailEvent boosters [] (n - 1)
            (freshContinuationHistory c)) := by
      apply uniformProbability_mono
      intro c hbad
      have hhist :
          continuationHistory ((edgeContinuationEquivFresh p).symm c) =
            freshContinuationHistory c := by
        have h := freshContinuationHistory_edgeContinuationEquivFresh p
          ((edgeContinuationEquivFresh p).symm c)
        simpa using h.symm
      unfold boosterLowerTailEvent
      rw [← graphProcessHitCountFrom_eq_boosterHitCountFrom]
      apply graphProcessHitCountFrom_le_pred
      simpa [hhist] using hbad
    _ = uniformBoosterLowerTailMass ambient boosters [] R (n - 1) := by
      exact uniformProbability_boosterLowerTailEvent_eq_uniformBoosterLowerTailMass
        ambient boosters hh
    _ ≤ Real.exp (((n - 1 : ℕ) : ℝ) -
          (1 / 16 : ℝ) * (R : ℝ) * (1 - Real.exp (-1))) := by
      exact graphProcessLowerTailMass_one_sixteenth hn (edgePrefixSet p)
        hconnected hexpander (by simpa [ambient] using hR)

/-! ## Averaging over the base prefix -/

/-- The exact finite sprinkling comparison used by the asymptotic assembly. -/
theorem thresholdFailureProbability_le_base_add_adaptiveSprinklingError
    {ε ρ : ℝ} {n : ℕ}
    (hn : 8 ≤ n)
    (hbaseTarget : baseEdgeThreshold ρ n ≤ edgeThreshold ε n)
    (htarget : edgeThreshold ε n ≤ edgeCount n) :
    thresholdFailureProbability ε n ≤
      baseBadProbability ρ n + adaptiveSprinklingError ε ρ n := by
  let m := baseEdgeThreshold ρ n
  let R := sprinklingLength ε ρ n
  have hmR : m + R = edgeThreshold ε n := by
    simp only [m, R, sprinklingLength]
    exact Nat.add_sub_of_le hbaseTarget
  have hm : m ≤ edgeCount n := hbaseTarget.trans htarget
  have hR : R ≤ edgeCount n - m := by omega
  have hC : 0 < (edgeCount n - m).descFactorial R :=
    Nat.descFactorial_pos.mpr hR
  letI : Nonempty (EdgePrefix n m) := by
    rw [← Fintype.card_pos_iff]
    rw [Fintype.card_embedding_eq, card_edge]
    simpa using (Nat.descFactorial_pos.mpr hm)
  have hsigma := uniformProbability_sigma_le_bad_base_add
    ((edgeCount n - m).descFactorial R) hC
    (fun p : EdgePrefix n m ↦ by simpa using card_edgeContinuation p)
    (fun p : EdgePrefix n m ↦
      (graphOfEdges (edgePrefixSet p)).IsTwoExpanderUpTo (n / 4))
    (fun z : Σ p : EdgePrefix n m, EdgeContinuation p R ↦
      ¬(graphAfterHistory (edgePrefixSet z.1)
        (continuationHistory z.2)).IsHamiltonian)
    (adaptiveSprinklingError ε ρ n)
    (Real.exp_nonneg _)
    (fun p hp ↦ by
      simpa [adaptiveSprinklingError, R] using
        edgeContinuation_nonHamiltonian_probability_le hn p hp hR)
  have hsigma' :
      uniformProbability (fun q : EdgePrefix n (m + R) ↦
        ¬(graphOfEdges (edgePrefixSet q)).IsHamiltonian) ≤
      uniformProbability (fun p : EdgePrefix n m ↦
        ¬(graphOfEdges (edgePrefixSet p)).IsTwoExpanderUpTo (n / 4)) +
        adaptiveSprinklingError ε ρ n := by
    rw [uniformProbability_equiv (splitEdgePrefixEquiv n m R)]
    have hevent :
        (fun z : Σ p : EdgePrefix n m, EdgeContinuation p R ↦
          ¬(graphOfEdges (edgePrefixSet
            ((splitEdgePrefixEquiv n m R).symm z))).IsHamiltonian) =
        (fun z : Σ p : EdgePrefix n m, EdgeContinuation p R ↦
          ¬(graphAfterHistory (edgePrefixSet z.1)
            (continuationHistory z.2)).IsHamiltonian) := by
      funext z
      rcases z with ⟨p, c⟩
      rw [graph_splitEdgePrefixEquiv_symm]
    rw [hevent]
    exact hsigma
  have htargetFailure :
      thresholdFailureProbability ε n =
        uniformProbability (fun q : EdgePrefix n (m + R) ↦
          ¬(graphOfEdges (edgePrefixSet q)).IsHamiltonian) := by
    rw [thresholdFailureProbability_eq_graphPropertyFailure htarget]
    rw [← hmR]
    unfold graphPropertyFailure graphPropertyProbability
    rw [← uniformProbability_edgePrefix_comp]
    rfl
  have hbaseFailure :
      baseBadProbability ρ n =
        uniformProbability (fun p : EdgePrefix n m ↦
          ¬(graphOfEdges (edgePrefixSet p)).IsTwoExpanderUpTo (n / 4)) := by
    unfold baseBadProbability IsQuarterTwoExpander graphPropertyFailure
      graphPropertyProbability
    change uniformProbability (fun G : FixedEdgeGraph n m ↦
        ¬(FixedEdgeGraph.graph G).IsTwoExpanderUpTo (n / 4)) = _
    rw [← uniformProbability_edgePrefix_comp]
    rfl
  rw [htargetFailure, hbaseFailure]
  exact hsigma'

/-- Eventual threshold comparison in the exact form consumed by
`ThresholdAssembly`. -/
theorem eventually_thresholdFailure_le_base_add_sprinklingError_exact
    {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ ≤ ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      thresholdFailureProbability ε n ≤
        baseBadProbability ρ n + thresholdSprinklingError ρ n := by
  apply eventually_thresholdFailure_le_base_add_sprinklingError hρ hρε
  intro n hn hbaseTarget htarget
  exact thresholdFailureProbability_le_base_add_adaptiveSprinklingError
    hn hbaseTarget htarget

end

end Erdos746
