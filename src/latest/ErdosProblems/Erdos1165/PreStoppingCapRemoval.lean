import ErdosProblems.Erdos1165.PreStoppingFiber

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.PreStoppingFiber

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber

/-!
# Removing the insertion-coordinate cap

For a predicate on genuine natural-valued insertion coordinates, the capped
stopped fibres form an increasing sequence.  Their union is exactly the full
countable fixed-external stopped fibre, and continuity from below gives
convergence of the corresponding `fairSteps` probabilities.  This is purely
measure-theoretic and makes no favorite-event identification assumption.
-/

/-- Genuine insertion vectors satisfying coherent fibre data and accepted by
the stopping clock. -/
abbrev AcceptedCoordinates (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) (P : (Fin (i + 1) → ℕ) → Prop) :=
  {q : Fin (i + 1) → ℕ // P q ∧ StoppingAccepted τ r q tail}

/-- The full countable stopped fibre over one retained word and tail. -/
def unboundedPreStoppingFiberEvent (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) (P : (Fin (i + 1) → ℕ) → Prop) : Set StepPath :=
  ⋃ q : AcceptedCoordinates τ r tail P, stoppedInsertionAtom τ r q.1 tail

/-- The coherent finite-coordinate truncation of the preceding event. -/
def coherentCappedFiberEvent (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (cap : ℕ)
    (tail : List Direction) (P : (Fin (i + 1) → ℕ) → Prop) : Set StepPath :=
  preStoppingFiberEvent τ r cap tail (fun q ↦ P (fun k ↦ (q k : ℕ)))

theorem monotone_coherentCappedFiberEvent (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) (P : (Fin (i + 1) → ℕ) → Prop) :
    Monotone fun cap ↦ coherentCappedFiberEvent τ r cap tail P := by
  intro cap cap' hcap ω hω
  unfold coherentCappedFiberEvent preStoppingFiberEvent at hω ⊢
  rcases Set.mem_iUnion.mp hω with ⟨q, hqω⟩
  let q' : CappedCoordinates i cap' := fun k ↦
    ⟨q.1 k, (q.1 k).isLt.trans_le (Nat.succ_le_succ hcap)⟩
  have hnat : (fun k ↦ (q' k : ℕ)) = fun k ↦ (q.1 k : ℕ) := by rfl
  have hP : P (fun k ↦ (q' k : ℕ)) := by
    rw [hnat]
    exact q.2.1
  have hacc : StoppingAccepted τ r (fun k ↦ (q' k : ℕ)) tail := by
    rw [hnat]
    exact q.2.2
  apply Set.mem_iUnion.mpr
  refine ⟨⟨q', hP, hacc⟩, ?_⟩
  rw [hnat]
  exact hqω

/-- Every genuine finite insertion vector occurs in some finite cap. -/
theorem iUnion_coherentCappedFiberEvent (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) (P : (Fin (i + 1) → ℕ) → Prop) :
    (⋃ cap, coherentCappedFiberEvent τ r cap tail P) =
      unboundedPreStoppingFiberEvent τ r tail P := by
  classical
  ext ω
  unfold coherentCappedFiberEvent preStoppingFiberEvent
    unboundedPreStoppingFiberEvent
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨cap, q, hqω⟩
    let qu : AcceptedCoordinates τ r tail P :=
      ⟨(fun k ↦ (q.1 k : ℕ)), q.2.1, q.2.2⟩
    exact ⟨qu, hqω⟩
  · rintro ⟨q, hqω⟩
    let cap : ℕ := ∑ k, q.1 k
    have hbound : ∀ k, q.1 k < cap + 1 := by
      intro k
      apply Nat.lt_succ_of_le
      exact Finset.single_le_sum (s := Finset.univ)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    let qc : CappedCoordinates i cap := fun k ↦ ⟨q.1 k, hbound k⟩
    have hnat : (fun k ↦ (qc k : ℕ)) = q.1 := by rfl
    refine ⟨cap, ⟨⟨qc, ?_, ?_⟩, ?_⟩⟩
    · change P (fun k ↦ (qc k : ℕ))
      rw [hnat]
      exact q.2.1
    · rw [hnat]
      exact q.2.2
    · change ω ∈ stoppedInsertionAtom τ r (fun k ↦ (qc k : ℕ)) tail
      rw [hnat]
      exact hqω

theorem measurableSet_unboundedPreStoppingFiberEvent {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (tail : List Direction)
    (P : (Fin (i + 1) → ℕ) → Prop) :
    MeasurableSet (unboundedPreStoppingFiberEvent τ r tail P) := by
  classical
  exact MeasurableSet.iUnion fun q ↦ by
    rw [stoppedInsertionAtom_eq_cylinder hτ r q.1 tail q.2.2]
    exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const

/-- Probability convergence from finite coordinate caps to the full
countable stopped fibre. -/
theorem tendsto_fairSteps_coherentCappedFiberEvent (τ : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) (P : (Fin (i + 1) → ℕ) → Prop) :
    Tendsto
      (fun cap ↦ fairSteps (coherentCappedFiberEvent τ r cap tail P)) atTop
      (nhds (fairSteps (unboundedPreStoppingFiberEvent τ r tail P))) := by
  have h := tendsto_measure_iUnion_atTop (μ := fairSteps)
    (monotone_coherentCappedFiberEvent τ r tail P)
  rw [iUnion_coherentCappedFiberEvent τ r tail P] at h
  exact h

end Erdos1165.PreStoppingFiber
