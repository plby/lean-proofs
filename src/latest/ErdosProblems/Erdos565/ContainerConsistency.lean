/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos565.ContainerA

/-!
# Fingerprint consistency for the container algorithm

The Campos--Samotij container map is obtained from a deterministic selector.
The selector chooses the next layer and seed from the current hypergraph; the
input independent set decides only whether that seed is accepted.  This file
formalizes the standard first-differing-answer argument: two executions with
the same final fingerprint have identical answer histories and identical
final states.  Consequently their final container is a function of the
fingerprint alone.

No weight estimate occurs here.  The only quantitative input needed later is
the separate fact that every final fingerprint is contained in its input.
-/

namespace Erdos565
namespace ContainerA

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The observable result of a deterministic selector execution.  Recording
the branch list makes the usual "same fingerprint implies same transcript"
claim literal. -/
structure Execution (V : Type*) [DecidableEq V] where
  finalState : State V
  branches : List Branch

namespace Selector

/-- Execute a canonical selector for at most `fuel` rounds and record all
branches taken before termination. -/
def execute {s : ℕ} (selector : Selector (V := V) s) (I : Finset V) :
    ℕ → State V → Execution V
  | 0, state => ⟨state, []⟩
  | fuel + 1, state =>
      letI : Decidable (selector.terminal state.family) :=
        selector.decision state.family
      if hterminal : selector.terminal state.family then
        ⟨state, []⟩
      else
        let choice := selector.choose state.family hterminal
        let branch := branchFor I choice.seed
        let tail := execute selector I fuel
          (state.next choice.layerIndex choice.seed branch)
        ⟨tail.finalState, branch :: tail.branches⟩

@[simp] theorem execute_zero {s : ℕ} (selector : Selector (V := V) s)
    (I : Finset V) (state : State V) :
    execute selector I 0 state = ⟨state, []⟩ := rfl

@[simp] theorem execute_succ_of_terminal {s : ℕ}
    (selector : Selector (V := V) s) (I : Finset V) {fuel : ℕ}
    {state : State V} (hterminal : selector.terminal state.family) :
    execute selector I (fuel + 1) state = ⟨state, []⟩ := by
  simp [execute, hterminal]

theorem execute_succ_of_not_terminal {s : ℕ}
    (selector : Selector (V := V) s) (I : Finset V) {fuel : ℕ}
    {state : State V} (hterminal : ¬ selector.terminal state.family) :
    execute selector I (fuel + 1) state =
      let choice := selector.choose state.family hterminal
      let branch := branchFor I choice.seed
      let tail := execute selector I fuel
        (state.next choice.layerIndex choice.seed branch)
      ⟨tail.finalState, branch :: tail.branches⟩ := by
  simp [execute, hterminal]

/-- The current fingerprint is contained in the final fingerprint of every
finite execution. -/
theorem fingerprint_subset_execute {s : ℕ}
    (selector : Selector (V := V) s) (I : Finset V) :
    ∀ fuel state,
      state.fingerprint ⊆ (execute selector I fuel state).finalState.fingerprint := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      exact Finset.Subset.rfl
  | succ fuel ih =>
      intro state
      by_cases hterminal : selector.terminal state.family
      · rw [execute_succ_of_terminal selector I hterminal]
      · rw [execute_succ_of_not_terminal selector I hterminal]
        exact (fingerprint_mono_next state _ _ _).trans (ih _)

theorem toOracle_next_eq_direct {s : ℕ}
    (selector : Selector (V := V) s) (I : Finset V) {state : State V}
    (hterminal : ¬ selector.terminal state.family) :
    (selector.toOracle I).next state =
      let choice := selector.choose state.family hterminal
      state.next choice.layerIndex choice.seed (branchFor I choice.seed) := by
  rw [(selector.toOracle I).next_eq_round_of_not_terminal hterminal]
  rfl

/-- The concrete `algorithmStep` presentation in `ContainerA` is exactly the
oracle step induced by its canonical selector.  This lets clients freely use
the quantitative `algorithmStep` lemmas and the deterministic-selector
consistency lemmas on the same execution. -/
theorem algorithmStep_eq_toOracle_next (p : ℝ) (s : ℕ) (hs : 0 < s)
    (hp : 0 < p) (I : Finset V) (state : State V) :
    algorithmStep p s hs hp I state =
      ((algorithmSelector (V := V) p s hs hp).toOracle I).next state := by
  by_cases hterminal : algorithmTerminal p s state.family
  · rw [algorithmStep_eq_self hterminal]
    rw [Oracle.next_eq_of_terminal]
    exact hterminal
  · rw [algorithmStep_eq_next hterminal]
    rw [Oracle.next_eq_round_of_not_terminal]
    rfl

/-- The state component of `execute` is exactly the existing oracle/fuel
execution from `ContainerA`. -/
theorem execute_finalState_eq_run {s : ℕ}
    (selector : Selector (V := V) s) (I : Finset V) :
    ∀ fuel state,
      (execute selector I fuel state).finalState =
        @ContainerFuel.run (State V) (selector.toOracle I).terminal
          (selector.toOracle I).decision (selector.toOracle I).next fuel state := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      rfl
  | succ fuel ih =>
      intro state
      by_cases hterminal : selector.terminal state.family
      · rw [execute_succ_of_terminal selector I hterminal]
        rw [ContainerFuel.run_succ_of_terminal]
        exact hterminal
      · rw [execute_succ_of_not_terminal selector I hterminal]
        rw [ContainerFuel.run_succ_of_not_terminal]
        · rw [toOracle_next_eq_direct selector I hterminal]
          apply ih
        · exact hterminal

/-- Equal final fingerprints force equality of the entire canonical
execution, provided (as guaranteed by the algorithm invariant) each final
fingerprint is contained in the corresponding input.

The proof compares the first branch.  If one input accepts the common seed
and the other rejects it, the seed lies in the first final fingerprint by
monotonicity.  Equality of final fingerprints and containment in the second
input then force the second branch to accept as well, a contradiction. -/
theorem execute_eq_of_final_fingerprint_eq {s : ℕ}
    (selector : Selector (V := V) s) (I J : Finset V) :
    ∀ fuel state,
      let outI := execute selector I fuel state
      let outJ := execute selector J fuel state
      outI.finalState.fingerprint ⊆ I →
      outJ.finalState.fingerprint ⊆ J →
      outI.finalState.fingerprint = outJ.finalState.fingerprint →
      outI = outJ := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      dsimp only
      intro _ _ _
      rfl
  | succ fuel ih =>
      intro state
      dsimp only
      intro hsubI hsubJ hfp
      by_cases hterminal : selector.terminal state.family
      · simp [execute, hterminal]
      · let choice := selector.choose state.family hterminal
        by_cases hseedI : choice.seed ⊆ I
        · by_cases hseedJ : choice.seed ⊆ J
          · rw [execute_succ_of_not_terminal selector I hterminal] at hsubI hfp ⊢
            rw [execute_succ_of_not_terminal selector J hterminal] at hsubJ hfp ⊢
            simp only [choice, branchFor, hseedI, hseedJ, ↓reduceIte]
              at hsubI hsubJ hfp ⊢
            exact congrArg
              (fun tail : Execution V =>
                Execution.mk tail.finalState (Branch.accept :: tail.branches))
              (ih _ hsubI hsubJ hfp)
          · exfalso
            rw [execute_succ_of_not_terminal selector I hterminal] at hsubI hfp
            rw [execute_succ_of_not_terminal selector J hterminal] at hsubJ hfp
            simp only [choice, branchFor, hseedI, hseedJ, ↓reduceIte] at hsubI hsubJ hfp
            apply hseedJ
            intro v hv
            apply hsubJ
            rw [← hfp]
            apply fingerprint_subset_execute selector I fuel
            simp only [State.next]
            exact Finset.mem_union_right _ hv
        · by_cases hseedJ : choice.seed ⊆ J
          · exfalso
            rw [execute_succ_of_not_terminal selector I hterminal] at hsubI hfp
            rw [execute_succ_of_not_terminal selector J hterminal] at hsubJ hfp
            simp only [choice, branchFor, hseedI, hseedJ, ↓reduceIte] at hsubI hsubJ hfp
            apply hseedI
            intro v hv
            apply hsubI
            rw [hfp]
            apply fingerprint_subset_execute selector J fuel
            simp only [State.next]
            exact Finset.mem_union_right _ hv
          · rw [execute_succ_of_not_terminal selector I hterminal] at hsubI hfp ⊢
            rw [execute_succ_of_not_terminal selector J hterminal] at hsubJ hfp ⊢
            simp only [choice, branchFor, hseedI, hseedJ, ↓reduceIte]
              at hsubI hsubJ hfp ⊢
            exact congrArg
              (fun tail : Execution V =>
                Execution.mk tail.finalState (Branch.reject :: tail.branches))
              (ih _ hsubI hsubJ hfp)

/-- State-level form of fingerprint consistency, phrased with the established
`ContainerFuel.run`/`Oracle.next` API. -/
theorem run_eq_of_final_fingerprint_eq {s : ℕ}
    (selector : Selector (V := V) s) (I J : Finset V) (fuel : ℕ)
    (state : State V)
    (hsubI :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint ⊆ I)
    (hsubJ :
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint ⊆ J)
    (hfp :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint =
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint) :
    @ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state =
      @ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state := by
  rw [← execute_finalState_eq_run selector I fuel state] at hsubI
  rw [← execute_finalState_eq_run selector J fuel state] at hsubJ
  rw [← execute_finalState_eq_run selector I fuel state,
    ← execute_finalState_eq_run selector J fuel state] at hfp ⊢
  exact congrArg Execution.finalState
    (execute_eq_of_final_fingerprint_eq selector I J fuel state hsubI hsubJ hfp)

/-- Transcript-level form of the same result.  This exposes equality of the
branch histories while accepting hypotheses stated for the established
oracle runs. -/
theorem execute_eq_of_run_final_fingerprint_eq {s : ℕ}
    (selector : Selector (V := V) s) (I J : Finset V) (fuel : ℕ)
    (state : State V)
    (hsubI :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint ⊆ I)
    (hsubJ :
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint ⊆ J)
    (hfp :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint =
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint) :
    execute selector I fuel state = execute selector J fuel state := by
  rw [← execute_finalState_eq_run selector I fuel state] at hsubI
  rw [← execute_finalState_eq_run selector J fuel state] at hsubJ
  rw [← execute_finalState_eq_run selector I fuel state,
    ← execute_finalState_eq_run selector J fuel state] at hfp
  exact execute_eq_of_final_fingerprint_eq selector I J fuel state hsubI hsubJ hfp

/-- The form normally used by the container construction: invariant
preservation supplies the two fingerprint-containment hypotheses. -/
theorem run_eq_of_final_fingerprint_eq_of_invariant {s : ℕ}
    (selector : Selector (V := V) s) {H₀ : Family V} (I J : Finset V)
    (fuel : ℕ) (state : State V)
    (hinvI : Invariant H₀ I s state) (hinvJ : Invariant H₀ J s state)
    (hfp :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint =
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint) :
    @ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state =
      @ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state := by
  exact run_eq_of_final_fingerprint_eq selector I J fuel state
    ((selector.toOracle I).invariant_run hinvI fuel).fingerprint_subset
    ((selector.toOracle J).invariant_run hinvJ fuel).fingerprint_subset hfp

/-- Under the same invariant hypotheses, the complete branch transcript is
also a function of the final fingerprint. -/
theorem execute_eq_of_final_fingerprint_eq_of_invariant {s : ℕ}
    (selector : Selector (V := V) s) {H₀ : Family V} (I J : Finset V)
    (fuel : ℕ) (state : State V)
    (hinvI : Invariant H₀ I s state) (hinvJ : Invariant H₀ J s state)
    (hfp :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint =
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint) :
    execute selector I fuel state = execute selector J fuel state := by
  exact execute_eq_of_run_final_fingerprint_eq selector I J fuel state
    ((selector.toOracle I).invariant_run hinvI fuel).fingerprint_subset
    ((selector.toOracle J).invariant_run hinvJ fuel).fingerprint_subset hfp

/-- Therefore the final hypergraph depends only on the final fingerprint. -/
theorem run_family_eq_of_final_fingerprint_eq {s : ℕ}
    (selector : Selector (V := V) s) (I J : Finset V) (fuel : ℕ)
    (state : State V)
    (hsubI :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint ⊆ I)
    (hsubJ :
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint ⊆ J)
    (hfp :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint =
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint) :
    (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).family =
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).family := by
  exact congrArg State.family
    (run_eq_of_final_fingerprint_eq selector I J fuel state hsubI hsubJ hfp)

/-- In particular, the returned vertex container depends only on the final
fingerprint. -/
theorem run_container_eq_of_final_fingerprint_eq {s : ℕ}
    (selector : Selector (V := V) s) (I J : Finset V) (fuel : ℕ)
    (state : State V)
    (hsubI :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint ⊆ I)
    (hsubJ :
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint ⊆ J)
    (hfp :
      (@ContainerFuel.run (State V) (selector.toOracle I).terminal
        (selector.toOracle I).decision (selector.toOracle I).next fuel state).fingerprint =
      (@ContainerFuel.run (State V) (selector.toOracle J).terminal
        (selector.toOracle J).decision (selector.toOracle J).next fuel state).fingerprint) :
    containerVertices
        (@ContainerFuel.run (State V) (selector.toOracle I).terminal
          (selector.toOracle I).decision (selector.toOracle I).next fuel state).family =
      containerVertices
        (@ContainerFuel.run (State V) (selector.toOracle J).terminal
          (selector.toOracle J).decision (selector.toOracle J).next fuel state).family := by
  exact congrArg containerVertices
    (run_family_eq_of_final_fingerprint_eq selector I J fuel state hsubI hsubJ hfp)

/-! ## The fingerprint-indexed output map -/

/-- The uniform fuel used by the finite container execution. -/
def fullFuel (V : Type*) [Fintype V] : ℕ := 2 ^ Fintype.card V + 1

/-- The final state produced from an initial hypergraph and an input set. -/
def finalState {s : ℕ} (selector : Selector (V := V) s)
    (H : Family V) (I : Finset V) : State V :=
  @ContainerFuel.run (State V) (selector.toOracle I).terminal
    (selector.toOracle I).decision (selector.toOracle I).next
    (fullFuel V) (initialState H)

/-- The fingerprint returned by the full execution. -/
def fingerprint {s : ℕ} (selector : Selector (V := V) s)
    (H : Family V) (I : Finset V) : Finset V :=
  (selector.finalState H I).fingerprint

/-- The vertex container returned by the full execution. -/
def container {s : ℕ} (selector : Selector (V := V) s)
    (H : Family V) (I : Finset V) : Finset V :=
  containerVertices (selector.finalState H I).family

theorem finalState_invariant {s : ℕ} (selector : Selector (V := V) s)
    {H : Family V} {I : Finset V} (hs : 0 < s) (huniform : IsUniform H s)
    (hI : Independent H I) : Invariant H I s (selector.finalState H I) := by
  exact (selector.toOracle I).invariant_run
    (initial_invariant hs huniform hI) (fullFuel V)

theorem fingerprint_subset_input {s : ℕ} (selector : Selector (V := V) s)
    {H : Family V} {I : Finset V} (hs : 0 < s) (huniform : IsUniform H s)
    (hI : Independent H I) : selector.fingerprint H I ⊆ I :=
  (selector.finalState_invariant hs huniform hI).fingerprint_subset

/-- Full-fuel specialization: two independent inputs with the same returned
fingerprint have exactly the same final state. -/
theorem finalState_eq_of_fingerprint_eq {s : ℕ}
    (selector : Selector (V := V) s) (H : Family V) (I J : Finset V)
    (hs : 0 < s) (huniform : IsUniform H s)
    (hI : Independent H I) (hJ : Independent H J)
    (hfp : selector.fingerprint H I = selector.fingerprint H J) :
    selector.finalState H I = selector.finalState H J := by
  apply run_eq_of_final_fingerprint_eq_of_invariant selector I J
    (fullFuel V) (initialState H)
  · exact initial_invariant hs huniform hI
  · exact initial_invariant hs huniform hJ
  · exact hfp

/-- Thus the concrete returned vertex container depends only on the returned
fingerprint. -/
theorem container_eq_of_fingerprint_eq {s : ℕ}
    (selector : Selector (V := V) s) (H : Family V) (I J : Finset V)
    (hs : 0 < s) (huniform : IsUniform H s)
    (hI : Independent H I) (hJ : Independent H J)
    (hfp : selector.fingerprint H I = selector.fingerprint H J) :
    selector.container H I = selector.container H J := by
  exact congrArg (fun state : State V => containerVertices state.family)
    (selector.finalState_eq_of_fingerprint_eq H I J hs huniform hI hJ hfp)

/-- Choose an input realizing `S` as a fingerprint when one exists.  The
fallback is irrelevant on the range of `fingerprint`. -/
noncomputable def representative {s : ℕ} (selector : Selector (V := V) s)
    (H : Family V) (S : Finset V) : Finset V :=
  letI : Decidable
      (∃ I : Finset V, Independent H I ∧ selector.fingerprint H I = S) :=
    Classical.propDecidable _
  if h : ∃ I : Finset V, Independent H I ∧ selector.fingerprint H I = S then
    Classical.choose h
  else ∅

theorem representative_spec {s : ℕ} (selector : Selector (V := V) s)
    (H : Family V) (S : Finset V)
    (h : ∃ I : Finset V, Independent H I ∧ selector.fingerprint H I = S) :
    Independent H (selector.representative H S) ∧
      selector.fingerprint H (selector.representative H S) = S := by
  rw [representative, dif_pos h]
  exact Classical.choose_spec h

/-- The paper's map `ψ`: assign a vertex container to every possible
fingerprint by running on a canonical representative. -/
noncomputable def containerMap {s : ℕ} (selector : Selector (V := V) s)
    (H : Family V) (S : Finset V) : Finset V :=
  selector.container H (selector.representative H S)

/-- On every independent input, `containerMap` evaluated at the returned
fingerprint is exactly the container of that input.  This is the well-defined
output-map statement needed by the Campos--Samotij theorem. -/
theorem containerMap_fingerprint {s : ℕ}
    (selector : Selector (V := V) s) (H : Family V) (I : Finset V)
    (hs : 0 < s) (huniform : IsUniform H s) (hI : Independent H I) :
    selector.containerMap H (selector.fingerprint H I) = selector.container H I := by
  have hex : ∃ J : Finset V,
      Independent H J ∧ selector.fingerprint H J = selector.fingerprint H I :=
    ⟨I, hI, rfl⟩
  have hrep := selector.representative_spec H (selector.fingerprint H I) hex
  exact selector.container_eq_of_fingerprint_eq H
    (selector.representative H (selector.fingerprint H I)) I hs huniform hrep.1 hI hrep.2

/-! ## Concrete Campos--Samotij selector -/

/-- Projecting the quantitative execution to its underlying state gives the
same execution as iterating the oracle induced by the canonical selector. -/
theorem quantRun_state_eq_selector_run
    {H : Family V} {I : Finset V} {p : ℝ} {s : ℕ}
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (x : QuantState H I p s) : ∀ fuel,
    (@ContainerFuel.run (QuantState H I p s) quantTerminal
      quantTerminalDecision (quantNext hs hp hpmax) fuel x).1 =
      @ContainerFuel.run (State V)
        ((algorithmSelector (V := V) p s hs hp).toOracle I).terminal
        ((algorithmSelector (V := V) p s hs hp).toOracle I).decision
        ((algorithmSelector (V := V) p s hs hp).toOracle I).next fuel x.1 := by
  intro fuel
  exact quantRun_val_eq_algorithmRunAux (V := V) hs hp hpmax fuel x

/-- The underlying state of `finalQuantState`, used to construct
`finiteContainer`, is the full-fuel selector state used above. -/
theorem finalQuantState_state_eq_selector_finalState
    (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (hI : Independent H I) :
    (finalQuantState H I p s hs hp hpmax huniform hI).1 =
      (algorithmSelector (V := V) p s hs hp).finalState H I := by
  calc
    (finalQuantState H I p s hs hp hpmax huniform hI).1 =
        algorithmRun H I p s hs hp :=
      finalQuantState_val_eq_algorithmRun H I p s hs hp hpmax huniform hI
    _ = (algorithmSelector (V := V) p s hs hp).finalState H I := by
      rfl

/-- The fingerprint field exposed by `finiteContainer` is exactly the
canonical selector fingerprint. -/
theorem finiteContainer_fingerprint_eq_selector_fingerprint
    (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (hI : Independent H I) :
    (finiteContainer H s p hs hp hpmax huniform I hI).fingerprint =
      (algorithmSelector (V := V) p s hs hp).fingerprint H I := by
  change (finalQuantState H I p s hs hp hpmax huniform hI).1.fingerprint =
    ((algorithmSelector (V := V) p s hs hp).finalState H I).fingerprint
  exact congrArg State.fingerprint
    (finalQuantState_state_eq_selector_finalState
      H I p s hs hp hpmax huniform hI)

/-- The container field exposed by `finiteContainer` is exactly the selector
container. -/
theorem finiteContainer_container_eq_selector_container
    (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (hI : Independent H I) :
    (finiteContainer H s p hs hp hpmax huniform I hI).container =
      (algorithmSelector (V := V) p s hs hp).container H I := by
  change containerVertices
      (finalQuantState H I p s hs hp hpmax huniform hI).1.family =
    containerVertices
      ((algorithmSelector (V := V) p s hs hp).finalState H I).family
  exact congrArg (fun state : State V => containerVertices state.family)
    (finalQuantState_state_eq_selector_finalState
      H I p s hs hp hpmax huniform hI)

/-- The cover field exposed by `finiteContainer` is the `aboveOne` family of
the selector's final state. -/
theorem finiteContainer_cover_eq_selector_aboveOne
    (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (hI : Independent H I) :
    (finiteContainer H s p hs hp hpmax huniform I hI).cover =
      aboveOne ((algorithmSelector (V := V) p s hs hp).finalState H I).family := by
  change aboveOne (finalQuantState H I p s hs hp hpmax huniform hI).1.family =
    aboveOne ((algorithmSelector (V := V) p s hs hp).finalState H I).family
  exact congrArg (fun state : State V => aboveOne state.family)
    (finalQuantState_state_eq_selector_finalState
      H I p s hs hp hpmax huniform hI)

/-- For the canonical weighted selector, equal full-fuel fingerprints force
equal final states. -/
theorem algorithmSelector_finalState_eq_of_fingerprint_eq
    (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p)
    (H : Family V) (I J : Finset V) (huniform : IsUniform H s)
    (hI : Independent H I) (hJ : Independent H J)
    (hfp :
      (algorithmSelector (V := V) p s hs hp).fingerprint H I =
        (algorithmSelector (V := V) p s hs hp).fingerprint H J) :
    (algorithmSelector (V := V) p s hs hp).finalState H I =
      (algorithmSelector (V := V) p s hs hp).finalState H J := by
  exact (algorithmSelector (V := V) p s hs hp).finalState_eq_of_fingerprint_eq
    H I J hs huniform hI hJ hfp

/-- Concrete output consistency: the returned vertex container is determined
by the final fingerprint. -/
theorem algorithmSelector_container_eq_of_fingerprint_eq
    (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p)
    (H : Family V) (I J : Finset V) (huniform : IsUniform H s)
    (hI : Independent H I) (hJ : Independent H J)
    (hfp :
      (algorithmSelector (V := V) p s hs hp).fingerprint H I =
        (algorithmSelector (V := V) p s hs hp).fingerprint H J) :
    (algorithmSelector (V := V) p s hs hp).container H I =
      (algorithmSelector (V := V) p s hs hp).container H J := by
  exact (algorithmSelector (V := V) p s hs hp).container_eq_of_fingerprint_eq
    H I J hs huniform hI hJ hfp

/-- The residual hypergraph above the singleton layer is likewise determined
by the final fingerprint.  In particular, its cover data can be indexed by
that fingerprint. -/
theorem algorithmSelector_aboveOne_eq_of_fingerprint_eq
    (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p)
    (H : Family V) (I J : Finset V) (huniform : IsUniform H s)
    (hI : Independent H I) (hJ : Independent H J)
    (hfp :
      (algorithmSelector (V := V) p s hs hp).fingerprint H I =
        (algorithmSelector (V := V) p s hs hp).fingerprint H J) :
    aboveOne ((algorithmSelector (V := V) p s hs hp).finalState H I).family =
      aboveOne ((algorithmSelector (V := V) p s hs hp).finalState H J).family := by
  exact congrArg (fun state : State V => aboveOne state.family)
    (algorithmSelector_finalState_eq_of_fingerprint_eq
      p s hs hp H I J huniform hI hJ hfp)

/-- The representative-based output map specializes directly to the
canonical weighted selector used in the Campos--Samotij algorithm. -/
theorem algorithmSelector_containerMap_fingerprint
    (p : ℝ) (s : ℕ) (hs : 0 < s) (hp : 0 < p)
    (H : Family V) (I : Finset V) (huniform : IsUniform H s)
    (hI : Independent H I) :
    (algorithmSelector (V := V) p s hs hp).containerMap H
        ((algorithmSelector (V := V) p s hs hp).fingerprint H I) =
      (algorithmSelector (V := V) p s hs hp).container H I := by
  exact (algorithmSelector (V := V) p s hs hp).containerMap_fingerprint
    H I hs huniform hI

/-- Record-level consistency for the finite container theorem: equal exposed
fingerprints force equal exposed vertex containers. -/
theorem finiteContainer_container_eq_of_fingerprint_eq
    (H : Family V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (I J : Finset V)
    (hI : Independent H I) (hJ : Independent H J)
    (hfp :
      (finiteContainer H s p hs hp hpmax huniform I hI).fingerprint =
        (finiteContainer H s p hs hp hpmax huniform J hJ).fingerprint) :
    (finiteContainer H s p hs hp hpmax huniform I hI).container =
      (finiteContainer H s p hs hp hpmax huniform J hJ).container := by
  let selector := algorithmSelector (V := V) p s hs hp
  have hfp' : selector.fingerprint H I = selector.fingerprint H J := by
    calc
      selector.fingerprint H I =
          (finiteContainer H s p hs hp hpmax huniform I hI).fingerprint :=
        (finiteContainer_fingerprint_eq_selector_fingerprint
          H I p s hs hp hpmax huniform hI).symm
      _ = (finiteContainer H s p hs hp hpmax huniform J hJ).fingerprint := hfp
      _ = selector.fingerprint H J :=
        finiteContainer_fingerprint_eq_selector_fingerprint
          H J p s hs hp hpmax huniform hJ
  calc
    (finiteContainer H s p hs hp hpmax huniform I hI).container =
        selector.container H I :=
      finiteContainer_container_eq_selector_container
        H I p s hs hp hpmax huniform hI
    _ = selector.container H J :=
      algorithmSelector_container_eq_of_fingerprint_eq
        p s hs hp H I J huniform hI hJ hfp'
    _ = (finiteContainer H s p hs hp hpmax huniform J hJ).container :=
      (finiteContainer_container_eq_selector_container
        H J p s hs hp hpmax huniform hJ).symm

/-- Equal exposed fingerprints also force equality of the residual cover
families returned by `finiteContainer`. -/
theorem finiteContainer_cover_eq_of_fingerprint_eq
    (H : Family V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (I J : Finset V)
    (hI : Independent H I) (hJ : Independent H J)
    (hfp :
      (finiteContainer H s p hs hp hpmax huniform I hI).fingerprint =
        (finiteContainer H s p hs hp hpmax huniform J hJ).fingerprint) :
    (finiteContainer H s p hs hp hpmax huniform I hI).cover =
      (finiteContainer H s p hs hp hpmax huniform J hJ).cover := by
  let selector := algorithmSelector (V := V) p s hs hp
  have hfp' : selector.fingerprint H I = selector.fingerprint H J := by
    calc
      selector.fingerprint H I =
          (finiteContainer H s p hs hp hpmax huniform I hI).fingerprint :=
        (finiteContainer_fingerprint_eq_selector_fingerprint
          H I p s hs hp hpmax huniform hI).symm
      _ = (finiteContainer H s p hs hp hpmax huniform J hJ).fingerprint := hfp
      _ = selector.fingerprint H J :=
        finiteContainer_fingerprint_eq_selector_fingerprint
          H J p s hs hp hpmax huniform hJ
  calc
    (finiteContainer H s p hs hp hpmax huniform I hI).cover =
        aboveOne (selector.finalState H I).family :=
      finiteContainer_cover_eq_selector_aboveOne
        H I p s hs hp hpmax huniform hI
    _ = aboveOne (selector.finalState H J).family :=
      algorithmSelector_aboveOne_eq_of_fingerprint_eq
        p s hs hp H I J huniform hI hJ hfp'
    _ = (finiteContainer H s p hs hp hpmax huniform J hJ).cover :=
      (finiteContainer_cover_eq_selector_aboveOne
        H J p s hs hp hpmax huniform hJ).symm

/-- Direct `finiteContainer` form of the paper's `ψ ∘ φ` identity.  The
representative-based map evaluated at the record's exposed fingerprint is its
exposed vertex container. -/
theorem algorithmSelector_containerMap_finiteContainer_fingerprint
    (H : Family V) (I : Finset V) (p : ℝ) (s : ℕ)
    (hs : 0 < s) (hp : 0 < p) (hpmax : p ≤ 1 / (8 * (s : ℝ) ^ 2))
    (huniform : IsUniform H s) (hI : Independent H I) :
    (algorithmSelector (V := V) p s hs hp).containerMap H
        (finiteContainer H s p hs hp hpmax huniform I hI).fingerprint =
      (finiteContainer H s p hs hp hpmax huniform I hI).container := by
  let selector := algorithmSelector (V := V) p s hs hp
  calc
    selector.containerMap H
        (finiteContainer H s p hs hp hpmax huniform I hI).fingerprint =
        selector.containerMap H (selector.fingerprint H I) := by
      rw [finiteContainer_fingerprint_eq_selector_fingerprint
        H I p s hs hp hpmax huniform hI]
    _ = selector.container H I :=
      algorithmSelector_containerMap_fingerprint
        p s hs hp H I huniform hI
    _ = (finiteContainer H s p hs hp hpmax huniform I hI).container :=
      (finiteContainer_container_eq_selector_container
        H I p s hs hp hpmax huniform hI).symm

end Selector
end ContainerA
end Erdos565
