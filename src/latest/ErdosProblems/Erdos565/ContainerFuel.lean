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
module

public import ErdosProblems.Erdos565.Hypergraph

/-!
# Fuel for finite container algorithms

Container algorithms repeatedly replace a hypergraph by one whose generated
up-set is strictly larger.  This file packages the elementary termination
argument independently of the particular choice of the next round.

The main theorem, `terminal_run_upClosure`, applies to an arbitrary state type.
The state need not itself be finite: it is enough to attach a hypergraph on a
fixed finite vertex type to every state.  Since an up-set is a subfamily of the
`2 ^ |V|` subsets of `V`, no execution can make more than that many strict
increases without reaching a terminal state.
-/

@[expose] public section

namespace Erdos565
namespace ContainerFuel

/-- Run `next` until `terminal` becomes true, or until the supplied fuel is
exhausted.  A terminal state is fixed rather than updated. -/
def run {State : Type*} (terminal : State → Prop) [DecidablePred terminal]
    (next : State → State) : ℕ → State → State
  | 0, state => state
  | fuel + 1, state =>
      if terminal state then state else run terminal next fuel (next state)

@[simp] theorem run_zero {State : Type*} (terminal : State → Prop)
    [DecidablePred terminal] (next : State → State) (state : State) :
    run terminal next 0 state = state := rfl

@[simp] theorem run_succ_of_terminal {State : Type*} (terminal : State → Prop)
    [DecidablePred terminal] (next : State → State) {fuel : ℕ} {state : State}
    (hstate : terminal state) :
    run terminal next (fuel + 1) state = state := by
  simp [run, hstate]

@[simp] theorem run_succ_of_not_terminal {State : Type*} (terminal : State → Prop)
    [DecidablePred terminal] (next : State → State) {fuel : ℕ} {state : State}
    (hstate : ¬ terminal state) :
    run terminal next (fuel + 1) state = run terminal next fuel (next state) := by
  simp [run, hstate]

/-- Once a run has reached a terminal state, extra fuel does not change it. -/
theorem run_eq_of_terminal {State : Type*} (terminal : State → Prop)
    [DecidablePred terminal] (next : State → State) {state : State}
    (hstate : terminal state) : ∀ fuel, run terminal next fuel state = state
  | 0 => rfl
  | _ + 1 => run_succ_of_terminal terminal next hstate

/-- If the final state of a run of length `fuel` is still nonterminal, then a
natural-valued rank which strictly increases at every nonterminal step has
increased by at least `fuel`.

This formulation is useful because it neither assumes that the state space is
finite nor records an execution trace. -/
theorem rank_add_fuel_le_of_not_terminal_run {State : Type*}
    (terminal : State → Prop) [DecidablePred terminal] (next : State → State)
    (rank : State → ℕ)
    (rank_strict : ∀ state, ¬ terminal state → rank state < rank (next state)) :
    ∀ {fuel : ℕ} {state : State},
      ¬ terminal (run terminal next fuel state) →
        rank state + fuel ≤ rank (run terminal next fuel state) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state _
      simp
  | succ fuel ih =>
      intro state hfinal
      by_cases hstate : terminal state
      · rw [run_succ_of_terminal terminal next hstate] at hfinal
        exact False.elim (hfinal hstate)
      · rw [run_succ_of_not_terminal terminal next hstate] at hfinal ⊢
        have hstep := rank_strict state hstate
        have htail := ih hfinal
        omega

/-- A strictly increasing bounded natural rank forces `run` to terminate after
`bound + 1` rounds.  The extra one makes the statement independent of the
initial rank (which may be zero). -/
theorem terminal_run_of_strict_bounded_rank {State : Type*}
    (terminal : State → Prop) [DecidablePred terminal] (next : State → State)
    (rank : State → ℕ) (bound : ℕ)
    (rank_le : ∀ state, rank state ≤ bound)
    (rank_strict : ∀ state, ¬ terminal state → rank state < rank (next state))
    (state : State) : terminal (run terminal next (bound + 1) state) := by
  by_contra hfinal
  have hgrowth := rank_add_fuel_le_of_not_terminal_run terminal next rank
    rank_strict hfinal
  have hbound := rank_le (run terminal next (bound + 1) state)
  omega

variable {V State : Type*} [Fintype V] [DecidableEq V]

/-- The generated up-set of every hypergraph on `V` has at most `2 ^ |V|`
members. -/
theorem upClosure_card_le_two_pow (H : Hypergraph V) :
    H.upClosure.card ≤ 2 ^ Fintype.card V := by
  have hfilter : H.upClosure.card ≤ ((Finset.univ : Finset V).powerset).card := by
    rw [Hypergraph.upClosure]
    exact Finset.card_filter_le _ _
  simpa using hfilter

/-- Hypergraph-specialized fuel theorem.  If each nonterminal transition
strictly increases the cardinality of the generated up-set, the state reached
with fuel `2 ^ |V| + 1` is terminal. -/
theorem terminal_run_upClosure (terminal : State → Prop) [DecidablePred terminal]
    (next : State → State) (family : State → Hypergraph V)
    (upClosure_strict : ∀ state, ¬ terminal state →
      (family state).upClosure.card < (family (next state)).upClosure.card)
    (state : State) :
    terminal (run terminal next (2 ^ Fintype.card V + 1) state) := by
  exact terminal_run_of_strict_bounded_rank terminal next
    (fun state => (family state).upClosure.card) (2 ^ Fintype.card V)
    (fun state => upClosure_card_le_two_pow (family state)) upClosure_strict state

end ContainerFuel
end Erdos565
