/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
module

public import ErdosProblems.Erdos565.Graph
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The finite final reduction for Erdős problem 565

The probabilistic part of the induced-Ramsey proof supplies an upper bound for
each *terminal bad event*.  This file contains the deterministic argument which
turns those bounds into a Ramsey host.  In particular, the key estimate is an
ordinary theorem hypothesis about the cardinality of a filtered finite set; it
is not introduced as an unproved primitive.

The abstraction is intentionally a little more general than the application.
`bad ω s` says that the finite object `ω` is bad at state `s`, `terminal ω s`
says that the key lemma applies at that state, and `rank s` is the sum of the
orders of the current target graphs.  The descent hypothesis is exactly the
minimal-counterexample step in the paper: every nonterminal bad state has a bad
state of strictly smaller rank.
-/

@[expose] public section

open scoped BigOperators

namespace Erdos565
namespace FinalReduction

/-! ## Deterministic descent -/

/-- Repeated strict descent in a natural-valued rank reaches a terminal bad
state.  This is the formal minimal-counterexample argument used in the last
section of the proof. -/
theorem descends_to_terminal {Ω State : Type*} (rank : State → ℕ)
    (bad terminal : Ω → State → Prop)
    (descent : ∀ ω s, bad ω s → ¬ terminal ω s →
      ∃ t, bad ω t ∧ rank t < rank s) :
    ∀ ω s, bad ω s → ∃ t, bad ω t ∧ terminal ω t := by
  intro ω s
  induction h : rank s using Nat.strong_induction_on generalizing s with
  | h n ih =>
      intro hs
      by_cases hterminal : terminal ω s
      · exact ⟨s, hs, hterminal⟩
      · obtain ⟨t, ht, hlt⟩ := descent ω s hs hterminal
        exact ih (rank t) (h ▸ hlt) t rfl ht

/-- The exact finite set of terminal bad objects associated with one state. -/
noncomputable def terminalBadSet {Ω State : Type*} [Fintype Ω]
    (bad terminal : Ω → State → Prop) (s : State) : Finset Ω :=
  by
    classical
    exact Finset.univ.filter fun ω ↦ bad ω s ∧ terminal ω s

/-- The exact finite set of objects satisfying an initial bad predicate. -/
noncomputable def initialBadSet {Ω : Type*} [Fintype Ω]
    (initialBad : Ω → Prop) : Finset Ω :=
  by
    classical
    exact Finset.univ.filter initialBad

/-- Every initially bad object lies in one of the terminal bad-event sets.

The initial state is allowed to depend on the object.  In the Ramsey
application it is constant (the vertex set of the host together with `r`
copies of the target), but this slightly stronger statement costs nothing. -/
theorem initialBadSet_subset_terminalUnion
    {Ω State : Type*} [Fintype Ω] [Fintype State]
    [DecidableEq Ω]
    (rank : State → ℕ) (bad terminal : Ω → State → Prop)
    (initialBad : Ω → Prop) (initialState : Ω → State)
    (start : ∀ ω, initialBad ω → bad ω (initialState ω))
    (descent : ∀ ω s, bad ω s → ¬ terminal ω s →
      ∃ t, bad ω t ∧ rank t < rank s) :
    initialBadSet initialBad ⊆
      Finset.univ.biUnion (terminalBadSet bad terminal) := by
  classical
  intro ω hω
  have hinitial : initialBad ω := by
    simpa [initialBadSet] using hω
  obtain ⟨s, hbad, hterminal⟩ :=
    descends_to_terminal rank bad terminal descent ω (initialState ω)
      (start ω hinitial)
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_univ s, ?_⟩
  simp only [terminalBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hbad, hterminal⟩

/-! ## The exact union bound -/

/-- If every terminal bad-event set has at most `K` elements, then the set of
initially bad objects has at most `|State| K` elements.  This is the finite
counting form of the union bound; no probability space or real-valued measure
is hidden in the statement. -/
theorem card_initialBadSet_le
    {Ω State : Type*} [Fintype Ω] [Fintype State]
    (rank : State → ℕ) (bad terminal : Ω → State → Prop)
    (initialBad : Ω → Prop) (initialState : Ω → State) (K : ℕ)
    (start : ∀ ω, initialBad ω → bad ω (initialState ω))
    (descent : ∀ ω s, bad ω s → ¬ terminal ω s →
      ∃ t, bad ω t ∧ rank t < rank s)
    (key : ∀ s, (terminalBadSet bad terminal s).card ≤ K) :
    (initialBadSet initialBad).card ≤ Fintype.card State * K := by
  classical
  calc
    (initialBadSet initialBad).card ≤
        (Finset.univ.biUnion (terminalBadSet bad terminal)).card :=
      Finset.card_le_card
        (initialBadSet_subset_terminalUnion rank bad terminal initialBad
          initialState start descent)
    _ ≤ ∑ s ∈ (Finset.univ : Finset State),
          (terminalBadSet bad terminal s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ (Finset.univ : Finset State), K := by
      exact Finset.sum_le_sum fun s _ ↦ key s
    _ = Fintype.card State * K := by simp

/-- If the terminal-event union bound is strictly smaller than the finite
sample space, at least one object is not initially bad. -/
theorem exists_not_initialBad
    {Ω State : Type*} [Fintype Ω] [Fintype State]
    (rank : State → ℕ) (bad terminal : Ω → State → Prop)
    (initialBad : Ω → Prop) (initialState : Ω → State) (K : ℕ)
    (start : ∀ ω, initialBad ω → bad ω (initialState ω))
    (descent : ∀ ω s, bad ω s → ¬ terminal ω s →
      ∃ t, bad ω t ∧ rank t < rank s)
    (key : ∀ s, (terminalBadSet bad terminal s).card ≤ K)
    (small : Fintype.card State * K < Fintype.card Ω) :
    ∃ ω, ¬ initialBad ω := by
  classical
  by_contra h
  push Not at h
  have hall : initialBadSet initialBad = (Finset.univ : Finset Ω) := by
    rw [initialBadSet]
    apply Finset.filter_eq_self.mpr
    intro ω _
    exact h ω
  have hcard := card_initialBadSet_le rank bad terminal initialBad
    initialState K start descent key
  rw [hall, Finset.card_univ] at hcard
  omega

/-! ## States used by the Ramsey descent -/

/-- A state consists of the current vertex subset and one current target for
each color.  In the application `Target` is the finite type of labelled graphs
of order at most the original target order. -/
structure RamseyState (V Color Target : Type*) where
  vertices : Finset V
  targets : Color → Target

namespace RamseyState

/-- A state is equivalently its pair of fields.  Besides being occasionally
convenient for counting, this gives the finite and decidable instances below
without adding fields to the mathematical definition. -/
def equivProd {V Color Target : Type*} :
    RamseyState V Color Target ≃ Finset V × (Color → Target) where
  toFun s := (s.vertices, s.targets)
  invFun p := ⟨p.1, p.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by cases p; rfl

instance {V Color Target : Type*}
    [DecidableEq V] [Fintype Color] [DecidableEq Target] :
    DecidableEq (RamseyState V Color Target) := equivProd.decidableEq

instance {V Color Target : Type*}
    [Fintype V] [DecidableEq V] [Fintype Color] [DecidableEq Color]
    [Fintype Target] [DecidableEq Target] :
    Fintype (RamseyState V Color Target) :=
  Fintype.ofEquiv (Finset V × (Color → Target)) equivProd.symm

/-- The rank minimized in the final reduction: the sum of target orders. -/
def rank {V Color Target : Type*} [Fintype Color]
    (order : Target → ℕ) (s : RamseyState V Color Target) : ℕ :=
  ∑ i, order (s.targets i)

/-- Exact admissibility condition for the current vertex set.  The function
`requiredSize` packages the rounded power appearing in the paper. -/
def Admissible {V Color Target : Type*} [Fintype Color]
    (order : Target → ℕ) (requiredSize : ℕ → ℕ)
    (s : RamseyState V Color Target) : Prop :=
  requiredSize (s.rank order) ≤ s.vertices.card

end RamseyState

/-! ## Specialization to induced Ramsey hosts -/

/-- A finite terminal-event estimate, together with strict state descent,
produces an `N`-vertex induced Ramsey host.

For an actual invocation, `bad H s` includes both the bad-copy condition and
the exact cardinal admissibility of `s`; `terminal H s` is the event called
`E` in the paper.  Thus `descent` is precisely the deterministic reduction,
while `key` is where the separately proved probabilistic key lemma is supplied.
-/
theorem inducedRamseyOrder_of_keyEstimate
    {n N : ℕ} (G : SimpleGraph (Fin n))
    {State : Type*} [Fintype State]
    (rank : State → ℕ)
    (bad terminal : SimpleGraph (Fin N) → State → Prop)
    (initialState : SimpleGraph (Fin N) → State) (K : ℕ)
    (start : ∀ H, ¬ IsInducedRamseyWitness G H → bad H (initialState H))
    (descent : ∀ H s, bad H s → ¬ terminal H s →
      ∃ t, bad H t ∧ rank t < rank s)
    (key : ∀ s, (terminalBadSet bad terminal s).card ≤ K)
    (small : Fintype.card State * K <
      Fintype.card (SimpleGraph (Fin N))) :
    IsInducedRamseyOrder G N := by
  classical
  obtain ⟨H, hH⟩ := exists_not_initialBad rank bad terminal
    (fun H ↦ ¬ IsInducedRamseyWitness G H) initialState K start descent key small
  exact ⟨H, not_not.mp hH⟩

/-- The witness-forward bounded form used by the statement of Problem 565.
It deliberately returns the host order and its bound instead of defining a
minimum before existence has been proved. -/
theorem exists_bounded_inducedRamseyOrder_of_keyEstimate
    {n N B : ℕ} (G : SimpleGraph (Fin n)) (hNB : N ≤ B)
    {State : Type*} [Fintype State]
    (rank : State → ℕ)
    (bad terminal : SimpleGraph (Fin N) → State → Prop)
    (initialState : SimpleGraph (Fin N) → State) (K : ℕ)
    (start : ∀ H, ¬ IsInducedRamseyWitness G H → bad H (initialState H))
    (descent : ∀ H s, bad H s → ¬ terminal H s →
      ∃ t, bad H t ∧ rank t < rank s)
    (key : ∀ s, (terminalBadSet bad terminal s).card ≤ K)
    (small : Fintype.card State * K <
      Fintype.card (SimpleGraph (Fin N))) :
    ∃ m, m ≤ B ∧ IsInducedRamseyOrder G m := by
  exact ⟨N, hNB, inducedRamseyOrder_of_keyEstimate G rank bad terminal
    initialState K start descent key small⟩

end FinalReduction
end Erdos565
