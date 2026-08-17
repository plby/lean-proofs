/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Basic
import ErdosProblems.Erdos171.Framework

/-!
# Public statement of Erdős Problem 171

This file connects the internal real-valued density formulation of density
Hales--Jewett to the cardinality inequality in the statement of Erdős Problem
171.  It also spells out Mathlib's combinatorial-line structure coordinate by
coordinate: every coordinate is either the alphabet parameter or a constant,
and at least one coordinate is the parameter.

No density-Hales--Jewett result is assumed globally here.  The packaging
theorems take `EventualDensityHJ t` as an explicit hypothesis.
-/

namespace Erdos171

open Set

/-- A parametrized family of words has the coordinate pattern of a proper
combinatorial line: every coordinate is either the parameter itself or is
constant, and at least one coordinate is the parameter. -/
def IsCoordinateLine {t n : ℕ} (p : Fin t → Word t n) : Prop :=
  (∀ j : Fin n,
      (∀ a : Fin t, p a j = a) ∨
        ∃ c : Fin t, ∀ a : Fin t, p a j = c) ∧
    ∃ j : Fin n, ∀ a : Fin t, p a j = a

/-- The wildcard coordinate makes a coordinatewise line parametrization
injective, so its range really consists of `t` parametrized points. -/
theorem IsCoordinateLine.injective {t n : ℕ} {p : Fin t → Word t n}
    (hp : IsCoordinateLine p) : Function.Injective p := by
  intro a b hab
  obtain ⟨j, hj⟩ := hp.2
  have hcoord := congrFun hab j
  simpa only [hj a, hj b] using hcoord

/-- A coordinatewise line over `Fin t` has exactly `t` points. -/
theorem IsCoordinateLine.ncard_range {t n : ℕ} {p : Fin t → Word t n}
    (hp : IsCoordinateLine p) : Set.ncard (Set.range p) = t := by
  rw [Set.ncard_range_of_injective hp.injective]
  simp

/-- Evaluation of a Mathlib combinatorial line has the coordinatewise form
used in the statement of Erdős Problem 171. -/
theorem isCoordinateLine_of_line {t n : ℕ}
    (l : Combinatorics.Line (Fin t) (Fin n)) : IsCoordinateLine l := by
  constructor
  · intro j
    cases hj : l.idxFun j with
    | none =>
        exact Or.inl fun a ↦ l.apply_none a j hj
    | some c =>
        exact Or.inr ⟨c, fun _ ↦ l.apply_some hj⟩
  · obtain ⟨j, hj⟩ := l.proper
    exact ⟨j, fun a ↦ l.apply_none a j hj⟩

/-- A coordinatewise line parametrization determines Mathlib's proper
combinatorial line with exactly the same evaluation map. -/
theorem exists_line_eq_of_isCoordinateLine {t n : ℕ} {p : Fin t → Word t n}
    (hp : IsCoordinateLine p) :
    ∃ l : Combinatorics.Line (Fin t) (Fin n), (⇑l) = p := by
  classical
  let idx : Fin n → Option (Fin t) := fun j ↦
    if h : ∀ a : Fin t, p a j = a then none
    else some (Classical.choose ((hp.1 j).resolve_left h))
  have hproper : ∃ j, idx j = none := by
    obtain ⟨j, hj⟩ := hp.2
    exact ⟨j, by simp [idx, hj]⟩
  let l : Combinatorics.Line (Fin t) (Fin n) :=
    { idxFun := idx
      proper := hproper }
  refine ⟨l, ?_⟩
  funext a j
  by_cases hj : ∀ b : Fin t, p b j = b
  · simp [l, idx, hj, Combinatorics.Line.coe_apply]
  · have hc := Classical.choose_spec ((hp.1 j).resolve_left hj)
    simpa [l, idx, hj, Combinatorics.Line.coe_apply] using (hc a).symm

/-- Coordinatewise characterization of `ContainsLine`, including membership
of every parametrized word in the ambient set. -/
theorem containsLine_iff_exists_coordinateLine {t n : ℕ}
    {A : Set (Word t n)} :
    ContainsLine A ↔
      ∃ p : Fin t → Word t n,
        IsCoordinateLine p ∧ ∀ a : Fin t, p a ∈ A := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, isCoordinateLine_of_line l, fun a ↦ hl ⟨a, rfl⟩⟩
  · rintro ⟨p, hp, hA⟩
    obtain ⟨l, rfl⟩ := exists_line_eq_of_isCoordinateLine hp
    exact (containsLine_iff (A := A)).2 ⟨l, hA⟩

/-- Finset version of the coordinatewise characterization of
`ContainsLine`. -/
theorem containsLine_coe_finset_iff_exists_coordinateLine {t n : ℕ}
    {A : Finset (Word t n)} :
    ContainsLine (A : Set (Word t n)) ↔
      ∃ p : Fin t → Word t n,
        IsCoordinateLine p ∧ ∀ a : Fin t, p a ∈ A := by
  simpa only [Finset.mem_coe] using
    (containsLine_iff_exists_coordinateLine
      (A := (A : Set (Word t n))))

/-- The cardinality formulation of the eventual density Hales--Jewett
property for the alphabet `Fin t`.  This is the literal quantitative
hypothesis in Erdős Problem 171. -/
def CardinalityEventualDensityHJ (t : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset (Word t N),
      ε * (t : ℝ) ^ N ≤ (A.card : ℝ) →
        ContainsLine (A : Set (Word t N))

/-- For a nonempty alphabet, the real-valued density formulation implies the
literal cardinality formulation in Erdős Problem 171. -/
theorem EventualDensityHJ.cardinality {t : ℕ} (ht : 0 < t)
    (h : EventualDensityHJ t) : CardinalityEventualDensityHJ t := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  refine ⟨N₀, ?_⟩
  intro N hN A hcard
  apply hN₀ N hN A
  rw [density_eq_card_div_card, card_word]
  simpa only [Nat.cast_pow] using
    (le_div_iff₀ (by positivity : (0 : ℝ) < (t : ℝ) ^ N)).2 hcard

/-- For a nonempty alphabet, the cardinality formulation also implies the
real-valued density formulation. -/
theorem CardinalityEventualDensityHJ.eventual {t : ℕ} (ht : 0 < t)
    (h : CardinalityEventualDensityHJ t) : EventualDensityHJ t := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := h δ hδ
  refine ⟨N₀, ?_⟩
  intro N hN A hdensity
  apply hN₀ N hN A
  rw [density_eq_card_div_card, card_word] at hdensity
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (t : ℝ) ^ N)).1
  simpa only [Nat.cast_pow] using hdensity

/-- For every positive alphabet size, the internal real-density statement and
the cardinality statement from Erdős Problem 171 are equivalent. -/
theorem eventualDensityHJ_iff_cardinality {t : ℕ} (ht : 0 < t) :
    EventualDensityHJ t ↔ CardinalityEventualDensityHJ t :=
  ⟨fun h ↦ h.cardinality ht, fun h ↦ h.eventual ht⟩

/-- The exact all-alphabet statement asked in Erdős Problem 171. -/
def Erdos171Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t →
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset (Word t N),
      ε * (t : ℝ) ^ N ≤ (A.card : ℝ) →
        ContainsLine (A : Set (Word t N))

/-- Package a proof of eventual density Hales--Jewett for every nonempty
finite alphabet into the exact statement of Erdős Problem 171. -/
theorem erdos171Statement_of_eventualDensityHJ
    (h : ∀ t : ℕ, 0 < t → EventualDensityHJ t) :
    Erdos171Statement := by
  intro ε hε t ht
  exact (h t (by omega)).cardinality (by omega) ε hε

end Erdos171
