/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# The Janzer--Sudakov random-restriction lemma

This file uses a finite bipartite incidence relation rather than a graph on a
sum type.  Thus there is no bookkeeping involving the two vertex parts.  All
density conclusions are cross-multiplied natural-number inequalities; in
particular, no division-by-zero convention is hidden in the statement.
-/

open Finset Fintype

namespace Erdos182

section Bipartite

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The neighbors in `B` of a vertex in `A`. -/
def bipNeighborsA (R : A → B → Prop) [DecidableRel R] (u : A) : Finset B :=
  Finset.univ.filter (R u)

/-- The neighbors in `A` of a vertex in `B`. -/
def bipNeighborsB (R : A → B → Prop) [DecidableRel R] (v : B) : Finset A :=
  Finset.univ.filter fun u ↦ R u v

/-- Degree of an `A`-vertex in a finite bipartite incidence relation. -/
def bipDegreeA (R : A → B → Prop) [DecidableRel R] (u : A) : ℕ :=
  (bipNeighborsA R u).card

/-- Degree of a `B`-vertex in a finite bipartite incidence relation. -/
def bipDegreeB (R : A → B → Prop) [DecidableRel R] (v : B) : ℕ :=
  (bipNeighborsB R v).card

/-- Number of common `B`-neighbors of two `A`-vertices. -/
def bipCodegree (R : A → B → Prop) [DecidableRel R] (u w : A) : ℕ :=
  (Finset.univ.filter fun v ↦ R u v ∧ R w v).card

/-- Number of incidences of a finite bipartite relation. -/
def bipEdgeCount (R : A → B → Prop) [DecidableRel R] : ℕ :=
  ∑ u, bipDegreeA R u

/-- Number of incidences left after restricting both parts. -/
def bipRestrictedEdgeCount (R : A → B → Prop) [DecidableRel R]
    (A' : Finset A) (B' : Finset B) : ℕ :=
  ∑ u ∈ A', (B'.filter (R u)).card

/-- Degree of an `A`-vertex into a restricted `B`-part. -/
def bipRestrictedDegreeA (R : A → B → Prop) [DecidableRel R]
    (B' : Finset B) (u : A) : ℕ :=
  (B'.filter (R u)).card

@[simp] theorem mem_bipNeighborsA {R : A → B → Prop} [DecidableRel R]
    {u : A} {v : B} : v ∈ bipNeighborsA R u ↔ R u v := by
  simp [bipNeighborsA]

@[simp] theorem mem_bipNeighborsB {R : A → B → Prop} [DecidableRel R]
    {u : A} {v : B} : u ∈ bipNeighborsB R v ↔ R u v := by
  simp [bipNeighborsB]

/-- Double-counting the incidences by the two vertex parts. -/
theorem bipEdgeCount_eq_sum_degreeB (R : A → B → Prop) [DecidableRel R] :
    bipEdgeCount R = ∑ v, bipDegreeB R v := by
  classical
  simp only [bipEdgeCount, bipDegreeA, bipDegreeB, bipNeighborsA, bipNeighborsB,
    Finset.card_filter]
  rw [Finset.sum_comm]

/-- The conclusion of the random-restriction lemma, stated without quotients.
The first inequality says `Q / (10 x r) ≤ e / |A'|`; the second says
`Δ_A ≤ 40 x r² e / |A'|`. -/
def IsKeyRestriction (R : A → B → Prop) [DecidableRel R]
    (r x Q : ℕ) (A' : Finset A) (B' : Finset B) : Prop :=
  A'.Nonempty ∧
    (∀ v : ↑B', ∀ u, R u v.1 → u ∈ A') ∧
    Q * A'.card ≤ 10 * x * r * bipRestrictedEdgeCount R A' B' ∧
    ∀ u ∈ A',
      bipRestrictedDegreeA R B' u * A'.card ≤
        40 * x * r ^ 2 * bipRestrictedEdgeCount R A' B'

end Bipartite

end Erdos182
