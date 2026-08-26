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
import ErdosProblems.Erdos19.Pippenger.Fractional
import Mathlib.Data.Finset.Powerset

/-!
# Finite weighted hypergraphs for the Kahn rounding step

Edges are indexed by a finite type rather than stored as a set.  This permits
parallel indexed edges, which is convenient when local fractional packings are
averaged before equal supports are collected.  All mathematical content is in
the finite support map.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A finite incidence hypergraph.  `E` indexes its (possibly parallel)
hyperedges and `support e` is the finite set of vertices incident with `e`. -/
structure FiniteHypergraph (V E : Type*) where
  vertexSet : Finset V
  support : E → Finset V
  support_subset_vertexSet : ∀ e, support e ⊆ vertexSet

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Every hyperedge has at most `k` vertices. -/
def IsBounded (H : FiniteHypergraph V E) (k : ℕ) : Prop :=
  ∀ e, (H.support e).card ≤ k

/-- Every indexed hyperedge has exactly `k` vertices. -/
def IsUniform (H : FiniteHypergraph V E) (k : ℕ) : Prop :=
  ∀ e, (H.support e).card = k

/-- Total weight of all indexed hyperedges. -/
def totalWeight (_H : FiniteHypergraph V E) (w : E → ℝ) : ℝ :=
  ∑ e, w e

/-- Fractional load at a vertex. -/
def vertexLoad (H : FiniteHypergraph V E) (w : E → ℝ) (v : V) : ℝ :=
  ∑ e with v ∈ H.support e, w e

/-- Fractional codegree load at two vertices. -/
def pairLoad (H : FiniteHypergraph V E) (w : E → ℝ) (x y : V) : ℝ :=
  ∑ e with x ∈ H.support e ∧ y ∈ H.support e, w e

/-- A nonnegative edge weighting with load at most one at every vertex. -/
def IsFractionalMatching (H : FiniteHypergraph V E) (w : E → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧ ∀ v ∈ H.vertexSet, H.vertexLoad w v ≤ 1

/-- All distinct-vertex fractional codegrees are strictly below `δ`. -/
def PairCodegreeLT (H : FiniteHypergraph V E) (w : E → ℝ) (δ : ℝ) : Prop :=
  ∀ x y, x ≠ y → H.pairLoad w x y < δ

/-- A selected family of indexed hyperedges with pairwise disjoint supports. -/
def IsMatching (H : FiniteHypergraph V E) (M : Finset E) : Prop :=
  (M : Set E).Pairwise fun e f ↦ Disjoint (H.support e) (H.support f)

lemma IsFractionalMatching.nonneg {H : FiniteHypergraph V E} {w : E → ℝ}
    (hw : H.IsFractionalMatching w) (e : E) : 0 ≤ w e :=
  hw.1 e

lemma IsFractionalMatching.vertexLoad_le_one
    {H : FiniteHypergraph V E} {w : E → ℝ}
    (hw : H.IsFractionalMatching w) {v : V} (hv : v ∈ H.vertexSet) :
    H.vertexLoad w v ≤ 1 :=
  hw.2 v hv

lemma totalWeight_nonneg {H : FiniteHypergraph V E} {w : E → ℝ}
    (hw : H.IsFractionalMatching w) : 0 ≤ H.totalWeight w := by
  exact sum_nonneg fun e _ ↦ hw.nonneg e

@[simp] lemma totalWeight_zero (H : FiniteHypergraph V E) :
    H.totalWeight (fun _ : E ↦ (0 : ℝ)) = 0 := by
  simp [totalWeight]

@[simp] lemma vertexLoad_zero (H : FiniteHypergraph V E) (v : V) :
    H.vertexLoad (fun _ ↦ 0) v = 0 := by
  simp [vertexLoad]

@[simp] lemma pairLoad_zero (H : FiniteHypergraph V E) (x y : V) :
    H.pairLoad (fun _ ↦ 0) x y = 0 := by
  simp [pairLoad]

lemma isFractionalMatching_zero (H : FiniteHypergraph V E) :
    H.IsFractionalMatching (fun _ ↦ 0) := by
  constructor
  · simp
  · intro v hv
    simp

lemma empty_isMatching (H : FiniteHypergraph V E) : H.IsMatching ∅ := by
  simp [IsMatching]

end FiniteHypergraph

/-- The finite epsilon--delta weighted matching theorem used in the one-shot
rounding of Erdős 76.  This is Kahn's weighted
Frankl--Rödl--Pippenger theorem in the cardinality-only form recorded by
Keevash. -/
def KahnWeightedMatching : Prop :=
  ∀ k : ℕ, 0 < k → ∀ ζ : ℝ, 0 < ζ → ∃ δ : ℝ, 0 < δ ∧
    ∀ (V E : Type) [DecidableEq V] [Fintype E] [DecidableEq E],
      ∀ (H : FiniteHypergraph V E) (w : E → ℝ),
        H.IsUniform k → H.IsFractionalMatching w → H.PairCodegreeLT w δ →
          ∃ M : Finset E, H.IsMatching M ∧
            H.totalWeight w ≤ (M.card : ℝ) + ζ * H.vertexSet.card

end

end Erdos76
