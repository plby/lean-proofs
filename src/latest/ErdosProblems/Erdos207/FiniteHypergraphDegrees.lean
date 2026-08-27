/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformSampledHypergraph
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual finite-hypergraph degree extrema and regularization weights -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def finiteHypergraphDegree
    {V : Type*} [DecidableEq V] (G : Finset (Finset V)) (v : V) : ℕ :=
  (G.filter fun E ↦ v ∈ E).card

def finiteHypergraphMaxDegree
    {V : Type*} [Fintype V] [DecidableEq V] (G : Finset (Finset V)) : ℕ :=
  univ.sup (finiteHypergraphDegree G)

def finiteHypergraphMinDegree
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : Finset (Finset V)) : ℕ :=
  univ.inf' univ_nonempty (finiteHypergraphDegree G)

def finiteHypergraphDegreeGap
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : Finset (Finset V)) : ℕ :=
  finiteHypergraphMaxDegree G - finiteHypergraphMinDegree G

theorem finiteHypergraphDegree_mono
    {V : Type*} [DecidableEq V] {G H : Finset (Finset V)} (h : G ⊆ H) (v : V) :
    finiteHypergraphDegree G v ≤ finiteHypergraphDegree H v :=
  card_le_card (filter_subset_filter _ h)

theorem finiteHypergraphDegree_union
    {V : Type*} [DecidableEq V] (G H : Finset (Finset V)) (h : Disjoint G H) (v : V) :
    finiteHypergraphDegree (G ∪ H) v = finiteHypergraphDegree G v + finiteHypergraphDegree H v := by
  unfold finiteHypergraphDegree
  rw [filter_union, card_union_of_disjoint]
  exact h.mono (filter_subset _ _) (filter_subset _ _)

theorem finiteHypergraphDegree_le_max
    {V : Type*} [Fintype V] [DecidableEq V] (G : Finset (Finset V)) (v : V) :
    finiteHypergraphDegree G v ≤ finiteHypergraphMaxDegree G :=
  le_sup (f := finiteHypergraphDegree G) (mem_univ v)

theorem finiteHypergraphMinDegree_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : Finset (Finset V)) (v : V) :
    finiteHypergraphMinDegree G ≤ finiteHypergraphDegree G v :=
  inf'_le (finiteHypergraphDegree G) (mem_univ v)

theorem finiteHypergraphMaxDegree_le_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : Finset (Finset V)) (D : ℕ) :
    finiteHypergraphMaxDegree G ≤ D ↔ ∀ v, finiteHypergraphDegree G v ≤ D := by
  simp [finiteHypergraphMaxDegree]

theorem finiteHypergraphMinDegree_le_max
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : Finset (Finset V)) :
    finiteHypergraphMinDegree G ≤ finiteHypergraphMaxDegree G := by
  obtain ⟨v⟩ := ‹Nonempty V›
  exact (finiteHypergraphMinDegree_le G v).trans (finiteHypergraphDegree_le_max G v)

def finiteHypergraphRegularizationWeight
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : Finset (Finset V)) (v : V) : ℝ≥0 :=
  (finiteHypergraphMaxDegree G + finiteHypergraphDegreeGap G - finiteHypergraphDegree G v : ℕ)

theorem finiteHypergraphRegularizationWeight_bounds
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : Finset (Finset V)) (v : V) :
    (finiteHypergraphDegreeGap G : ℝ≥0) ≤ finiteHypergraphRegularizationWeight G v ∧
      finiteHypergraphRegularizationWeight G v ≤ 2 * (finiteHypergraphDegreeGap G : ℝ≥0) := by
  have hmin := finiteHypergraphMinDegree_le G v
  have hmax := finiteHypergraphDegree_le_max G v
  have horder := finiteHypergraphMinDegree_le_max G
  unfold finiteHypergraphRegularizationWeight finiteHypergraphDegreeGap
  constructor <;> exact_mod_cast (by omega :
    _)

theorem finiteHypergraphRegularizationWeight_center
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : Finset (Finset V)) (v : V) :
    (finiteHypergraphDegree G v : ℝ) + (finiteHypergraphRegularizationWeight G v : ℝ) =
      finiteHypergraphMaxDegree G + (finiteHypergraphDegreeGap G : ℝ) := by
  have hmax := finiteHypergraphDegree_le_max G v
  have heq : finiteHypergraphDegree G v +
      (finiteHypergraphMaxDegree G + finiteHypergraphDegreeGap G - finiteHypergraphDegree G v) =
      finiteHypergraphMaxDegree G + finiteHypergraphDegreeGap G := by omega
  unfold finiteHypergraphRegularizationWeight
  exact_mod_cast heq

end

end Erdos207
