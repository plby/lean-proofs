import ErdosProblems.Erdos788.GraphFormulation
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Normalized sum graphs

The paper translates `I n` to `0, ..., n - 2`.  This file introduces the
corresponding graph on `Fin N` and proves the basic maximum-degree estimate.
-/

namespace Erdos788

open Finset

/-- The normalized sum graph on `0, ..., N - 1`. -/
def sumGraph (N : ℕ) (A : Finset ℕ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun x y ↦ x.1 + y.1 ∈ A

@[simp]
theorem sumGraph_adj {N : ℕ} {A : Finset ℕ} {x y : Fin N} :
    (sumGraph N A).Adj x y ↔ x ≠ y ∧ x.1 + y.1 ∈ A := by
  simp [sumGraph, add_comm]

noncomputable instance sumGraphDecidableAdj (N : ℕ) (A : Finset ℕ) :
    DecidableRel (sumGraph N A).Adj :=
  Classical.decRel _

/-- Admissibility in normalized coordinates. -/
def NormalizedAdmissible {N : ℕ} (A : Finset ℕ)
    (C : Finset (Fin N)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x.1 + y.1 ∉ A

theorem normalizedAdmissible_iff_isIndepSet
    {N : ℕ} {A : Finset ℕ} {C : Finset (Fin N)} :
    NormalizedAdmissible A C ↔
      (sumGraph N A).IsIndepSet (C : Set (Fin N)) := by
  rw [SimpleGraph.isIndepSet_iff]
  simp only [Set.Pairwise, Finset.mem_coe]
  constructor
  · intro h x hx y hy hxy
    exact sumGraph_adj.mp.mt fun hadj ↦ h x hx y hy hxy hadj.2
  · intro h x hx y hy hxy hsum
    exact h hx hy hxy (sumGraph_adj.mpr ⟨hxy, hsum⟩)

/-- Adding a fixed vertex to the vertex label is injective. -/
def addEmbedding {N : ℕ} (x : Fin N) : Fin N ↪ ℕ where
  toFun y := x.1 + y.1
  inj' := by
    intro y z h
    apply Fin.ext
    exact Nat.add_left_cancel h

/-- Equation (2.1): each selected sum supplies at most one neighbor of a
fixed vertex. -/
theorem degree_sumGraph_le_card {N : ℕ} (A : Finset ℕ) (x : Fin N) :
    (sumGraph N A).degree x ≤ A.card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← card_map (addEmbedding x)]
  apply card_le_card
  intro s hs
  rw [mem_map] at hs
  obtain ⟨y, hy, rfl⟩ := hs
  have hadj : (sumGraph N A).Adj x y :=
    (SimpleGraph.mem_neighborFinset (G := sumGraph N A) (v := x) y).mp hy
  exact (sumGraph_adj.mp hadj).2

theorem maxDegree_sumGraph_le_card {N : ℕ} (A : Finset ℕ) :
    (sumGraph N A).maxDegree ≤ A.card := by
  exact SimpleGraph.maxDegree_le_of_forall_degree_le (G := sumGraph N A)
    A.card (degree_sumGraph_le_card A)

end Erdos788
