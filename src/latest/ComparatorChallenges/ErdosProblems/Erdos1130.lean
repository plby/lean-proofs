/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1130

open scoped BigOperators
open Finset Set

structure NodeConfiguration (n : ℕ) where
  nodes : Fin n → ℝ
  strictMono_nodes : StrictMono nodes
  nodes_mem : ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

instance {n : ℕ} : CoeFun (NodeConfiguration n) (fun _ ↦ Fin n → ℝ) :=
  ⟨NodeConfiguration.nodes⟩

noncomputable def lagrangeBasis {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k, (x - X i) / (X k - X i)

noncomputable def lebesgueFunction {n : ℕ} (X : NodeConfiguration n)
    (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis X k x|

def augmentedNodes {n : ℕ} (X : NodeConfiguration n) : Fin (n + 2) → ℝ :=
  Fin.cons (-1) (Fin.snoc X.nodes 1)

noncomputable def localPeak {n : ℕ} (X : NodeConfiguration n)
    (i : Fin (n + 1)) : ℝ :=
  sSup (lebesgueFunction X ''
    Set.Icc (augmentedNodes X i.castSucc) (augmentedNodes X i.succ))

noncomputable def upsilon {n : ℕ} (X : NodeConfiguration n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (localPeak X)

def GapPeaksEqual {n : ℕ} (X : NodeConfiguration n) : Prop :=
  ∀ i j, localPeak X i = localPeak X j

def IsUpsilonMaximizer {n : ℕ} (X : NodeConfiguration n) : Prop :=
  ∀ Y : NodeConfiguration n, upsilon Y ≤ upsilon X

theorem erdos_1130_free_node_characterization_false :
    ∃ X : NodeConfiguration 3,
      IsUpsilonMaximizer X ∧ ¬ GapPeaksEqual X := by
  sorry

end Erdos1130
