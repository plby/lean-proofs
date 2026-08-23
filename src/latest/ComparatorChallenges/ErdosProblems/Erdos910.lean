/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Connected

open Set Function
open scoped Cardinal

namespace Erdos910

noncomputable section

abbrev Plane := ℝ × ℝ

abbrev Euclidean (n : ℕ) := Fin n → ℝ

def Nondegenerate {α : Type*} (s : Set α) : Prop :=
  ¬s.Subsingleton

def ConnectedSubsets (M : Set Plane) :=
  {N : Set Plane // N ⊆ M ∧ IsConnected N}

def EuclideanConnectedSubsets (n : ℕ) (M : Set (Euclidean n)) :=
  {N : Set (Euclidean n) // N ⊆ M ∧ IsConnected N}

def SecondQuestionAllDimensions : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ M : Set (Euclidean n), IsConnected M → Nondegenerate M →
    Cardinal.continuum < Cardinal.mk (EuclideanConnectedSubsets n M)

structure RudinCountableComplement (M : Set Plane) : Prop where
  connected : IsConnected M
  nondegenerate : Nondegenerate M
  countable_complement : ∀ N : Set Plane, N ⊆ M → IsConnected N → Nondegenerate N →
    (M \ N).Countable

def planeInterval : Set Plane := Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)

theorem erdos_910 :
    (∀ m : Set (Euclidean 1), IsConnected m → Nondegenerate m →
      ∃ n : Set (Euclidean 1),
        n ⊆ m ∧ IsConnected n ∧ Nondegenerate n ∧ ¬ Nonempty (m ≃ₜ n)) ∧
    Cardinal.mk (ConnectedSubsets planeInterval) = Cardinal.continuum ∧
    ¬ SecondQuestionAllDimensions ∧
    ∀ M : Set Plane, RudinCountableComplement M →
      Cardinal.mk (ConnectedSubsets M) = Cardinal.continuum ∧
      ∃ N : Set Plane,
        N ⊂ M ∧ IsConnected N ∧ Nondegenerate N ∧ (M \ N).Countable := by
  sorry

end

end Erdos910
