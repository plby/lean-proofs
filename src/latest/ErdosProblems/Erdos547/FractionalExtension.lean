import ErdosProblems.Erdos547.AllocationOperations
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.BigOperators

/-!
# Extending and combining fractional matchings on vertex regions
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace FractionalMatching

open scoped Classical in
def inducedWeight (S : Set V) [Fintype S] (μ : FractionalMatching (G.induce S)) (u v : V) : ℝ :=
  if hu : u ∈ S then if hv : v ∈ S then μ.weight ⟨u, hu⟩ ⟨v, hv⟩ else 0 else 0

theorem sum_inducedWeight_of_mem (S : Set V) [Fintype S]
    (μ : FractionalMatching (G.induce S)) {u : V} (hu : u ∈ S) :
    (∑ v, inducedWeight S μ u v) = μ.load ⟨u, hu⟩ := by
  classical
  simp only [inducedWeight, dif_pos hu]
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero, load]
  exact (Equiv.subtypeEquivRight (by simp)).sum_comp fun x : S ↦ μ.weight ⟨u, hu⟩ x

theorem sum_inducedWeight_of_notMem (S : Set V) [Fintype S]
    (μ : FractionalMatching (G.induce S)) {u : V} (hu : u ∉ S) :
    (∑ v, inducedWeight S μ u v) = 0 := by
  classical
  simp [inducedWeight, hu]

/-- Extend an induced fractional matching by zero outside its region. -/
def liftInduced (S : Set V) [Fintype S] (μ : FractionalMatching (G.induce S)) :
    FractionalMatching G where
  weight := inducedWeight S μ
  symmetric u v := by
    classical
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · simp only [inducedWeight, dif_pos hu, dif_pos hv]
      exact μ.symmetric _ _
    · simp [inducedWeight, hu, hv]
    · simp [inducedWeight, hu, hv]
    · simp [inducedWeight, hu, hv]
  nonnegative u v := by
    classical
    simp only [inducedWeight]
    split_ifs <;> first | exact μ.nonnegative _ _ | exact le_rfl
  supported u v huv := by
    classical
    simp only [inducedWeight]
    split_ifs <;> first | exact μ.supported _ _ huv | rfl
  capacity u := by
    classical
    by_cases hu : u ∈ S
    · rw [sum_inducedWeight_of_mem S μ hu]
      exact μ.load_le_one _
    · rw [sum_inducedWeight_of_notMem S μ hu]
      norm_num

theorem liftInduced_load_of_mem (S : Set V) [Fintype S]
    (μ : FractionalMatching (G.induce S)) {u : V} (hu : u ∈ S) :
    (μ.liftInduced S).load u = μ.load ⟨u, hu⟩ := sum_inducedWeight_of_mem S μ hu

theorem liftInduced_load_of_notMem (S : Set V) [Fintype S]
    (μ : FractionalMatching (G.induce S)) {u : V} (hu : u ∉ S) :
    (μ.liftInduced S).load u = 0 := sum_inducedWeight_of_notMem S μ hu

theorem liftInduced_weight_eq_zero_of_notMem (S : Set V) [Fintype S]
    (μ : FractionalMatching (G.induce S)) {u v : V} (hu : u ∉ S ∨ v ∉ S) :
    (μ.liftInduced S).weight u v = 0 := by
  classical
  rcases hu with hu | hv
  · simp [liftInduced, inducedWeight, hu]
  · simp [liftInduced, inducedWeight, hv]

def sum {I : Type*} [Fintype I] (μ : I → FractionalMatching G)
    (h : ∀ u, (∑ i, (μ i).load u) ≤ 1) : FractionalMatching G where
  weight u v := ∑ i, (μ i).weight u v
  symmetric u v := Finset.sum_congr rfl fun i _ ↦ (μ i).symmetric u v
  nonnegative u v := Finset.sum_nonneg fun i _ ↦ (μ i).nonnegative u v
  supported u v huv := Finset.sum_eq_zero fun i _ ↦ (μ i).supported u v huv
  capacity u := by rw [Finset.sum_comm]; exact h u

@[simp] theorem sum_load_at {I : Type*} [Fintype I] (μ : I → FractionalMatching G)
    (h : ∀ u, (∑ i, (μ i).load u) ≤ 1) (u : V) :
    (sum μ h).load u = ∑ i, (μ i).load u := by
  exact Finset.sum_comm

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.liftInduced_load_of_mem
