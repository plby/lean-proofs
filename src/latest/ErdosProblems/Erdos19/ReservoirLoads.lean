import Mathlib.Tactic

/-! # Load balancing for repeated reservoir repairs -/

namespace Erdos19

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def totalLoad (load : V → ℕ) : ℕ := ∑ v, load v

def overloadedVertices (K : ℕ) (load : V → ℕ) : Finset V :=
  univ.filter fun v ↦ K * totalLoad load + Fintype.card V ≤ Fintype.card V * load v

def IsLoadBalanced (K : ℕ) (load : V → ℕ) : Prop :=
  ∀ v, Fintype.card V * load v ≤ K * totalLoad load + 2 * Fintype.card V

theorem overloadedVertices_card_mul_lt (K : ℕ) (load : V → ℕ)
    (hV : 0 < Fintype.card V) :
    K * (overloadedVertices K load).card < Fintype.card V := by
  let B := overloadedVertices K load
  let n := Fintype.card V
  let S := totalLoad load
  have hsum : B.card * (K * S + n) ≤ n * S := by
    calc
      B.card * (K * S + n) = ∑ _v ∈ B, (K * S + n) := by simp
      _ ≤ ∑ v ∈ B, n * load v := by
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp hv).2
      _ ≤ ∑ v : V, n * load v := sum_le_sum_of_subset (subset_univ _)
      _ = n * S := by rw [← mul_sum]; rfl
  by_contra hnot
  have hK : n ≤ K * B.card := Nat.le_of_not_gt hnot
  have hprod := Nat.mul_le_mul_right S hK
  have hzero : n * B.card = 0 := by nlinarith only [hsum, hprod]
  have hBzero : B.card = 0 := (Nat.mul_eq_zero.mp hzero).resolve_left (Nat.ne_of_gt hV)
  simp only [hBzero, Nat.mul_zero] at hK
  omega

theorem totalLoad_mono {load next : V → ℕ} (h : ∀ v, load v ≤ next v) :
    totalLoad load ≤ totalLoad next := sum_le_sum (fun v _ ↦ h v)

theorem IsLoadBalanced.step {K : ℕ} {load next : V → ℕ}
    (hbal : IsLoadBalanced K load) (hmono : ∀ v, load v ≤ next v)
    (hone : ∀ v, next v ≤ load v + 1)
    (havoid : ∀ v, load v < next v → v ∉ overloadedVertices K load) :
    IsLoadBalanced K next := by
  have htotal := Nat.mul_le_mul_left K (totalLoad_mono hmono)
  intro v
  by_cases heq : next v = load v
  · rw [heq]
    exact (hbal v).trans (Nat.add_le_add_right htotal _)
  · have hinc : load v < next v := lt_of_le_of_ne (hmono v) (Ne.symm heq)
    have hsmall : Fintype.card V * load v < K * totalLoad load + Fintype.card V := by
      have h := havoid v hinc
      simpa only [overloadedVertices, mem_filter, mem_univ, true_and, not_le] using h
    have hstep := Nat.mul_le_mul_left (Fintype.card V) (hone v)
    nlinarith only [hsmall, hstep, htotal]

theorem totalLoad_step_le_add_card {load next : V → ℕ} (T : Finset V)
    (hone : ∀ v, next v ≤ load v + 1)
    (hfixed : ∀ v ∉ T, next v = load v) :
    totalLoad next ≤ totalLoad load + T.card := by
  have hp : ∀ v, next v ≤ load v + if v ∈ T then 1 else 0 := by
    intro v
    by_cases hv : v ∈ T
    · simpa only [hv, ↓reduceIte] using hone v
    · simp only [hv, ↓reduceIte, Nat.add_zero, hfixed v hv, le_refl]
  have hs := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) ↦ hp v)
  simpa [totalLoad, sum_add_distrib] using hs

#print axioms overloadedVertices_card_mul_lt
#print axioms IsLoadBalanced.step
#print axioms totalLoad_step_le_add_card

end Erdos19
