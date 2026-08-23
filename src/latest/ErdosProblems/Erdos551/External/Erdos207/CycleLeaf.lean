/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# The cycle-leaf lemma for the Erdős 207 sphere gadget

The in/out triangles of one sphere are indexed by edges of a cycle of length
`2*q`.  This file proves the elementary fact used in the sphere expansion:
a nonempty selection of at most `q` cycle edges either uses only the one
exceptional root edge, or has a degree-one cycle vertex away from the two
root vertices.
-/

namespace Erdos207

open Finset

/-- The ordinary predecessor of a nonzero `Fin n`, without cyclic wrap. -/
def finPred {n : ℕ} (k : Fin n) (hk : 0 < k.val) : Fin n :=
  ⟨k.val - 1, by omega⟩

@[simp]
lemma finPred_val {n : ℕ} (k : Fin n) (hk : 0 < k.val) :
    (finPred k hk).val = k.val - 1 := rfl

/-- Cyclic successor on a nonempty finite interval. -/
def finCycleSucc {n : ℕ} (hn : 0 < n) (k : Fin n) : Fin n :=
  if h : k.val + 1 < n then ⟨k.val + 1, h⟩ else ⟨0, hn⟩

@[simp]
lemma finCycleSucc_val {n : ℕ} (hn : 0 < n) (k : Fin n) :
    (finCycleSucc hn k).val = (k.val + 1) % n := by
  unfold finCycleSucc
  split
  · rename_i h
    simp [Nat.mod_eq_of_lt h]
  · rename_i h
    have htop : k.val + 1 = n := by omega
    simp [htop]

/-- On a cycle with at least two vertices, successor has no fixed point. -/
lemma finCycleSucc_ne {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    finCycleSucc (by omega) k ≠ k := by
  intro hfixed
  unfold finCycleSucc at hfixed
  split at hfixed
  · have := Fin.ext_iff.mp hfixed
    simp at this
  · have hkzero : k.val = 0 := by
      simpa using Fin.ext_iff.mp hfixed.symm
    rename_i hlast
    apply hlast
    omega

/-- Cyclic successor is injective. -/
lemma finCycleSucc_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (finCycleSucc hn) := by
  intro j u h
  unfold finCycleSucc at h
  split at h
  · rename_i hj
    split at h
    · have hval := Fin.ext_iff.mp h
      apply Fin.ext
      simp at hval ⊢
      omega
    · have hval := Fin.ext_iff.mp h
      simp at hval
  · rename_i hj
    split at h
    · have hval := Fin.ext_iff.mp h
      simp at hval
    · rename_i hu
      apply Fin.ext
      omega

/-- A cycle of length at least three has no two-cycle. -/
lemma finCycleSucc_sq_ne {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    finCycleSucc (by omega) (finCycleSucc (by omega) k) ≠ k := by
  intro h
  by_cases h₁ : k.val + 1 < n
  · have hs₁ : finCycleSucc (by omega) k = ⟨k.val + 1, h₁⟩ := by
      simp [finCycleSucc, h₁]
    rw [hs₁] at h
    by_cases h₂ : k.val + 1 + 1 < n
    · have hs₂ : finCycleSucc (by omega) (⟨k.val + 1, h₁⟩ : Fin n) =
          ⟨k.val + 1 + 1, h₂⟩ := by
        simp [finCycleSucc, h₂]
      rw [hs₂] at h
      have hval := Fin.ext_iff.mp h
      simp at hval
      omega
    · have hs₂ : finCycleSucc (by omega) (⟨k.val + 1, h₁⟩ : Fin n) =
          ⟨0, by omega⟩ := by
        simp [finCycleSucc, h₂]
      rw [hs₂] at h
      have hval := Fin.ext_iff.mp h
      simp at hval
      omega
  · have htop : k.val + 1 = n := by omega
    have hs₁ : finCycleSucc (by omega) k = ⟨0, by omega⟩ := by
      simp [finCycleSucc, h₁]
    rw [hs₁] at h
    have hzeroStep : (0 : ℕ) + 1 < n := by omega
    have hs₂ : finCycleSucc (by omega) (⟨0, by omega⟩ : Fin n) =
        ⟨1, hzeroStep⟩ := by
      simp [finCycleSucc, hzeroStep]
    rw [hs₂] at h
    have hval := Fin.ext_iff.mp h
    simp at hval
    omega

/-- An unoriented edge of a cycle of length at least three has a unique
lower-endpoint index. -/
lemma cycleEdge_index_unique {n : ℕ} (hn : 3 ≤ n) (j u : Fin n)
    (h : ({j, finCycleSucc (by omega) j} : Finset (Fin n)) =
      {u, finCycleSucc (by omega) u}) : j = u := by
  have hj : j = u ∨ j = finCycleSucc (by omega) u := by
    have : j ∈ ({u, finCycleSucc (by omega) u} : Finset (Fin n)) := by
      rw [← h]
      simp
    simpa [eq_comm] using this
  rcases hj with hju | hjs
  · exact hju
  have hu : u = j ∨ u = finCycleSucc (by omega) j := by
    have : u ∈ ({j, finCycleSucc (by omega) j} : Finset (Fin n)) := by
      rw [h]
      simp
    simpa [eq_comm] using this
  rcases hu with huj | hus
  · exact huj.symm
  · exfalso
    subst j
    exact finCycleSucc_sq_ne hn u hus.symm

/-- Away from zero, the cyclic successor equals `k` exactly when its input
is the ordinary predecessor of `k`. -/
lemma finCycleSucc_eq_iff_eq_finPred {n : ℕ} (hn : 0 < n)
    (j k : Fin n) (hk : 0 < k.val) :
    finCycleSucc hn j = k ↔ j = finPred k hk := by
  constructor
  · intro h
    unfold finCycleSucc at h
    split at h
    · apply Fin.ext
      have hval := Fin.ext_iff.mp h
      simp at hval ⊢
      omega
    · have hkzero : k.val = 0 := by
        simpa using Fin.ext_iff.mp h.symm
      omega
  · intro h
    subst j
    unfold finCycleSucc
    split
    · apply Fin.ext
      simp
      omega
    · rename_i hlast
      exfalso
      apply hlast
      simp
      omega

/-- Cyclic predecessor, inverse to `finCycleSucc`. -/
def finCyclePred {n : ℕ} (hn : 0 < n) (k : Fin n) : Fin n :=
  if h : k.val = 0 then ⟨n - 1, by omega⟩ else finPred k (by omega)

lemma finCycleSucc_pred {n : ℕ} (hn : 0 < n) (k : Fin n) :
    finCycleSucc hn (finCyclePred hn k) = k := by
  unfold finCyclePred
  split
  · rename_i hk
    have hkfin : k = (⟨0, hn⟩ : Fin n) := by
      apply Fin.ext
      simpa using hk
    rw [hkfin]
    apply Fin.ext
    simp only [finCycleSucc_val]
    have hnsub : n - 1 + 1 = n := by omega
    simp [hnsub]
  · rename_i hk
    apply (finCycleSucc_eq_iff_eq_finPred hn _ k (by omega)).mpr
    rfl

lemma finCyclePred_succ {n : ℕ} (hn : 0 < n) (k : Fin n) :
    finCyclePred hn (finCycleSucc hn k) = k := by
  apply finCycleSucc_injective hn
  rw [finCycleSucc_pred]

/-- A non-root vertex of the cycle is incident with exactly one selected
edge.  Cycle edges are indexed by their upper endpoint here, so the two
incident edges at `k` have indices `k-1` and `k`. -/
def IsPrivateCycleLeaf {n : ℕ} (S : Finset (Fin n)) (k : Fin n) : Prop :=
  2 ≤ k.val ∧ ∃ hk : 0 < k.val,
    ¬ (finPred k hk ∈ S ↔ k ∈ S)

/-- Cycle-leaf dichotomy underlying KSSS's sphere expansion lemma. -/
theorem exists_private_cycle_leaf_or_exceptional
    {q : ℕ} (hq : 2 ≤ q) (S : Finset (Fin (2 * q)))
    (hcard : S.card ≤ q) :
    (∀ j ∈ S, j.val = 0) ∨ ∃ k, IsPrivateCycleLeaf S k := by
  by_cases hzero : ∀ j ∈ S, j.val = 0
  · exact Or.inl hzero
  right
  have hex : ∃ j ∈ S, j.val ≠ 0 := by
    by_contra hnone
    apply hzero
    intro j hjS
    by_contra hjne
    exact hnone ⟨j, hjS, hjne⟩
  obtain ⟨j, hjS, hjne⟩ := hex
  have hjpos : 1 ≤ j.val := by omega
  by_contra hleaf
  have hnoleaf : ∀ k : Fin (2 * q), ¬ IsPrivateCycleLeaf S k :=
    not_exists.mp hleaf
  have hstep : ∀ k : Fin (2 * q), (hk2 : 2 ≤ k.val) →
      (finPred k (by omega) ∈ S ↔ k ∈ S) := by
    intro k hk2
    by_contra hiff
    exact hnoleaf k ⟨hk2, ⟨by omega, hiff⟩⟩
  have hnpos : 0 < 2 * q := by omega
  let one : Fin (2 * q) := ⟨1, by omega⟩
  have hchain : ∀ m : ℕ, 1 ≤ m → (hm : m < 2 * q) →
      (one ∈ S ↔ (⟨m, hm⟩ : Fin (2 * q)) ∈ S) := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ m ih =>
        intro hm1 hmlt
        by_cases hm0 : m = 0
        · subst m
          rfl
        · have hm1' : 1 ≤ m := by omega
          have hmlt' : m < 2 * q := by omega
          have hprev := ih hm1' hmlt'
          let curr : Fin (2 * q) := ⟨m + 1, hmlt⟩
          have hcurr : 2 ≤ curr.val := by simp [curr]; omega
          have hs := hstep curr hcurr
          have hpred : finPred curr (by omega) =
              (⟨m, hmlt'⟩ : Fin (2 * q)) := by
            apply Fin.ext
            simp [finPred, curr]
          rw [hpred] at hs
          exact hprev.trans hs
  have hone : one ∈ S := by
    have hj' : (⟨j.val, j.isLt⟩ : Fin (2 * q)) ∈ S := by
      simpa using hjS
    exact (hchain j.val hjpos j.isLt).mpr hj'
  have hall : ∀ x : Fin (2 * q), x.val ≠ 0 → x ∈ S := by
    intro x hx
    have hx1 : 1 ≤ x.val := by omega
    have hx' := (hchain x.val hx1 x.isLt).mp hone
    simpa using hx'
  let z : Fin (2 * q) := ⟨0, hnpos⟩
  have hsub : (univ.erase z : Finset (Fin (2 * q))) ⊆ S := by
    intro x hx
    have hxne : x ≠ z := (mem_erase.mp hx).1
    apply hall x
    intro hxzero
    apply hxne
    apply Fin.ext
    simpa [z] using hxzero
  have hlower := card_le_card hsub
  have hzmem : z ∈ (univ : Finset (Fin (2 * q))) := mem_univ z
  rw [card_erase_of_mem hzmem, card_univ, Fintype.card_fin] at hlower
  omega

end Erdos207
