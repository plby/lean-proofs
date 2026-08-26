/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Coverage by ordered digit frames: the first nonzero coordinate selects a tag.
Informal source: Section 5 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GridSlots

namespace Erdos1189.Grid

open Finset

variable {ι : Type*} {q : ι → ℕ}

def zeroPoint (hq : ∀ i, 0 < q i) : Point q := fun i => ⟨0, hq i⟩

def slotValue (s : Slot q) : Fin (q s.1) :=
  ⟨s.2.val + 1, by have := s.2.isLt; omega⟩

def spikePoint [DecidableEq ι] (hq : ∀ i, 0 < q i) (s : Slot q) : Point q :=
  Function.update (zeroPoint hq) s.1 (slotValue s)

lemma spikePoint_self [DecidableEq ι] (hq : ∀ i, 0 < q i) (s : Slot q) :
    spikePoint hq s s.1 = slotValue s := by simp [spikePoint]

lemma spikePoint_other [DecidableEq ι] (hq : ∀ i, 0 < q i) (s : Slot q) {i : ι}
    (hi : i ≠ s.1) :
    (spikePoint hq s i : ℕ) = 0 := by simp [spikePoint, hi, zeroPoint]

lemma first_nonzero [Finite ι] {x : Point q} (rank : ι → ℕ) (hx : ∃ i, (x i : ℕ) ≠ 0) :
    ∃ i, (x i : ℕ) ≠ 0 ∧ ∀ j, rank j < rank i → (x j : ℕ) = 0 := by
  classical
  let := Fintype.ofFinite ι
  let S := univ.filter fun i => (x i : ℕ) ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := exists_min_image S rank hS
  refine ⟨i, (mem_filter.mp hi).2, ?_⟩
  intro j hj
  by_contra hxj
  exact (not_le_of_gt hj) (hmin j (mem_filter.mpr ⟨mem_univ _, hxj⟩))

/-- Each fixed coordinate of a tag is either its own nonzero coordinate
or an earlier coordinate fixed to zero. -/
def IsOrderedTagFamily (H : Slot q → Box q) (rank : ι → ℕ) : Prop :=
  ∀ s i v, H s i = some v →
    (i = s.1 ∧ (v : ℕ) = s.2.val + 1) ∨ (rank i < rank s.1 ∧ (v : ℕ) = 0)

theorem IsOrderedTagFamily.covers_nonzero [Finite ι] {H : Slot q → Box q} {rank : ι → ℕ}
    (hH : IsOrderedTagFamily H rank) {x : Point q} (hx : ∃ i, (x i : ℕ) ≠ 0) :
    ∃ s, Contains (H s) x := by
  obtain ⟨i, hi, hfirst⟩ := first_nonzero rank hx
  have ha : (x i : ℕ) - 1 < q i - 1 := by have := (x i).isLt; omega
  let s : Slot q := ⟨i, ⟨(x i : ℕ) - 1, ha⟩⟩
  refine ⟨s, ?_⟩
  intro j v hjv
  rcases hH s j v hjv with ⟨hji, hv⟩ | ⟨hji, hv⟩
  · apply Fin.ext
    have hji' : j = i := hji
    have hxj : (x j : ℕ) = (x i : ℕ) := congrArg (fun t => (x t : ℕ)) hji'
    change (v : ℕ) = (x i : ℕ) - 1 + 1 at hv
    omega
  · apply Fin.ext
    exact (hfirst j hji).trans hv.symm

end Erdos1189.Grid
