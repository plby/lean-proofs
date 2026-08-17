/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos1217.Basic
import Mathlib.Data.Nat.Nth

/-!
# Erdős Problem 1217: deterministic reindexing

This file contains the order-theoretic bookkeeping used after a sample path
has been selected.  An infinite set of hitting times is enumerated by
`Nat.nth`; passing to these times preserves both strict increase and a
step-by-step divisibility relation.  Finally, a strictly increasing sequence
of values in the range of another strictly increasing sequence has a unique
strictly increasing sequence of preimage indices.
-/

namespace Erdos1217

/-! ## Enumerating the visits to a set -/

/-- The index of the `i`th visit of `c` to `A`. -/
noncomputable def hitIndex (A : Set ℕ) (c : ℕ → ℕ) (i : ℕ) : ℕ :=
  Nat.nth (fun k ↦ c k ∈ A) i

/-- The set of hitting times of `A` by `c`. -/
def hitTimes (A : Set ℕ) (c : ℕ → ℕ) : Set ℕ :=
  {k | c k ∈ A}

@[simp]
lemma mem_hitTimes_iff {A : Set ℕ} {c : ℕ → ℕ} {k : ℕ} :
    k ∈ hitTimes A c ↔ c k ∈ A := Iff.rfl

lemma hitIndex_strictMono {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (hitTimes A c).Infinite) :
    StrictMono (hitIndex A c) := by
  exact Nat.nth_strictMono hinf

lemma hitIndex_mem {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (hitTimes A c).Infinite) (i : ℕ) :
    c (hitIndex A c i) ∈ A := by
  exact Nat.nth_mem_of_infinite hinf i

lemma range_hitIndex {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (hitTimes A c).Infinite) :
    Set.range (hitIndex A c) = hitTimes A c := by
  exact Nat.range_nth_of_infinite hinf

/-- Infinitely many distinct visited values in `A` imply infinitely many
hitting times.  This is the form naturally produced by the counting
argument. -/
lemma hitTimes_infinite_of_range_inter {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (Set.range c ∩ A).Infinite) :
    (hitTimes A c).Infinite := by
  intro hfin
  apply hinf
  apply (hfin.image c).subset
  rintro y ⟨⟨i, rfl⟩, hi⟩
  exact ⟨i, hi, rfl⟩

/-- The values selected at the hitting times are exactly the visited values
which belong to `A`. -/
lemma range_hitSubsequence {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (hitTimes A c).Infinite) :
    Set.range (fun i ↦ c (hitIndex A c i)) = Set.range c ∩ A := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨hitIndex A c i, rfl⟩, hitIndex_mem hinf i⟩
  · rintro ⟨⟨i, rfl⟩, hi⟩
    have hi' : i ∈ Set.range (hitIndex A c) := by
      rw [range_hitIndex hinf]
      exact hi
    rcases hi' with ⟨j, rfl⟩
    exact ⟨j, rfl⟩

/-- A divisibility relation between consecutive terms propagates to every
ordered pair of indices. -/
lemma dvd_of_step_dvd {c : ℕ → ℕ} (hstep : ∀ i, c i ∣ c (i + 1))
    {i j : ℕ} (hij : i ≤ j) : c i ∣ c j := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_rfl
  | succ j hij ih => exact ih.trans (hstep j)

/-- Passing to the successive hitting times preserves stepwise divisibility. -/
lemma hitSubsequence_step_dvd {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (hitTimes A c).Infinite) (hstep : ∀ i, c i ∣ c (i + 1)) (i : ℕ) :
    c (hitIndex A c i) ∣ c (hitIndex A c (i + 1)) := by
  apply dvd_of_step_dvd hstep
  exact (hitIndex_strictMono hinf).monotone (Nat.le_succ i)

/-- Passing to the successive hitting times preserves strict increase. -/
lemma hitSubsequence_strictMono {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (hitTimes A c).Infinite) (hc : StrictMono c) :
    StrictMono (fun i ↦ c (hitIndex A c i)) :=
  hc.comp (hitIndex_strictMono hinf)

/-- The selected values are precisely the values of `c` at hitting times.
In particular, they all lie in `A`. -/
lemma hitSubsequence_mem {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (hitTimes A c).Infinite) (i : ℕ) :
    c (hitIndex A c i) ∈ A :=
  hitIndex_mem hinf i

/-- Bundled extraction of an increasing divisibility subsequence from an
infinite collection of visits. -/
theorem exists_hit_subsequence {A : Set ℕ} {c : ℕ → ℕ}
    (hinf : (hitTimes A c).Infinite) (hc : StrictMono c)
    (hstep : ∀ i, c i ∣ c (i + 1)) :
    ∃ h : ℕ → ℕ, StrictMono h ∧
      (∀ i, c (h i) ∈ A) ∧
      StrictMono (fun i ↦ c (h i)) ∧
      ∀ i, c (h i) ∣ c (h (i + 1)) := by
  refine ⟨hitIndex A c, hitIndex_strictMono hinf, hitIndex_mem hinf,
    hitSubsequence_strictMono hinf hc, ?_⟩
  exact hitSubsequence_step_dvd hinf hstep

/-! ## Recovering indices in an ambient increasing sequence -/

/-- The unique index in `a` at which the value `d i` occurs. -/
noncomputable def rangeIndex (a d : ℕ → ℕ)
    (hd : ∀ i, d i ∈ Set.range a) (i : ℕ) : ℕ :=
  Classical.choose (hd i)

lemma rangeIndex_spec (a d : ℕ → ℕ) (hd : ∀ i, d i ∈ Set.range a) (i : ℕ) :
    a (rangeIndex a d hd i) = d i :=
  Classical.choose_spec (hd i)

/-- If both the ambient sequence and the selected values are strictly
increasing, their preimage indices are strictly increasing. -/
lemma rangeIndex_strictMono {a d : ℕ → ℕ} (ha : StrictMono a)
    (hd : ∀ i, d i ∈ Set.range a) (hdmono : StrictMono d) :
    StrictMono (rangeIndex a d hd) := by
  intro i j hij
  apply (ha.lt_iff_lt).mp
  rw [rangeIndex_spec a d hd i, rangeIndex_spec a d hd j]
  exact hdmono hij

/-- Reindexing a selected sequence in `range a` recovers it pointwise. -/
lemma comp_rangeIndex (a d : ℕ → ℕ) (hd : ∀ i, d i ∈ Set.range a) :
    a ∘ rangeIndex a d hd = d := by
  funext i
  exact rangeIndex_spec a d hd i

/-- A bundled existence form convenient for the final theorem. -/
theorem exists_strictMono_indices {a d : ℕ → ℕ} (ha : StrictMono a)
    (hd : ∀ i, d i ∈ Set.range a) (hdmono : StrictMono d) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ i, a (n i) = d i := by
  refine ⟨rangeIndex a d hd, rangeIndex_strictMono ha hd hdmono, ?_⟩
  exact rangeIndex_spec a d hd

end Erdos1217
