/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.KeyRestriction

/-!
# Dyadic buckets for the Janzer--Sudakov key restriction

This file formalizes the deterministic bucketing and pigeonhole part of
Janzer--Sudakov's Lemma 4.1.  The probabilistic restriction which follows it
is kept separate.
-/

open Finset Fintype

namespace Erdos182

/-- The least dyadic exponent large enough for `d`, but never below `s + 1`. -/
def dyadicBucket (s d : ℕ) : ℕ :=
  max (s + 1) (Nat.clog 2 d)

theorem le_dyadicBucket (s d : ℕ) : s + 1 ≤ dyadicBucket s d := by
  simp [dyadicBucket]

/-- If `d ≤ 2^t` and `s < t`, then its bucket belongs to `[s+1,t]`. -/
theorem dyadicBucket_le {s t d : ℕ} (hst : s < t) (hd : d ≤ 2 ^ t) :
    dyadicBucket s d ≤ t := by
  simp only [dyadicBucket, max_le_iff]
  exact ⟨hst, Nat.clog_le_of_le_pow hd⟩

/-- The degree is at most the upper endpoint of its dyadic bucket. -/
theorem le_two_pow_dyadicBucket (s d : ℕ) : d ≤ 2 ^ dyadicBucket s d := by
  exact (Nat.le_pow_clog (by omega) d).trans
    (Nat.pow_le_pow_right (by omega) (le_max_right (s + 1) (Nat.clog 2 d)))

/-- The upper endpoint of a bucket is at most its forced bottom endpoint plus twice the degree. -/
theorem two_pow_dyadicBucket_le (s d : ℕ) :
    2 ^ dyadicBucket s d ≤ 2 ^ (s + 1) + 2 * d := by
  by_cases h : Nat.clog 2 d ≤ s + 1
  · rw [dyadicBucket, max_eq_left h]
    omega
  · have hsd : s + 1 ≤ Nat.clog 2 d := Nat.le_of_not_ge h
    rw [dyadicBucket, max_eq_right hsd]
    by_cases hd : d ≤ 1
    · have hc : Nat.clog 2 d = 0 := Nat.clog_of_right_le_one hd 2
      exact (h (hc ▸ Nat.zero_le _)).elim
    · have hd' : 1 < d := Nat.lt_of_not_ge hd
      have hcpos : 0 < Nat.clog 2 d := Nat.clog_pos (by omega) hd'
      have hp : 2 ^ (Nat.clog 2 d).pred < d :=
        Nat.pow_pred_clog_lt_self (by omega) hd'
      calc
        2 ^ Nat.clog 2 d = 2 ^ ((Nat.clog 2 d).pred + 1) := by
          congr 1
          exact (Nat.succ_pred_eq_of_pos hcpos).symm
        _ = 2 ^ (Nat.clog 2 d).pred * 2 := by rw [pow_succ]
        _ ≤ d * 2 := Nat.mul_le_mul_right 2 hp.le
        _ = 2 * d := Nat.mul_comm d 2
        _ ≤ 2 ^ (s + 1) + 2 * d := Nat.le_add_left _ _

section Relation

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The dyadic bucket of the degree of an `A`-vertex. -/
def bucketIndex (R : A → B → Prop) [DecidableRel R] (s : ℕ) (u : A) : ℕ :=
  dyadicBucket s (bipDegreeA R u)

theorem bucketIndex_lower (R : A → B → Prop) [DecidableRel R] (s : ℕ) (u : A) :
    s + 1 ≤ bucketIndex R s u := by
  exact le_dyadicBucket _ _

theorem bucketIndex_upper (R : A → B → Prop) [DecidableRel R]
    {s t : ℕ} (hst : s < t) (hdegree : ∀ u, bipDegreeA R u ≤ 2 ^ t) (u : A) :
    bucketIndex R s u ≤ t := by
  exact dyadicBucket_le hst (hdegree u)

theorem degree_le_two_pow_bucketIndex (R : A → B → Prop) [DecidableRel R]
    (s : ℕ) (u : A) : bipDegreeA R u ≤ 2 ^ bucketIndex R s u := by
  exact le_two_pow_dyadicBucket _ _

theorem two_pow_bucketIndex_le (R : A → B → Prop) [DecidableRel R]
    (s : ℕ) (u : A) :
    2 ^ bucketIndex R s u ≤ 2 ^ (s + 1) + 2 * bipDegreeA R u := by
  exact two_pow_dyadicBucket_le _ _

/-- Sum of bucket indices over the neighbors of a `B`-vertex. -/
def bucketSum (R : A → B → Prop) [DecidableRel R] (s : ℕ) (v : B) : ℕ :=
  ∑ u ∈ bipNeighborsB R v, bucketIndex R s u

theorem bucketSum_lower (R : A → B → Prop) [DecidableRel R]
    (s r : ℕ) (hregular : ∀ v, bipDegreeB R v = r) (v : B) :
    r * (s + 1) ≤ bucketSum R s v := by
  classical
  rw [bucketSum]
  calc
    r * (s + 1) = ∑ _u ∈ bipNeighborsB R v, (s + 1) := by
      simp [← hregular v, bipDegreeB]
    _ ≤ ∑ u ∈ bipNeighborsB R v, bucketIndex R s u :=
      Finset.sum_le_sum fun u _hu ↦ bucketIndex_lower R s u

theorem bucketSum_upper (R : A → B → Prop) [DecidableRel R]
    {s t r : ℕ} (hst : s < t) (hregular : ∀ v, bipDegreeB R v = r)
    (hdegree : ∀ u, bipDegreeA R u ≤ 2 ^ t) (v : B) :
    bucketSum R s v ≤ r * t := by
  classical
  rw [bucketSum]
  calc
    ∑ u ∈ bipNeighborsB R v, bucketIndex R s u ≤
        ∑ _u ∈ bipNeighborsB R v, t :=
      Finset.sum_le_sum fun u _hu ↦ bucketIndex_upper R hst hdegree u
    _ = r * t := by simp [← hregular v, bipDegreeB]

/-- The fiber of `bucketSum` above the value `γ`. -/
def bucketFiber (R : A → B → Prop) [DecidableRel R] (s γ : ℕ) : Finset B :=
  Finset.univ.filter fun v ↦ bucketSum R s v = γ

@[simp] theorem mem_bucketFiber (R : A → B → Prop) [DecidableRel R]
    (s γ : ℕ) (v : B) : v ∈ bucketFiber R s γ ↔ bucketSum R s v = γ := by
  simp [bucketFiber]

private theorem exists_large_fiber
    {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y)
    (hT : T.Nonempty) (hmaps : ∀ x ∈ S, f x ∈ T) :
    ∃ y ∈ T, S.card ≤ T.card * (S.filter fun x ↦ f x = y).card := by
  by_contra! h
  have hs :
      ∑ y ∈ T, T.card * (S.filter fun x ↦ f x = y).card <
        ∑ _y ∈ T, S.card := by
    refine Finset.sum_lt_sum (fun y hy ↦ (h y hy).le) ?_
    exact ⟨hT.choose, hT.choose_spec, h hT.choose hT.choose_spec⟩
  have hsum : ∑ y ∈ T, (S.filter fun x ↦ f x = y).card = S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter,
      Finset.filter_eq_self.mpr hmaps]
  simp only [← Finset.mul_sum, hsum, Finset.sum_const, nsmul_eq_mul] at hs
  exact (Nat.lt_irrefl _ hs)

/-- Pigeonholing the bucket sums.  All selected vertices have the same sum `γ`,
the sum has its expected lower bound, and at least a `1/(r(t-s))` fraction of
the `B`-part is selected. -/
theorem exists_large_bucketFiber (R : A → B → Prop) [DecidableRel R]
    {s t r : ℕ} (hr : 0 < r) (hst : s < t)
    (hregular : ∀ v, bipDegreeB R v = r)
    (hdegree : ∀ u, bipDegreeA R u ≤ 2 ^ t) :
    ∃ γ : ℕ,
      r * (s + 1) ≤ γ ∧ γ ≤ r * t ∧
      Fintype.card B ≤ r * (t - s) * (bucketFiber R s γ).card ∧
      ∀ v ∈ bucketFiber R s γ, bucketSum R s v = γ := by
  classical
  let T : Finset ℕ := Finset.Icc (r * (s + 1)) (r * t)
  have hT : T.Nonempty := by
    refine Finset.nonempty_Icc.mpr ?_
    exact Nat.mul_le_mul_left r hst
  have hmaps : ∀ v ∈ (Finset.univ : Finset B), bucketSum R s v ∈ T := by
    intro v hv
    exact Finset.mem_Icc.mpr
      ⟨bucketSum_lower R s r hregular v, bucketSum_upper R hst hregular hdegree v⟩
  obtain ⟨γ, hγT, hlarge⟩ :=
    exists_large_fiber (Finset.univ : Finset B) T (bucketSum R s) hT hmaps
  refine ⟨γ, (Finset.mem_Icc.mp hγT).1, (Finset.mem_Icc.mp hγT).2, ?_, ?_⟩
  · have hcardT : T.card ≤ r * (t - s) := by
      have ht : t = s + (t - s) := by omega
      have hupper : r * t = r * s + r * (t - s) := by
        calc
          r * t = r * (s + (t - s)) := congrArg (r * ·) ht
          _ = r * s + r * (t - s) := Nat.mul_add r s (t - s)
      change (Finset.Icc (r * (s + 1)) (r * t)).card ≤ r * (t - s)
      rw [Nat.card_Icc, hupper, Nat.mul_succ]
      omega
    calc
      Fintype.card B = (Finset.univ : Finset B).card := by simp
      _ ≤ T.card * ((Finset.univ : Finset B).filter fun v ↦ bucketSum R s v = γ).card :=
        hlarge
      _ ≤ (r * (t - s)) * (bucketFiber R s γ).card := by
        simpa [bucketFiber] using
          Nat.mul_le_mul_right (bucketFiber R s γ).card hcardT
  · intro v hv
    exact (mem_bucketFiber R s γ v).mp hv

end Relation

end Erdos182
