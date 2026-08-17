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
# Deterministic pruning after the Janzer--Sudakov sampling step

This file contains no probability theory.  Starting from a sampled left set
`S` and a selected right set `T`, it removes the left vertices whose degree
into `T` is above a cutoff, and then removes every right vertex which sees
one of those bad left vertices.  The main counting lemma is the literal
inequality used in JS Lemma 4.1: if every right vertex has degree `r`, then
the surviving edge count is at least `X - r * Y`, where `X` is the edge
count before pruning and `Y` is the number of edges at bad left vertices.

The last two lemmas convert the positive real-valued score used in the
probabilistic argument into the division-free natural-number inequalities
of `IsKeyRestriction`.
-/

open Finset Fintype

namespace Erdos182

section Pruning

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Sampled left vertices whose degree into `T` is strictly above `cutoff`. -/
def pruningBadA (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) : Finset A :=
  S.filter fun u ↦ cutoff < bipRestrictedDegreeA R T u

/-- The left set after deleting all bad sampled vertices. -/
def pruningSurvivingA (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) : Finset A :=
  S \ pruningBadA R S T cutoff

/-- The right set after deleting every vertex which touches a bad left
vertex. -/
def pruningSurvivingB (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) : Finset B :=
  T.filter fun v ↦ ∀ u ∈ pruningBadA R S T cutoff, ¬ R u v

/-- The number `Y` of incidences whose left endpoint is bad. -/
def pruningBadEdgeCount (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) : ℕ :=
  bipRestrictedEdgeCount R (pruningBadA R S T cutoff) T

@[simp] theorem mem_pruningBadA {R : A → B → Prop} [DecidableRel R]
    {S : Finset A} {T : Finset B} {cutoff : ℕ} {u : A} :
    u ∈ pruningBadA R S T cutoff ↔
      u ∈ S ∧ cutoff < bipRestrictedDegreeA R T u := by
  simp [pruningBadA]

@[simp] theorem mem_pruningSurvivingA {R : A → B → Prop} [DecidableRel R]
    {S : Finset A} {T : Finset B} {cutoff : ℕ} {u : A} :
    u ∈ pruningSurvivingA R S T cutoff ↔
      u ∈ S ∧ bipRestrictedDegreeA R T u ≤ cutoff := by
  simp only [pruningSurvivingA, mem_sdiff, mem_pruningBadA]
  constructor
  · rintro ⟨huS, hubad⟩
    exact ⟨huS, Nat.le_of_not_gt fun hdegree ↦ hubad ⟨huS, hdegree⟩⟩
  · rintro ⟨huS, hdegree⟩
    exact ⟨huS, fun hubad ↦ Nat.not_lt_of_ge hdegree hubad.2⟩

@[simp] theorem mem_pruningSurvivingB {R : A → B → Prop} [DecidableRel R]
    {S : Finset A} {T : Finset B} {cutoff : ℕ} {v : B} :
    v ∈ pruningSurvivingB R S T cutoff ↔
      v ∈ T ∧ ∀ u ∈ pruningBadA R S T cutoff, ¬ R u v := by
  simp [pruningSurvivingB]

theorem pruningBadA_subset (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) :
    pruningBadA R S T cutoff ⊆ S := by
  intro u hu
  exact (mem_pruningBadA.mp hu).1

theorem pruningSurvivingA_subset (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) :
    pruningSurvivingA R S T cutoff ⊆ S := by
  intro u hu
  exact (mem_pruningSurvivingA.mp hu).1

theorem pruningSurvivingB_subset (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) :
    pruningSurvivingB R S T cutoff ⊆ T := by
  intro v hv
  exact (mem_pruningSurvivingB.mp hv).1

/-- Every surviving right vertex has all its neighbours in the surviving
left set, provided the unpruned right set was already closed inside `S`. -/
theorem pruning_closed
    (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ)
    (hclosed : ∀ v ∈ T, ∀ u, R u v → u ∈ S) :
    ∀ v : ↑(pruningSurvivingB R S T cutoff), ∀ u,
      R u v → u ∈ pruningSurvivingA R S T cutoff := by
  rintro ⟨v, hv⟩ u huv
  have hv' := mem_pruningSurvivingB.mp hv
  refine mem_pruningSurvivingA.mpr ⟨hclosed v hv'.1 u huv, ?_⟩
  by_contra hdegree
  have hubad : u ∈ pruningBadA R S T cutoff :=
    mem_pruningBadA.mpr ⟨hclosed v hv'.1 u huv, Nat.lt_of_not_ge hdegree⟩
  exact hv'.2 u hubad huv

/-- Pruning enforces the cutoff on every surviving left vertex. -/
theorem pruning_max_degree
    (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) :
    ∀ u ∈ pruningSurvivingA R S T cutoff,
      bipRestrictedDegreeA R (pruningSurvivingB R S T cutoff) u ≤ cutoff := by
  intro u hu
  have hdegreeT : bipRestrictedDegreeA R T u ≤ cutoff :=
    (mem_pruningSurvivingA.mp hu).2
  exact (Finset.card_le_card (by
    intro v hv
    have hvT : v ∈ T := (mem_pruningSurvivingB.mp (mem_filter.mp hv).1).1
    exact mem_filter.mpr ⟨hvT, (mem_filter.mp hv).2⟩)).trans hdegreeT

/-- Double-count a restricted relation by its right part. -/
theorem bipRestrictedEdgeCount_eq_sum_right
    (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) :
    bipRestrictedEdgeCount R S T =
      ∑ v ∈ T, (S.filter fun u ↦ R u v).card := by
  classical
  simp only [bipRestrictedEdgeCount, Finset.card_filter]
  rw [Finset.sum_comm]

/-- If all selected right vertices have restricted degree `r`, the selected
edge count is `r * |T|`. -/
theorem bipRestrictedEdgeCount_eq_mul_card
    (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (r : ℕ)
    (hregular : ∀ v ∈ T, (S.filter fun u ↦ R u v).card = r) :
    bipRestrictedEdgeCount R S T = r * T.card := by
  rw [bipRestrictedEdgeCount_eq_sum_right]
  calc
    ∑ v ∈ T, (S.filter fun u ↦ R u v).card = ∑ _v ∈ T, r :=
      sum_congr rfl fun v hv ↦ hregular v hv
    _ = r * T.card := by simp [mul_comm]

/-- A surviving right vertex retains exactly the same neighbours as before
pruning: it has no bad neighbour, while every old neighbour lies in `S`. -/
theorem filter_survivingA_eq_filter_of_mem_survivingB
    (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ)
    (hclosed : ∀ v ∈ T, ∀ u, R u v → u ∈ S)
    {v : B} (hv : v ∈ pruningSurvivingB R S T cutoff) :
    (pruningSurvivingA R S T cutoff).filter (fun u ↦ R u v) =
      S.filter fun u ↦ R u v := by
  ext u
  constructor
  · intro hu
    have hu' := mem_filter.mp hu
    exact mem_filter.mpr ⟨(pruningSurvivingA_subset R S T cutoff hu'.1), hu'.2⟩
  · intro hu
    have hu' := mem_filter.mp hu
    have hv' := mem_pruningSurvivingB.mp hv
    have hunotbad : u ∉ pruningBadA R S T cutoff := by
      intro hubad
      exact hv'.2 u hubad hu'.2
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hu'.1, hunotbad⟩, hu'.2⟩

/-- The number of deleted right vertices is at most the number of incidences
at bad left vertices.  Each deleted right vertex chooses at least one such
incidence; overlaps only improve the bound. -/
theorem card_removedB_le_badEdgeCount
    (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff : ℕ) :
    (T \ pruningSurvivingB R S T cutoff).card ≤
      pruningBadEdgeCount R S T cutoff := by
  classical
  let bad := pruningBadA R S T cutoff
  let U : Finset B := bad.biUnion fun u ↦ T.filter (R u)
  have hsubset : T \ pruningSurvivingB R S T cutoff ⊆ U := by
    intro v hv
    have hvT : v ∈ T := (mem_sdiff.mp hv).1
    have hvnot : v ∉ pruningSurvivingB R S T cutoff := (mem_sdiff.mp hv).2
    have hex : ∃ u ∈ bad, R u v := by
      by_contra h
      push_neg at h
      apply hvnot
      exact mem_pruningSurvivingB.mpr ⟨hvT, h⟩
    obtain ⟨u, hubad, huv⟩ := hex
    exact mem_biUnion.mpr ⟨u, hubad, mem_filter.mpr ⟨hvT, huv⟩⟩
  calc
    (T \ pruningSurvivingB R S T cutoff).card ≤ U.card := card_le_card hsubset
    _ ≤ ∑ u ∈ bad, (T.filter (R u)).card := card_biUnion_le
    _ = pruningBadEdgeCount R S T cutoff := by
      simp [bad, pruningBadEdgeCount, bipRestrictedEdgeCount]

/-- The exact deterministic `X - rY` estimate from JS Lemma 4.1. -/
theorem pruning_edgeCount_sub_le
    (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff r : ℕ)
    (hclosed : ∀ v ∈ T, ∀ u, R u v → u ∈ S)
    (hregular : ∀ v ∈ T, (S.filter fun u ↦ R u v).card = r) :
    bipRestrictedEdgeCount R S T - r * pruningBadEdgeCount R S T cutoff ≤
      bipRestrictedEdgeCount R (pruningSurvivingA R S T cutoff)
        (pruningSurvivingB R S T cutoff) := by
  let A' := pruningSurvivingA R S T cutoff
  let B' := pruningSurvivingB R S T cutoff
  have hBsub : B' ⊆ T := pruningSurvivingB_subset R S T cutoff
  have hregular' : ∀ v ∈ B', (A'.filter fun u ↦ R u v).card = r := by
    intro v hv
    rw [filter_survivingA_eq_filter_of_mem_survivingB R S T cutoff hclosed hv]
    exact hregular v (hBsub hv)
  have horiginal : bipRestrictedEdgeCount R S T = r * T.card :=
    bipRestrictedEdgeCount_eq_mul_card R S T r hregular
  have hsurviving : bipRestrictedEdgeCount R A' B' = r * B'.card :=
    bipRestrictedEdgeCount_eq_mul_card R A' B' r hregular'
  have hremoved : (T \ B').card ≤ pruningBadEdgeCount R S T cutoff :=
    card_removedB_le_badEdgeCount R S T cutoff
  have hmul := Nat.mul_le_mul_left r hremoved
  have hcard : (T \ B').card + B'.card = T.card :=
    card_sdiff_add_card_eq_card hBsub
  rw [horiginal, hsurviving]
  calc
    r * T.card - r * pruningBadEdgeCount R S T cutoff ≤
        r * T.card - r * (T \ B').card :=
      Nat.sub_le_sub_left hmul _
    _ = r * B'.card := by
      rw [← hcard, Nat.mul_add]
      omega

/-- Additive form of `pruning_edgeCount_sub_le`, often more convenient for
natural-number algebra. -/
theorem pruning_edgeCount_le_add
    (R : A → B → Prop) [DecidableRel R]
    (S : Finset A) (T : Finset B) (cutoff r : ℕ)
    (hclosed : ∀ v ∈ T, ∀ u, R u v → u ∈ S)
    (hregular : ∀ v ∈ T, (S.filter fun u ↦ R u v).card = r) :
    bipRestrictedEdgeCount R S T ≤
      bipRestrictedEdgeCount R (pruningSurvivingA R S T cutoff)
          (pruningSurvivingB R S T cutoff) +
        r * pruningBadEdgeCount R S T cutoff := by
  have h := pruning_edgeCount_sub_le R S T cutoff r hclosed hregular
  omega

end Pruning

section Score

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A positive score `e - c|A'|` with
`c = Q / (10 x r)` gives the first, density, inequality in
`IsKeyRestriction`. -/
theorem keyRestriction_density_of_positive_score
    {R : A → B → Prop} [DecidableRel R]
    {x r Q : ℕ} {A' : Finset A} {B' : Finset B} {c : ℝ}
    (hx : 0 < x) (hr : 0 < r)
    (hc : c = (Q : ℝ) / (10 * (x : ℝ) * (r : ℝ)))
    (hscore : 0 < (bipRestrictedEdgeCount R A' B' : ℝ) - c * A'.card) :
    Q * A'.card ≤ 10 * x * r * bipRestrictedEdgeCount R A' B' := by
  have hden : 0 < 10 * (x : ℝ) * (r : ℝ) := by positivity
  have hc_mul : (10 * (x : ℝ) * (r : ℝ)) * c = Q := by
    rw [hc]
    field_simp
  have hscore' : c * (A'.card : ℝ) < bipRestrictedEdgeCount R A' B' := by
    linarith
  have hlt :
      (Q : ℝ) * (A'.card : ℝ) <
        (10 * (x : ℝ) * (r : ℝ)) *
          (bipRestrictedEdgeCount R A' B' : ℝ) := by
    calc
      (Q : ℝ) * (A'.card : ℝ) =
          (10 * (x : ℝ) * (r : ℝ)) * (c * A'.card) := by
            rw [← hc_mul]
            ring
      _ < (10 * (x : ℝ) * (r : ℝ)) *
          (bipRestrictedEdgeCount R A' B' : ℝ) :=
        mul_lt_mul_of_pos_left hscore' hden
  exact_mod_cast hlt.le

/-- The same positive score converts a pointwise real degree estimate into
the second, maximum-degree, inequality in `IsKeyRestriction`. -/
theorem keyRestriction_maxDegree_of_positive_score
    {R : A → B → Prop} [DecidableRel R]
    {x r : ℕ} {A' : Finset A} {B' : Finset B} {c : ℝ}
    (hx : 0 < x) (hr : 0 < r)
    (hscore : 0 < (bipRestrictedEdgeCount R A' B' : ℝ) - c * A'.card)
    (hdegree : ∀ u ∈ A',
      (bipRestrictedDegreeA R B' u : ℝ) ≤
        40 * (x : ℝ) * (r : ℝ) ^ 2 * c) :
    ∀ u ∈ A',
      bipRestrictedDegreeA R B' u * A'.card ≤
        40 * x * r ^ 2 * bipRestrictedEdgeCount R A' B' := by
  intro u hu
  have hcoeff : 0 < 40 * (x : ℝ) * (r : ℝ) ^ 2 := by positivity
  have hscore' : c * (A'.card : ℝ) < bipRestrictedEdgeCount R A' B' := by
    linarith
  have hlt :
      (bipRestrictedDegreeA R B' u : ℝ) * (A'.card : ℝ) <
        (40 * (x : ℝ) * (r : ℝ) ^ 2) *
          (bipRestrictedEdgeCount R A' B' : ℝ) := by
    calc
      (bipRestrictedDegreeA R B' u : ℝ) * (A'.card : ℝ) ≤
          (40 * (x : ℝ) * (r : ℝ) ^ 2 * c) * A'.card :=
        mul_le_mul_of_nonneg_right (hdegree u hu) (Nat.cast_nonneg _)
      _ = (40 * (x : ℝ) * (r : ℝ) ^ 2) * (c * A'.card) := by ring
      _ < (40 * (x : ℝ) * (r : ℝ) ^ 2) *
          (bipRestrictedEdgeCount R A' B' : ℝ) :=
        mul_lt_mul_of_pos_left hscore' hcoeff
  exact_mod_cast hlt.le

/-- Package the two score conversions, closure, and nonemptiness into the
exact conclusion expected by the key-restriction interface. -/
theorem isKeyRestriction_of_positive_score
    {R : A → B → Prop} [DecidableRel R]
    {x r Q : ℕ} {A' : Finset A} {B' : Finset B} {c : ℝ}
    (hx : 0 < x) (hr : 0 < r)
    (hc : c = (Q : ℝ) / (10 * (x : ℝ) * (r : ℝ)))
    (hscore : 0 < (bipRestrictedEdgeCount R A' B' : ℝ) - c * A'.card)
    (hclosed : ∀ v : ↑B', ∀ u, R u v → u ∈ A')
    (hdegree : ∀ u ∈ A',
      (bipRestrictedDegreeA R B' u : ℝ) ≤
        40 * (x : ℝ) * (r : ℝ) ^ 2 * c) :
    IsKeyRestriction R r x Q A' B' := by
  have hnonempty : A'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hA
    subst A'
    simpa [bipRestrictedEdgeCount] using hscore
  exact ⟨hnonempty, hclosed,
    keyRestriction_density_of_positive_score hx hr hc hscore,
    keyRestriction_maxDegree_of_positive_score hx hr hscore hdegree⟩

/-- End-to-end deterministic pruning interface.  A positive score for the
actual surviving edge count, together with a cutoff dominated by
`40 x r² c`, yields `IsKeyRestriction`. -/
theorem isKeyRestriction_pruning_of_positive_score
    {R : A → B → Prop} [DecidableRel R]
    {x r Q cutoff : ℕ} {S : Finset A} {T : Finset B} {c : ℝ}
    (hx : 0 < x) (hr : 0 < r)
    (hclosed : ∀ v ∈ T, ∀ u, R u v → u ∈ S)
    (hc : c = (Q : ℝ) / (10 * (x : ℝ) * (r : ℝ)))
    (hscore : 0 <
      (bipRestrictedEdgeCount R (pruningSurvivingA R S T cutoff)
          (pruningSurvivingB R S T cutoff) : ℝ) -
        c * (pruningSurvivingA R S T cutoff).card)
    (hcutoff : (cutoff : ℝ) ≤
      40 * (x : ℝ) * (r : ℝ) ^ 2 * c) :
    IsKeyRestriction R r x Q (pruningSurvivingA R S T cutoff)
      (pruningSurvivingB R S T cutoff) := by
  apply isKeyRestriction_of_positive_score hx hr hc hscore
  · exact pruning_closed R S T cutoff hclosed
  · intro u hu
    have hdegreeR :
        (bipRestrictedDegreeA R (pruningSurvivingB R S T cutoff) u : ℝ) ≤
          cutoff := by
      exact_mod_cast pruning_max_degree R S T cutoff u hu
    exact hdegreeR.trans hcutoff

/-- Version matching the probabilistic score verbatim.  The expectation
calculation subtracts `c * |S|`, where `S` is the sampled set before bad
vertices are removed.  Since the surviving left set is a subset of `S` and
`c > 0`, this is stronger than the score required by
`isKeyRestriction_pruning_of_positive_score`. -/
theorem isKeyRestriction_pruning_of_sampled_score
    {R : A → B → Prop} [DecidableRel R]
    {x r Q cutoff : ℕ} {S : Finset A} {T : Finset B} {c : ℝ}
    (hx : 0 < x) (hr : 0 < r)
    (hclosed : ∀ v ∈ T, ∀ u, R u v → u ∈ S)
    (hc : c = (Q : ℝ) / (10 * (x : ℝ) * (r : ℝ)))
    (hcpos : 0 < c)
    (hscore : 0 <
      (bipRestrictedEdgeCount R (pruningSurvivingA R S T cutoff)
          (pruningSurvivingB R S T cutoff) : ℝ) - c * S.card)
    (hcutoff : (cutoff : ℝ) ≤
      40 * (x : ℝ) * (r : ℝ) ^ 2 * c) :
    IsKeyRestriction R r x Q (pruningSurvivingA R S T cutoff)
      (pruningSurvivingB R S T cutoff) := by
  have hcard : (pruningSurvivingA R S T cutoff).card ≤ S.card :=
    card_le_card (pruningSurvivingA_subset R S T cutoff)
  have hcardR :
      c * ((pruningSurvivingA R S T cutoff).card : ℝ) ≤ c * (S.card : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hcpos.le
  have hsurvivingScore : 0 <
      (bipRestrictedEdgeCount R (pruningSurvivingA R S T cutoff)
          (pruningSurvivingB R S T cutoff) : ℝ) -
        c * (pruningSurvivingA R S T cutoff).card := by
    linarith
  exact isKeyRestriction_pruning_of_positive_score hx hr hclosed hc
    hsurvivingScore hcutoff

end Score

end Erdos182
