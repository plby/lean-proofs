/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import Mathlib

/-!
# Scaling symmetry of indexed subset sums

Multiplication by a unit permutes the finite sample space of indexed tuples
and scales every indexed subset sum by that unit.  Over `ZMod p` for prime
`p`, every nonzero scalar is a unit.  Consequently the number (and hence the
uniform probability) of tuples whose nonempty indexed subset sums miss a
given nonzero target is independent of that target.  The same permutation
simultaneously transports joint miss events.
-/

open scoped BigOperators
open Finset

namespace Erdos543.TargetSymmetry

attribute [local instance] Classical.propDecidable

/-- The finite iid tuple space used for indexed subset sums. -/
abbrev Sample (p k : ℕ) := Fin k → ZMod p

/-- Nonempty subsets of the coordinate set. -/
def nonemptyIndexSets (k : ℕ) : Finset (Finset (Fin k)) :=
  (Finset.univ : Finset (Fin k)).powerset.erase ∅

lemma mem_nonemptyIndexSets {k : ℕ} {S : Finset (Fin k)} :
    S ∈ nonemptyIndexSets k ↔ S.Nonempty := by
  simp [nonemptyIndexSets, Finset.nonempty_iff_ne_empty]

/-- The sum over the coordinates indexed by `S`. -/
def indexedSum {p k : ℕ} (a : Sample p k) (S : Finset (Fin k)) : ZMod p :=
  ∑ i ∈ S, a i

/-- The number of nonempty indexed subset sums equal to `x`. -/
def hitCount {p k : ℕ} (a : Sample p k) (x : ZMod p) : ℕ :=
  ((nonemptyIndexSets k).filter fun S ↦ indexedSum a S = x).card

/-- Every nonempty indexed subset sum of `a` misses `x`. -/
def MissesTarget {p k : ℕ} (a : Sample p k) (x : ZMod p) : Prop :=
  ∀ S ∈ nonemptyIndexSets k, indexedSum a S ≠ x

lemma missesTarget_iff_hitCount_eq_zero {p k : ℕ} (a : Sample p k) (x : ZMod p) :
    MissesTarget a x ↔ hitCount a x = 0 := by
  simp [MissesTarget, hitCount, Finset.card_eq_zero]

/-! ## Scaling by a unit -/

/-- Coordinatewise scaling of an iid tuple. -/
def scaleTuple {p k : ℕ} (c : ZMod p) (a : Sample p k) : Sample p k :=
  fun i ↦ c * a i

@[simp]
lemma scaleTuple_apply {p k : ℕ} (c : ZMod p) (a : Sample p k) (i : Fin k) :
    scaleTuple c a i = c * a i := rfl

/-- Scaling commutes with every indexed subset sum. -/
lemma indexedSum_scaleTuple {p k : ℕ} (c : ZMod p) (a : Sample p k)
    (S : Finset (Fin k)) :
    indexedSum (scaleTuple c a) S = c * indexedSum a S := by
  simp [indexedSum, scaleTuple, Finset.mul_sum]

/-- Coordinatewise multiplication by a unit, as a permutation of the sample
space. -/
def scaleEquiv {p k : ℕ} (u : (ZMod p)ˣ) : Sample p k ≃ Sample p k :=
  Equiv.piCongrRight fun _ ↦ u.mulLeft

@[simp]
lemma scaleEquiv_apply {p k : ℕ} (u : (ZMod p)ˣ) (a : Sample p k) :
    scaleEquiv u a = scaleTuple (u : ZMod p) a := by
  rfl

/-- Scaling by a unit transports each exact hit count. -/
lemma hitCount_scale_unit {p k : ℕ} (u : (ZMod p)ˣ)
    (a : Sample p k) (x : ZMod p) :
    hitCount (scaleTuple (u : ZMod p) a) ((u : ZMod p) * x) = hitCount a x := by
  unfold hitCount
  congr 1
  ext S
  simp only [Finset.mem_filter]
  rw [indexedSum_scaleTuple]
  constructor
  · rintro ⟨hS, h⟩
    exact ⟨hS, u.mulLeft.injective h⟩
  · rintro ⟨hS, rfl⟩
    exact ⟨hS, rfl⟩

/-- Scaling by a unit transports the event of missing a target. -/
lemma missesTarget_scale_unit_iff {p k : ℕ} (u : (ZMod p)ˣ)
    (a : Sample p k) (x : ZMod p) :
    MissesTarget (scaleTuple (u : ZMod p) a) ((u : ZMod p) * x) ↔
      MissesTarget a x := by
  rw [missesTarget_iff_hitCount_eq_zero, missesTarget_iff_hitCount_eq_zero,
    hitCount_scale_unit]

/-- The joint miss event for two targets is transported by the same scaling. -/
lemma jointMiss_scale_unit_iff {p k : ℕ} (u : (ZMod p)ˣ)
    (a : Sample p k) (x y : ZMod p) :
    (MissesTarget (scaleTuple (u : ZMod p) a) ((u : ZMod p) * x) ∧
        MissesTarget (scaleTuple (u : ZMod p) a) ((u : ZMod p) * y)) ↔
      (MissesTarget a x ∧ MissesTarget a y) := by
  simp only [missesTarget_scale_unit_iff]

/-! ## Exact finite counts and uniform probabilities -/

/-- Number of iid tuples all of whose nonempty indexed sums miss `x`. -/
noncomputable def missCount (p k : ℕ) [NeZero p] (x : ZMod p) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Sample p k)).filter fun a ↦ MissesTarget a x).card

/-- Number of iid tuples simultaneously missing `x` and `y`. -/
noncomputable def jointMissCount (p k : ℕ) [NeZero p] (x y : ZMod p) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Sample p k)).filter fun a ↦
    MissesTarget a x ∧ MissesTarget a y).card

/-- Exact uniform probability, represented as a rational number. -/
noncomputable def missProbability (p k : ℕ) [NeZero p] (x : ZMod p) : ℚ :=
  (missCount p k x : ℚ) / (Fintype.card (Sample p k) : ℚ)

/-- Exact uniform probability of jointly missing two targets. -/
noncomputable def jointMissProbability (p k : ℕ) [NeZero p]
    (x y : ZMod p) : ℚ :=
  (jointMissCount p k x y : ℚ) / (Fintype.card (Sample p k) : ℚ)

/-- Unit scaling preserves the exact number of tuples missing a target. -/
lemma missCount_scale_unit {p k : ℕ} [NeZero p] (u : (ZMod p)ˣ) (x : ZMod p) :
    missCount p k ((u : ZMod p) * x) = missCount p k x := by
  classical
  unfold missCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  symm
  exact Fintype.card_congr <|
    (scaleEquiv u).subtypeEquiv fun a ↦ by
      simpa using (missesTarget_scale_unit_iff u a x).symm

/-- Unit scaling preserves the exact number of tuples jointly missing two
targets. -/
lemma jointMissCount_scale_unit {p k : ℕ} [NeZero p] (u : (ZMod p)ˣ)
    (x y : ZMod p) :
    jointMissCount p k ((u : ZMod p) * x) ((u : ZMod p) * y) =
      jointMissCount p k x y := by
  classical
  unfold jointMissCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  symm
  exact Fintype.card_congr <|
    (scaleEquiv u).subtypeEquiv fun a ↦ by
      simpa using (jointMiss_scale_unit_iff u a x y).symm

lemma missProbability_scale_unit {p k : ℕ} [NeZero p]
    (u : (ZMod p)ˣ) (x : ZMod p) :
    missProbability p k ((u : ZMod p) * x) = missProbability p k x := by
  simp only [missProbability, missCount_scale_unit]

lemma jointMissProbability_scale_unit {p k : ℕ} [NeZero p]
    (u : (ZMod p)ˣ) (x y : ZMod p) :
    jointMissProbability p k ((u : ZMod p) * x) ((u : ZMod p) * y) =
      jointMissProbability p k x y := by
  simp only [jointMissProbability, jointMissCount_scale_unit]

/-! ## Prime moduli: every nonzero scalar acts -/

/-- At a prime modulus, scaling by any nonzero scalar transports the miss
event. -/
lemma missesTarget_scale_iff {p k : ℕ} (hp : p.Prime) (c : ZMod p) (hc : c ≠ 0)
    (a : Sample p k) (x : ZMod p) :
    MissesTarget (scaleTuple c a) (c * x) ↔ MissesTarget a x := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  simpa using missesTarget_scale_unit_iff (Units.mk0 c hc) a x

/-- At a prime modulus, a nonzero scalar simultaneously transports a joint
miss event. -/
lemma jointMiss_scale_iff {p k : ℕ} (hp : p.Prime) (c : ZMod p) (hc : c ≠ 0)
    (a : Sample p k) (x y : ZMod p) :
    (MissesTarget (scaleTuple c a) (c * x) ∧
        MissesTarget (scaleTuple c a) (c * y)) ↔
      (MissesTarget a x ∧ MissesTarget a y) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  simpa using jointMiss_scale_unit_iff (Units.mk0 c hc) a x y

lemma missCount_scale {p k : ℕ} [NeZero p]
    (hp : p.Prime) (c : ZMod p) (hc : c ≠ 0)
    (x : ZMod p) :
    missCount p k (c * x) = missCount p k x := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa using missCount_scale_unit (Units.mk0 c hc) x

lemma jointMissCount_scale {p k : ℕ} [NeZero p]
    (hp : p.Prime) (c : ZMod p) (hc : c ≠ 0)
    (x y : ZMod p) :
    jointMissCount p k (c * x) (c * y) = jointMissCount p k x y := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa using jointMissCount_scale_unit (Units.mk0 c hc) x y

lemma missProbability_scale {p k : ℕ} [NeZero p]
    (hp : p.Prime) (c : ZMod p) (hc : c ≠ 0)
    (x : ZMod p) :
    missProbability p k (c * x) = missProbability p k x := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa using missProbability_scale_unit (Units.mk0 c hc) x

lemma jointMissProbability_scale {p k : ℕ} [NeZero p] (hp : p.Prime)
    (c : ZMod p) (hc : c ≠ 0) (x y : ZMod p) :
    jointMissProbability p k (c * x) (c * y) = jointMissProbability p k x y := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa using jointMissProbability_scale_unit (Units.mk0 c hc) x y

/-- For a prime modulus, all nonzero targets have exactly the same miss count. -/
theorem missCount_nonzero_target_invariant {p k : ℕ} [NeZero p] (hp : p.Prime)
    {x y : ZMod p} (hx : x ≠ 0) (hy : y ≠ 0) :
    missCount p k x = missCount p k y := by
  letI : Fact p.Prime := ⟨hp⟩
  let c : ZMod p := x * y⁻¹
  have hc : c ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
  have hcy : c * y = x := by simp [c, hy]
  rw [← hcy, missCount_scale hp c hc]

/-- Probability form of `missCount_nonzero_target_invariant`. -/
theorem missProbability_nonzero_target_invariant {p k : ℕ} [NeZero p] (hp : p.Prime)
    {x y : ZMod p} (hx : x ≠ 0) (hy : y ≠ 0) :
    missProbability p k x = missProbability p k y := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [missProbability, missCount_nonzero_target_invariant hp hx hy]

end Erdos543.TargetSymmetry
