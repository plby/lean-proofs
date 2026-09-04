/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterColoring
import Mathlib.Probability.Distributions.Uniform

/-!
# Random labels for Hunter's radial shells

Each block supplies one candidate center for every requested arithmetic
progression.  Label every center independently and uniformly by a shell
index.  A fixed request is missed with probability `(1 - 1 / K)^Y`; a
finite union bound therefore produces one deterministic labeling which
serves all requests simultaneously.
-/

namespace Erdos721.HunterShellLabeling

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory BigOperators

open HunterColoring

/-- The uniform probability measure on the `K` shell labels. -/
noncomputable def uniformFinMeasure (K : ℕ) [NeZero K] :
    Measure (Fin K) :=
  (PMF.uniformOfFintype (Fin K)).toMeasure

noncomputable instance uniformFinMeasure_isProbabilityMeasure
    (K : ℕ) [NeZero K] : IsProbabilityMeasure (uniformFinMeasure K) := by
  unfold uniformFinMeasure
  infer_instance

/-- Independent uniform labels within one center block. -/
noncomputable def rowMeasure (S K : ℕ) [NeZero K] :
    Measure (Fin S → Fin K) :=
  Measure.pi fun _ : Fin S ↦ uniformFinMeasure K

noncomputable instance rowMeasure_isProbabilityMeasure
    (S K : ℕ) [NeZero K] : IsProbabilityMeasure (rowMeasure S K) := by
  unfold rowMeasure
  infer_instance

/-- Independent uniform labels in all blocks. -/
noncomputable def labelingMeasure (Y S K : ℕ) [NeZero K] :
    Measure (ShellLabeling Y S K) :=
  Measure.pi fun _ : Fin Y ↦ rowMeasure S K

noncomputable instance labelingMeasure_isProbabilityMeasure
    (Y S K : ℕ) [NeZero K] :
    IsProbabilityMeasure (labelingMeasure Y S K) := by
  unfold labelingMeasure
  infer_instance

lemma uniformFinMeasure_singleton {K : ℕ} [NeZero K] (k : Fin K) :
    uniformFinMeasure K ({k} : Set (Fin K)) = (K : ℝ≥0∞)⁻¹ := by
  unfold uniformFinMeasure
  rw [PMF.toMeasure_uniformOfFintype_apply _ MeasurableSet.of_discrete]
  simp

lemma uniformFinMeasure_compl_singleton {K : ℕ} [NeZero K] (k : Fin K) :
    uniformFinMeasure K ({k} : Set (Fin K))ᶜ =
      1 - (K : ℝ≥0∞)⁻¹ := by
  rw [measure_compl (MeasurableSet.singleton k) (measure_ne_top _ _),
    measure_univ, uniformFinMeasure_singleton]

/-- Rows whose distinguished center receives the wrong shell label. -/
def rowMissSet {S K : ℕ} (s : Fin S) (k : Fin K) :
    Set (Fin S → Fin K) :=
  {label | label s ≠ k}

lemma rowMissSet_eq_pi {S K : ℕ} (s : Fin S) (k : Fin K) :
    rowMissSet s k = Set.pi Set.univ
      (fun t : Fin S ↦ if t = s then ({k} : Set (Fin K))ᶜ else Set.univ) := by
  ext label
  constructor
  · intro h t _ht
    change label s ≠ k at h
    by_cases hts : t = s
    · subst t
      simpa using h
    · simp [hts]
  · intro h
    have hs := h s (Set.mem_univ s)
    change label s ≠ k
    simpa using hs

lemma rowMeasure_rowMissSet {S K : ℕ} [NeZero K]
    (s : Fin S) (k : Fin K) :
    rowMeasure S K (rowMissSet s k) = 1 - (K : ℝ≥0∞)⁻¹ := by
  rw [rowMissSet_eq_pi, rowMeasure, Measure.pi_pi]
  classical
  rw [Finset.prod_eq_single s]
  · simpa using uniformFinMeasure_compl_singleton k
  · intro t _ht hts
    simp [hts]
  · simp

/-- A complete labeling misses a request if all block candidates receive the
wrong shell label. -/
def labelMissEvent {R : Type*} {Y S K : ℕ}
    (chosen : R → Fin Y → Fin S) (wanted : R → Fin Y → Fin K)
    (r : R) : Set (ShellLabeling Y S K) :=
  {label | ∀ b, label b (chosen r b) ≠ wanted r b}

lemma labelMissEvent_eq_pi {R : Type*} {Y S K : ℕ}
    (chosen : R → Fin Y → Fin S) (wanted : R → Fin Y → Fin K)
    (r : R) :
    labelMissEvent chosen wanted r = Set.pi Set.univ
      (fun b : Fin Y ↦ rowMissSet (chosen r b) (wanted r b)) := by
  ext label
  simp [labelMissEvent, rowMissSet]

lemma labelingMeasure_labelMissEvent
    {R : Type*} {Y S K : ℕ} [NeZero K]
    (chosen : R → Fin Y → Fin S) (wanted : R → Fin Y → Fin K)
    (r : R) :
    labelingMeasure Y S K (labelMissEvent chosen wanted r) =
      (1 - (K : ℝ≥0∞)⁻¹) ^ Y := by
  rw [labelMissEvent_eq_pi, labelingMeasure, Measure.pi_pi]
  simp [rowMeasure_rowMissSet]

/-- Union of all requests missed by a labeling. -/
def someLabelMissEvent {R : Type*} {Y S K : ℕ}
    (chosen : R → Fin Y → Fin S) (wanted : R → Fin Y → Fin K) :
    Set (ShellLabeling Y S K) :=
  ⋃ r : R, labelMissEvent chosen wanted r

lemma labelingMeasure_someLabelMissEvent_le
    {R : Type*} [Fintype R] {Y S K : ℕ} [NeZero K]
    (chosen : R → Fin Y → Fin S) (wanted : R → Fin Y → Fin K) :
    labelingMeasure Y S K (someLabelMissEvent chosen wanted) ≤
      (Fintype.card R : ℕ) * (1 - (K : ℝ≥0∞)⁻¹) ^ Y := by
  rw [someLabelMissEvent]
  calc
    labelingMeasure Y S K
        (⋃ r : R, labelMissEvent chosen wanted r) ≤
        ∑ r : R, labelingMeasure Y S K
          (labelMissEvent chosen wanted r) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ _r : R, (1 - (K : ℝ≥0∞)⁻¹) ^ Y := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact labelingMeasure_labelMissEvent chosen wanted r
    _ = (Fintype.card R : ℕ) *
        (1 - (K : ℝ≥0∞)⁻¹) ^ Y := by simp

/-- If the finite union-bound expression is below one, a single shell
labeling matches at least one block candidate for every request. -/
theorem exists_shellLabeling
    {R : Type*} [Fintype R] {Y S K : ℕ} (hK : 0 < K)
    (chosen : R → Fin Y → Fin S) (wanted : R → Fin Y → Fin K)
    (hsmall : (Fintype.card R : ℕ) *
      (1 - (K : ℝ≥0∞)⁻¹) ^ Y < 1) :
    ∃ label : ShellLabeling Y S K,
      ∀ r : R, ∃ b : Fin Y,
        label b (chosen r b) = wanted r b := by
  let : NeZero K := ⟨hK.ne'⟩
  have hbad : labelingMeasure Y S K
      (someLabelMissEvent chosen wanted) < 1 :=
    (labelingMeasure_someLabelMissEvent_le chosen wanted).trans_lt hsmall
  have hproper : someLabelMissEvent chosen wanted ≠ Set.univ := by
    intro heq
    rw [heq] at hbad
    simpa using hbad
  obtain ⟨label, hlabel⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
  refine ⟨label, fun r ↦ ?_⟩
  have hr : ¬∀ b, label b (chosen r b) ≠ wanted r b := by
    intro hmiss
    exact hlabel (Set.mem_iUnion_of_mem r hmiss)
  simpa only [not_forall, not_ne_iff] using hr

end Erdos721.HunterShellLabeling
