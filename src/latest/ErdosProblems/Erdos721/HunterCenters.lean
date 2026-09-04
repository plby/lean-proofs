/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterPhase

/-!
# Finite random families of Hunter centers

This file isolates the product-Haar probability calculation used to choose
the centers in Hunter's construction.  A block of independent torus points
misses a measurable target of volume at least `p` with probability at most
`(1-p)^S`; a finite union bound then supplies one family which hits every
target in every block.
-/

namespace Erdos721.HunterCenters

open Function MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal MeasureTheory Pointwise Topology

open HunterTorus HunterPhase

/-- A family of `S` independent centers in each of `Y` blocks. -/
abbrev CenterFamily (Y S D : ℕ) := Fin Y → Fin S → Torus D

/-- Product torus volume is a probability measure whenever the coordinate
torus volume is normalized. -/
noncomputable def probabilityMeasurePi {ι X : Type*} [Fintype ι]
    [MeasureSpace X]
    [IsProbabilityMeasure (volume : Measure X)] :
    IsProbabilityMeasure (Measure.pi fun _ : ι ↦ (volume : Measure X)) :=
  inferInstance

/-- The event that every center in block `b` misses `F`. -/
def missEvent {Y S D : ℕ} (b : Fin Y) (F : Set (Torus D)) :
    Set (CenterFamily Y S D) :=
  {x | ∀ s, x b s ∉ F}

lemma missEvent_eq {Y S D : ℕ} (b : Fin Y) (F : Set (Torus D)) :
    missEvent b F =
      Function.eval b ⁻¹' Set.pi Set.univ (fun _ : Fin S ↦ Fᶜ) := by
  ext x
  simp [missEvent]

/-- Exact product probability for one block to miss a measurable target. -/
lemma volume_missEvent {Y S D : ℕ} (b : Fin Y) (F : Set (Torus D))
    (hF : MeasurableSet F) :
    volume (missEvent (S := S) b F) = (1 - volume F) ^ S := by
  let : IsProbabilityMeasure (volume : Measure (Torus D)) :=
    HunterTorus.probabilityVolume D
  let : IsProbabilityMeasure
      (volume : Measure (Fin S → Torus D)) := by
    rw [volume_pi]
    exact probabilityMeasurePi
  let : IsProbabilityMeasure
      (volume : Measure (CenterFamily Y S D)) := by
    rw [volume_pi]
    exact probabilityMeasurePi
  rw [missEvent_eq]
  rw [volume_pi]
  rw [(measurePreserving_eval (μ := fun _ : Fin Y ↦
    (volume : Measure (Fin S → Torus D))) b).measure_preimage]
  · rw [volume_pi_pi]
    rw [measure_compl hF (measure_ne_top _ _)]
    simp only [measure_univ, Fin.prod_const]
  · exact (MeasurableSet.univ_pi fun _ ↦ hF.compl).nullMeasurableSet

/-- A target of volume at least `p` is missed by a block with probability at
most `(1-p)^S`. -/
lemma volume_missEvent_le {Y S D : ℕ} (b : Fin Y) (F : Set (Torus D))
    (hF : MeasurableSet F) {p : ℝ≥0∞} (hp : p ≤ volume F) :
    volume (missEvent (S := S) b F) ≤ (1 - p) ^ S := by
  rw [volume_missEvent (S := S) b F hF]
  exact pow_le_pow_left' (tsub_le_tsub_left hp 1) S

/-- The bad event that at least one requested target is missed by at least
one block. -/
def someMissEvent {R : Type*} [Fintype R] {Y S D : ℕ}
    (F : R → Set (Torus D)) : Set (CenterFamily Y S D) :=
  ⋃ r : R, ⋃ b : Fin Y, missEvent b (F r)

/-- Finite product union bound for all requests and all blocks. -/
lemma volume_someMissEvent_le {R : Type*} [Fintype R]
    {Y S D : ℕ} (F : R → Set (Torus D))
    (hF : ∀ r, MeasurableSet (F r)) {p : ℝ≥0∞}
    (hp : ∀ r, p ≤ volume (F r)) :
    volume (someMissEvent (Y := Y) (S := S) F) ≤
      (Fintype.card R * Y : ℕ) * (1 - p) ^ S := by
  classical
  rw [someMissEvent]
  calc
    volume (⋃ r : R, ⋃ b : Fin Y, missEvent b (F r)) ≤
        ∑ r : R, ∑ b : Fin Y, volume (missEvent b (F r)) := by
      calc
        _ ≤ ∑ r : R, volume (⋃ b : Fin Y,
            missEvent (S := S) b (F r)) := measure_iUnion_fintype_le _ _
        _ ≤ ∑ r : R, ∑ b : Fin Y,
            volume (missEvent (S := S) b (F r)) := by
          gcongr with r
          exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _r : R, ∑ _b : Fin Y, (1 - p) ^ S := by
      gcongr with r b
      exact volume_missEvent_le (S := S) b (F r) (hF r) (hp r)
    _ = (Fintype.card R * Y : ℕ) * (1 - p) ^ S := by
      simp only [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul,
        Finset.card_univ, Nat.cast_mul]
      ac_rfl

/-- If the finite union-bound expression is below one, there is a center
family which hits every requested target in every block. -/
theorem exists_centerFamily_hits {R : Type*} [Fintype R]
    {Y S D : ℕ} (F : R → Set (Torus D))
    (hF : ∀ r, MeasurableSet (F r)) {p : ℝ≥0∞}
    (hp : ∀ r, p ≤ volume (F r))
    (hsmall : (Fintype.card R * Y : ℕ) * (1 - p) ^ S < 1) :
    ∃ x : CenterFamily Y S D,
      ∀ r b, ∃ s, x b s ∈ F r := by
  have hbad : volume (someMissEvent (Y := Y) (S := S) F) < 1 :=
    (volume_someMissEvent_le (Y := Y) (S := S) F hF hp).trans_lt hsmall
  have hproper : someMissEvent (Y := Y) (S := S) F ≠ Set.univ := by
    intro h
    rw [h] at hbad
    let : IsProbabilityMeasure (volume : Measure (Torus D)) :=
      HunterTorus.probabilityVolume D
    let : IsProbabilityMeasure
        (volume : Measure (Fin S → Torus D)) := by
      rw [volume_pi]
      exact probabilityMeasurePi
    let : IsProbabilityMeasure
        (volume : Measure (CenterFamily Y S D)) := by
      rw [volume_pi]
      exact probabilityMeasurePi
    simpa using hbad
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
  refine ⟨x, fun r b ↦ ?_⟩
  simp only [mem_compl_iff, someMissEvent, mem_iUnion, not_exists,
    missEvent] at hx
  simpa using not_forall.mp (hx r b)

end Erdos721.HunterCenters
