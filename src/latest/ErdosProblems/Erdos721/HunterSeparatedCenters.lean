/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterDistributedCenters
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Phase-distributed and affinely separated Hunter centers

The same product-Haar sample used for phase distribution is also required to
avoid every nontrivial approximate relation `xᵢ - 2xⱼ + xₗ ≈ 0`.  Each fixed
relation is Haar-uniform; a second finite union bound therefore gives both
properties simultaneously.
-/

namespace Erdos721.HunterSeparatedCenters

open Function MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal MeasureTheory Pointwise Topology

open HunterTorus HunterCenters HunterDistributedCenters HunterLattice HunterPhaseNet

/-- A center coordinate indexed by its block and position. -/
def centerAt {Y S D : ℕ} (x : CenterFamily Y S D)
    (p : Fin Y × Fin S) : Torus D := x p.1 p.2

/-- The affine combination relevant to a three-term progression. -/
def affineCombo {Y S D : ℕ} (a b c : Fin Y × Fin S) :
    CenterFamily Y S D →+ Torus D where
  toFun x := centerAt x a - 2 • centerAt x b + centerAt x c
  map_zero' := by simp [centerAt]
  map_add' x y := by
    simp only [centerAt, Pi.add_apply, zsmul_add]
    abel

lemma continuous_affineCombo {Y S D : ℕ} (a b c : Fin Y × Fin S) :
    Continuous (affineCombo (D := D) a b c) := by
  change Continuous (fun x : CenterFamily Y S D ↦
    x a.1 a.2 - 2 • x b.1 b.2 + x c.1 c.2)
  fun_prop

/-- A function family supported at one center coordinate. -/
def singletonCenter {Y S D : ℕ} (p : Fin Y × Fin S) (y : Torus D) :
    CenterFamily Y S D :=
  fun b s ↦ if (b, s) = p then y else 0

@[simp] lemma centerAt_singleton_self {Y S D : ℕ}
    (p : Fin Y × Fin S) (y : Torus D) :
    centerAt (singletonCenter p y) p = y := by
  simp [centerAt, singletonCenter]

lemma centerAt_singleton_of_ne {Y S D : ℕ}
    {p q : Fin Y × Fin S} (h : q ≠ p) (y : Torus D) :
    centerAt (singletonCenter p y) q = 0 := by
  simp [centerAt, singletonCenter, h]

/-- Coordinatewise half of a torus point. -/
noncomputable def torusHalf {D : ℕ} (y : Torus D) : Torus D :=
  fun i ↦ (((centeredCoord (y i) / 2 : ℝ)) : AddCircle (1 : ℝ))

@[simp] lemma two_nsmul_torusHalf {D : ℕ} (y : Torus D) :
    2 • torusHalf y = y := by
  funext i
  rw [← AddCircle.coe_equivIco (p := (1 : ℝ))
    (a := -(1 / 2 : ℝ)) (y := y i)]
  change 2 • (((centeredCoord (y i) / 2 : ℝ)) : AddCircle (1 : ℝ)) =
    ((centeredCoord (y i) : ℝ) : AddCircle (1 : ℝ))
  rw [two_nsmul]
  change (((centeredCoord (y i) / 2 + centeredCoord (y i) / 2 : ℝ)) :
      AddCircle (1 : ℝ)) = _
  congr 1
  ring

/-- Every nonconstant affine-combination map is surjective. -/
lemma affineCombo_surjective {Y S D : ℕ} (a b c : Fin Y × Fin S)
    (h : ¬ (a = b ∧ b = c)) :
    Surjective (affineCombo (D := D) a b c) := by
  classical
  intro y
  by_cases hab : a = b
  · subst b
    have hac : c ≠ a := by
      intro hca
      apply h
      exact ⟨rfl, hca.symm⟩
    refine ⟨singletonCenter c y, ?_⟩
    rw [show affineCombo a a c (singletonCenter c y) =
        centerAt (singletonCenter c y) a -
          2 • centerAt (singletonCenter c y) a +
          centerAt (singletonCenter c y) c by rfl,
      centerAt_singleton_of_ne hac.symm, centerAt_singleton_self]
    simp
  · by_cases hac : a = c
    · subst c
      refine ⟨singletonCenter a (torusHalf y), ?_⟩
      have hba : b ≠ a := fun hba ↦ hab hba.symm
      rw [show affineCombo a b a (singletonCenter a (torusHalf y)) =
          centerAt (singletonCenter a (torusHalf y)) a -
            2 • centerAt (singletonCenter a (torusHalf y)) b +
            centerAt (singletonCenter a (torusHalf y)) a by rfl,
        centerAt_singleton_self,
        centerAt_singleton_of_ne hba]
      simpa [two_nsmul] using two_nsmul_torusHalf y
    · refine ⟨singletonCenter a y, ?_⟩
      have hba : b ≠ a := fun hba ↦ hab hba.symm
      have hca : c ≠ a := fun hca ↦ hac hca.symm
      simp [affineCombo, centerAt_singleton_of_ne hba,
        centerAt_singleton_of_ne hca, centerAt_singleton_self]

/-- A continuous surjective homomorphism from the product center space to a
torus preserves normalized Haar volume. -/
theorem measurePreserving_affineCombo {Y S D : ℕ}
    (a b c : Fin Y × Fin S) (h : ¬ (a = b ∧ b = c)) :
    MeasurePreserving (affineCombo (D := D) a b c) := by
  letI : BorelSpace (Torus D) := Pi.borelSpace
  letI : BorelSpace (Fin S → Torus D) := Pi.borelSpace
  letI : BorelSpace (CenterFamily Y S D) := Pi.borelSpace
  letI : IsProbabilityMeasure (volume : Measure (Torus D)) :=
    probabilityVolume D
  letI : IsProbabilityMeasure
      (volume : Measure (Fin S → Torus D)) := by
    rw [volume_pi]
    exact probabilityMeasurePi
  letI : IsProbabilityMeasure
      (volume : Measure (CenterFamily Y S D)) := by
    rw [volume_pi]
    exact probabilityMeasurePi
  letI : (volume : Measure (Fin S → Torus D)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  letI : (volume : Measure (CenterFamily Y S D)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  let f := affineCombo (D := D) a b c
  have hf : Continuous f := continuous_affineCombo a b c
  have hsurj : Surjective f := affineCombo_surjective a b c h
  letI : IsProbabilityMeasure
      (Measure.map f (volume : Measure (CenterFamily Y S D))) :=
    Measure.isProbabilityMeasure_map hf.measurable.aemeasurable
  letI : (Measure.map f
      (volume : Measure (CenterFamily Y S D))).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure
      (volume : Measure (CenterFamily Y S D)) f hf hsurj
  refine ⟨hf.measurable, ?_⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
    (Measure.map f (volume : Measure (CenterFamily Y S D)))
    (volume : Measure (Torus D))

/-- Bad event for one ordered triple of center coordinates.  The diagonal
triple is declared empty. -/
def separationEvent {Y S D : ℕ} (δ : ℝ) (a b c : Fin Y × Fin S) :
    Set (CenterFamily Y S D) :=
  if a = b ∧ b = c then ∅
  else affineCombo (D := D) a b c ⁻¹' centeredBox D δ

lemma volume_separationEvent_le {Y S D : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : 2 * δ ≤ 1) (a b c : Fin Y × Fin S) :
    volume (separationEvent (D := D) δ a b c) ≤
      ENNReal.ofReal (2 * δ) ^ D := by
  classical
  by_cases h : a = b ∧ b = c
  · simp [separationEvent, h]
  · rw [separationEvent, if_neg h]
    rw [(measurePreserving_affineCombo a b c h).measure_preimage]
    · exact (volume_centeredBox hδ0 hδ).le
    · exact (centeredBox_compact D δ).measurableSet.nullMeasurableSet

/-- Union of all nontrivial approximate affine-relation events. -/
def someSeparationEvent {Y S D : ℕ} (δ : ℝ) :
    Set (CenterFamily Y S D) :=
  ⋃ a : Fin Y × Fin S, ⋃ b : Fin Y × Fin S,
    ⋃ c : Fin Y × Fin S, separationEvent (D := D) δ a b c

lemma volume_someSeparationEvent_le {Y S D : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : 2 * δ ≤ 1) :
    volume (someSeparationEvent (Y := Y) (S := S) (D := D) δ) ≤
      (Y * S) ^ 3 * ENNReal.ofReal (2 * δ) ^ D := by
  classical
  rw [someSeparationEvent]
  calc
    volume (⋃ a : Fin Y × Fin S, ⋃ b : Fin Y × Fin S,
        ⋃ c : Fin Y × Fin S, separationEvent (D := D) δ a b c) ≤
        ∑ a : Fin Y × Fin S, ∑ b : Fin Y × Fin S,
          ∑ c : Fin Y × Fin S,
            volume (separationEvent (D := D) δ a b c) := by
      calc
        _ ≤ ∑ a : Fin Y × Fin S,
            volume (⋃ b : Fin Y × Fin S, ⋃ c : Fin Y × Fin S,
              separationEvent (D := D) δ a b c) :=
          measure_iUnion_fintype_le _ _
        _ ≤ ∑ a : Fin Y × Fin S, ∑ b : Fin Y × Fin S,
            volume (⋃ c : Fin Y × Fin S,
              separationEvent (D := D) δ a b c) := by
          gcongr with a
          exact measure_iUnion_fintype_le _ _
        _ ≤ ∑ a : Fin Y × Fin S, ∑ b : Fin Y × Fin S,
            ∑ c : Fin Y × Fin S,
              volume (separationEvent (D := D) δ a b c) := by
          gcongr with a b
          exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _a : Fin Y × Fin S, ∑ _b : Fin Y × Fin S,
        ∑ _c : Fin Y × Fin S, ENNReal.ofReal (2 * δ) ^ D := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      apply Finset.sum_le_sum
      intro c _hc
      exact volume_separationEvent_le hδ0 hδ a b c
    _ = (Y * S) ^ 3 * ENNReal.ofReal (2 * δ) ^ D := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin]
      push_cast
      ring

/-- Quantitative affine separation of a center family. -/
def AffinelySeparated {Y S D : ℕ} (δ : ℝ)
    (x : CenterFamily Y S D) : Prop :=
  ∀ a b c : Fin Y × Fin S,
    affineCombo (D := D) a b c x ∈ centeredBox D δ →
      a = b ∧ b = c

/-- The two union bounds select one family with both exact phase distribution
and affine separation. -/
theorem exists_phaseDistributed_affinelySeparated
    {D H R Y S Q : ℕ} {r δ : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ : 2 * δ ≤ 1)
    (hQ : 2 ≤ Q) (hmesh : (Q : ℝ)⁻¹ ≤ r)
    (hsmall :
      (Fintype.card (PhaseRequest D H R Q) * Y : ℕ) *
          (1 - ENNReal.ofReal (2 * r) ^ R) ^ S +
        (Y * S) ^ 3 * ENNReal.ofReal (2 * δ) ^ D < 1) :
    ∃ x : CenterFamily Y S D,
      PhaseDistributed (H := H) (R := R) r x ∧
        AffinelySeparated δ x := by
  let F : PhaseRequest D H R Q → Set (Torus D) := requestTarget r
  let miss : Set (CenterFamily Y S D) := someMissEvent F
  let sep : Set (CenterFamily Y S D) := someSeparationEvent δ
  have hmiss : volume miss ≤
      (Fintype.card (PhaseRequest D H R Q) * Y : ℕ) *
        (1 - ENNReal.ofReal (2 * r) ^ R) ^ S := by
    exact volume_someMissEvent_le F
      (fun q ↦ measurableSet_requestTarget r q)
      (fun q ↦ volume_requestTarget hr0 hr q)
  have hsep : volume sep ≤
      (Y * S) ^ 3 * ENNReal.ofReal (2 * δ) ^ D :=
    volume_someSeparationEvent_le hδ0 hδ
  have hbad : volume (miss ∪ sep) < 1 :=
    (measure_union_le miss sep |>.trans (add_le_add hmiss hsep)).trans_lt hsmall
  have hproper : miss ∪ sep ≠ Set.univ := by
    intro heq
    rw [heq] at hbad
    letI : IsProbabilityMeasure (volume : Measure (Torus D)) :=
      probabilityVolume D
    letI : IsProbabilityMeasure
        (volume : Measure (Fin S → Torus D)) := by
      rw [volume_pi]
      exact probabilityMeasurePi
    letI : IsProbabilityMeasure
        (volume : Measure (CenterFamily Y S D)) := by
      rw [volume_pi]
      exact probabilityMeasurePi
    simpa using hbad
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
  have hxmiss : x ∉ miss := fun hxm ↦ hx (Or.inl hxm)
  have hxsep : x ∉ sep := fun hxs ↦ hx (Or.inr hxs)
  have hhit : ∀ q : PhaseRequest D H R Q, ∀ b : Fin Y,
      ∃ s, x b s ∈ F q := by
    simp only [miss, someMissEvent, mem_iUnion, not_exists, missEvent] at hxmiss
    intro q b
    simpa using not_forall.mp (hxmiss q b)
  have hdist : PhaseDistributed (H := H) (R := R) r x := by
    intro ξ b xStar
    let centers : Set (Torus D) := Set.range (x b)
    have hhit' : ∀ a : Fin (latticeRank (codedSubspace ξ)) → Fin Q,
        ∃ z ∈ centers, z ∈ phaseNetTarget (codedSubspace ξ) r a := by
      intro a
      obtain ⟨s, hs⟩ := hhit (⟨ξ, a⟩ : PhaseRequest D H R Q) b
      exact ⟨x b s, ⟨s, rfl⟩, hs⟩
    obtain ⟨z, ⟨s, rfl⟩, u, hu, hphase⟩ :=
      exists_small_correction_of_hits_phaseNet
        (codedSubspace ξ) hr0 hQ hmesh centers hhit' xStar
    refine ⟨s, u, ?_, hphase⟩
    have hsqrt : Real.sqrt (latticeRank (codedSubspace ξ)) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt (by exact_mod_cast latticeRank_codedSubspace_le ξ)
    exact hu.trans (by gcongr)
  have hseparated : AffinelySeparated δ x := by
    intro a b c habc
    by_contra htriple
    apply hxsep
    simp only [sep, someSeparationEvent, mem_iUnion]
    refine ⟨a, b, c, ?_⟩
    simp [separationEvent, htriple, habc]
  exact ⟨x, hdist, hseparated⟩

end Erdos721.HunterSeparatedCenters
