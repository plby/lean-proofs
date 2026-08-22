/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.StrongMarkovWithTop
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Strong Markov for the complete future increment sequence

`StrongMarkovWithTop` proves factorization for every finite future block.
Here finite-dimensional uniqueness on the countable product upgrades that
result to every measurable event of the complete future increment sequence.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos1165

noncomputable section

/-- The entire increment sequence following a possibly-infinite stopping
time.  As for `postWithTopStoppingBlock`, time zero is used on `{tau = ⊤}`;
all factorization results below restrict to the finite-value event. -/
def postWithTopStoppingSteps (tau : StepPath → WithTop ℕ) (omega : StepPath) :
    StepPath :=
  shiftSteps ((tau omega).untopD 0) omega

@[simp] theorem stepPrefix_postWithTopStoppingSteps
    (tau : StepPath → WithTop ℕ) (k : ℕ) (omega : StepPath) :
    stepPrefix k (postWithTopStoppingSteps tau omega) =
      postWithTopStoppingBlock tau k omega := rfl

/-- A finite block after a stopping time is globally measurable. -/
theorem measurable_postWithTopStoppingBlock'
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) (k : ℕ) :
    Measurable (postWithTopStoppingBlock tau k) := by
  intro C hC
  have hpre : postWithTopStoppingBlock tau k ⁻¹' C =
      ({omega | tau omega = ⊤} ∩ stepBlock 0 k ⁻¹' C) ∪
        ⋃ n : ℕ, {omega | tau omega = n} ∩ stepBlock n k ⁻¹' C := by
    ext omega
    simp only [mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    cases h : tau omega with
    | top =>
        have hblock : postWithTopStoppingBlock tau k omega = stepBlock 0 k omega := by
          funext j
          simp [postWithTopStoppingBlock, stepBlock, h]
        rw [hblock]
        simp
    | coe n =>
        have hblock : postWithTopStoppingBlock tau k omega = stepBlock n k omega := by
          funext j
          change omega ((tau omega).untopD 0 + (j : ℕ)) = omega (n + (j : ℕ))
          rw [h]
          exact congrArg (fun q : ℕ ↦ omega (q + (j : ℕ)))
            (WithTop.untopD_coe (0 : ℕ) n)
        rw [hblock]
        simp
  rw [hpre]
  have hcoe (n : ℕ) : MeasurableSet {omega : StepPath | tau omega = (n : WithTop ℕ)} :=
    incrementFiltration.le n _ (htau.measurableSet_eq n)
  have htopEq : {omega : StepPath | tau omega = ⊤} =
      (⋃ n : ℕ, {omega | tau omega = (n : WithTop ℕ)})ᶜ := by
    ext omega
    cases h : tau omega <;> simp [h]
  have htop : MeasurableSet {omega : StepPath | tau omega = ⊤} := by
    rw [htopEq]
    exact (MeasurableSet.iUnion hcoe).compl
  exact (htop.inter ((measurable_stepBlock 0 k) hC)).union
    (MeasurableSet.iUnion fun n : ℕ ↦
      (hcoe n).inter ((measurable_stepBlock n k) hC))

theorem measurable_postWithTopStoppingSteps
    {tau : StepPath → WithTop ℕ}
    (htau : IsStoppingTime incrementFiltration tau) :
    Measurable (postWithTopStoppingSteps tau) := by
  apply measurable_pi_lambda
  intro j
  let e : Fin (j + 1) := ⟨j, Nat.lt_succ_self j⟩
  have h := (measurable_pi_apply e).comp
    (measurable_postWithTopStoppingBlock' htau (j + 1))
  change Measurable (fun omega ↦
    postWithTopStoppingBlock tau (j + 1) omega e)
  exact h

private theorem stoppedFinitePart_measurable
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (hA : IsMeasurableAtWithTopStopping tau A) :
    MeasurableSet (A ∩ {omega | tau omega < ⊤}) := by
  have heq : A ∩ {omega | tau omega < ⊤} =
      ⋃ n : ℕ, A ∩ {omega | tau omega = (n : WithTop ℕ)} := by
    ext omega
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hωA, hfinite⟩
      have hne : tau omega ≠ ⊤ := WithTop.lt_top_iff_ne_top.mp hfinite
      cases hτ : tau omega with
      | top => exact (hne hτ).elim
      | coe n => exact ⟨n, hωA, rfl⟩
    · rintro ⟨n, hωA, hτ⟩
      exact ⟨hωA, hτ ▸ WithTop.coe_lt_top n⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦ incrementFiltration.le n _ (hA n)

private theorem cylinder_as_stepPrefix_preimage
    {I : Finset ℕ} {S : Set (∀ _i : I, Direction)}
    (_hS : MeasurableSet S) :
    ∃ k : ℕ, ∃ C : Set (Fin k → Direction), MeasurableSet C ∧
      cylinder I S = stepPrefix k ⁻¹' C := by
  let k := (∑ i ∈ I, i) + 1
  have hi (i : I) : (i : ℕ) < k := by
    apply Nat.lt_succ_of_le
    exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le q) i.property
  let restrictI : (Fin k → Direction) → (∀ i : I, Direction) :=
    fun u i ↦ u ⟨i, hi i⟩
  let C : Set (Fin k → Direction) := restrictI ⁻¹' S
  have hC : MeasurableSet C := (measurable_of_countable restrictI) _hS
  refine ⟨k, C, hC, ?_⟩
  ext omega
  simp only [mem_cylinder, Finset.restrict_def, mem_preimage, C, restrictI, stepPrefix]

private theorem fairBlock_cylinderStatistic
    {I : Finset ℕ} {S : Set (∀ _i : I, Direction)} (_hS : MeasurableSet S)
    {k : ℕ} {C : Set (Fin k → Direction)} (hC : MeasurableSet C)
    (hEq : cylinder I S = stepPrefix k ⁻¹' C) :
    fairBlock k C = fairSteps (cylinder I S) := by
  have hmap := congrArg (fun mu : Measure (Fin k → Direction) ↦ mu C)
    (fairSteps_map_stepBlock 0 k)
  rw [Measure.map_apply (measurable_stepBlock 0 k) hC] at hmap
  have hblock : stepBlock 0 k = stepPrefix k := by
    funext omega j
    simp [stepBlock, stepPrefix]
  rw [hblock, ← hEq] at hmap
  exact hmap.symm

/-- Full-tail strong Markov factorization on the finite part of a possibly
infinite stopping time. -/
theorem strongMarkov_withTop_fullTail_finiteEvent
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (hA : IsMeasurableAtWithTopStopping tau A)
    {C : Set StepPath} (hC : MeasurableSet C) :
    fairSteps ((A ∩ {omega | tau omega < ⊤}) ∩
        postWithTopStoppingSteps tau ⁻¹' C) =
      fairSteps (A ∩ {omega | tau omega < ⊤}) * fairSteps C := by
  let B : Set StepPath := A ∩ {omega | tau omega < ⊤}
  have hB : MeasurableSet B := stoppedFinitePart_measurable hA
  have hpost : Measurable (postWithTopStoppingSteps tau) :=
    measurable_postWithTopStoppingSteps htau
  let mu : Measure StepPath :=
    (fairSteps.restrict B).map (postWithTopStoppingSteps tau)
  let nu : Measure StepPath := (fairSteps B) • fairSteps
  have hmuFinite : IsFiniteMeasure mu := by
    dsimp only [mu]
    infer_instance
  let _ : IsFiniteMeasure mu := hmuFinite
  have hcyl : ∀ D ∈ measurableCylinders (fun _ : ℕ ↦ Direction), mu D = nu D := by
    intro D hD
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders D).mp hD
    obtain ⟨k, Ck, hCk, hEq⟩ := cylinder_as_stepPrefix_preimage hS
    have hpre : postWithTopStoppingSteps tau ⁻¹' cylinder I S =
        postWithTopStoppingBlock tau k ⁻¹' Ck := by
      rw [hEq]
      ext omega
      simp only [mem_preimage]
      rw [stepPrefix_postWithTopStoppingSteps]
    change ((fairSteps.restrict B).map (postWithTopStoppingSteps tau))
        (cylinder I S) = ((fairSteps B) • fairSteps) (cylinder I S)
    rw [Measure.map_apply hpost hS.cylinder,
      Measure.restrict_apply (hS.cylinder.preimage hpost), inter_comm, hpre]
    rw [Measure.smul_apply, smul_eq_mul]
    rw [strongMarkov_withTop_finiteEvent htau hA k Ck]
    rw [fairBlock_cylinderStatistic hS hCk hEq]
  have hmass : mu Set.univ = nu Set.univ := by
    have huniv : (Set.univ : Set StepPath) ∈
        measurableCylinders (fun _ : ℕ ↦ Direction) := by
      exact (mem_measurableCylinders _).mpr
        ⟨∅, Set.univ, MeasurableSet.univ, by simp⟩
    exact hcyl Set.univ huniv
  have hmeasure : mu = nu :=
    ext_of_generate_finite
      (measurableCylinders (fun _ : ℕ ↦ Direction))
      generateFrom_measurableCylinders.symm
      isPiSystem_measurableCylinders hcyl hmass
  have happ := congrArg (fun rho : Measure StepPath ↦ rho C) hmeasure
  change ((fairSteps.restrict B).map (postWithTopStoppingSteps tau)) C =
      ((fairSteps B) • fairSteps) C at happ
  rw [Measure.map_apply hpost hC, Measure.restrict_apply (hC.preimage hpost),
    inter_comm, Measure.smul_apply, smul_eq_mul] at happ
  exact happ

/-- Full-tail strong Markov at an almost surely finite clock. -/
theorem strongMarkov_withTop_fullTail_of_ae_finite
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    (htau : IsStoppingTime incrementFiltration tau)
    (hA : IsMeasurableAtWithTopStopping tau A)
    (hfinite : ∀ᵐ omega ∂fairSteps, tau omega < ⊤)
    {C : Set StepPath} (hC : MeasurableSet C) :
    fairSteps (A ∩ postWithTopStoppingSteps tau ⁻¹' C) =
      fairSteps A * fairSteps C := by
  have hAeq : (A : Set StepPath) =ᵐ[fairSteps]
      (A ∩ {omega | tau omega < ⊤} : Set StepPath) := by
    filter_upwards [hfinite] with omega hω
    exact propext (and_iff_left hω).symm
  have hleft :
      (A ∩ postWithTopStoppingSteps tau ⁻¹' C : Set StepPath) =ᵐ[fairSteps]
        ((A ∩ {omega | tau omega < ⊤}) ∩
          postWithTopStoppingSteps tau ⁻¹' C : Set StepPath) :=
    hAeq.inter (ae_eq_refl _)
  rw [measure_congr hleft,
    strongMarkov_withTop_fullTail_finiteEvent htau hA hC,
    measure_congr hAeq]

/-- Countable stopped-parameter disintegration on the finite part of a
possibly-infinite stopping time. -/
theorem strongMarkov_withTop_fullTail_countable_partition_finiteEvent
    {tau : StepPath → WithTop ℕ} {A : Set StepPath}
    {X : Type*} [Countable X]
    (htau : IsStoppingTime incrementFiltration tau) (location : StepPath → X)
    (hfiber : ∀ x, IsMeasurableAtWithTopStopping tau
      (A ∩ {omega | location omega = x}))
    (K : X → Set StepPath) (hK : ∀ x, MeasurableSet (K x)) :
    fairSteps {omega | omega ∈ A ∧ tau omega < ⊤ ∧
        postWithTopStoppingSteps tau omega ∈ K (location omega)} =
      ∑' x, fairSteps ((A ∩ {omega | location omega = x}) ∩
          {omega | tau omega < ⊤}) * fairSteps (K x) := by
  let D : X → Set StepPath := fun x ↦
    ((A ∩ {omega | location omega = x}) ∩ {omega | tau omega < ⊤}) ∩
      postWithTopStoppingSteps tau ⁻¹' K x
  have hunion : {omega | omega ∈ A ∧ tau omega < ⊤ ∧
      postWithTopStoppingSteps tau omega ∈ K (location omega)} = ⋃ x, D x := by
    ext omega
    constructor
    · rintro ⟨hA, hfinite, hfuture⟩
      exact Set.mem_iUnion.mpr
        ⟨location omega, ⟨⟨⟨hA, rfl⟩, hfinite⟩, hfuture⟩⟩
    · intro h
      obtain ⟨x, ⟨⟨⟨hA, hx⟩, hfinite⟩, hfuture⟩⟩ :=
        Set.mem_iUnion.mp h
      subst x
      exact ⟨hA, hfinite, hfuture⟩
  have hpost := measurable_postWithTopStoppingSteps htau
  have hDmeas : ∀ x, MeasurableSet (D x) := fun x ↦
    (stoppedFinitePart_measurable (hfiber x)).inter ((hK x).preimage hpost)
  have hDdisjoint : Pairwise fun x y ↦ Disjoint (D x) (D y) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro omega hx hy
    exact hxy (hx.1.1.2.symm.trans hy.1.1.2)
  rw [hunion, measure_iUnion hDdisjoint hDmeas]
  apply tsum_congr
  intro x
  exact strongMarkov_withTop_fullTail_finiteEvent htau (hfiber x) (hK x)

/-! ## Natural-valued stopping times and stopped spatial parameters -/

/-- The complete increment sequence after a natural-valued stopping time. -/
def postStoppingSteps (tau : StepPath → ℕ) (omega : StepPath) : StepPath :=
  shiftSteps (tau omega) omega

@[simp] theorem postWithTopStoppingSteps_coe (tau : StepPath → ℕ) :
    postWithTopStoppingSteps (fun omega ↦ (tau omega : WithTop ℕ)) =
      postStoppingSteps tau := by
  funext omega n
  unfold postWithTopStoppingSteps postStoppingSteps shiftSteps
  change omega ((WithTop.untopD 0 (tau omega : WithTop ℕ)) + n) =
    omega (tau omega + n)
  have h : WithTop.untopD 0 (tau omega : WithTop ℕ) = tau omega :=
    WithTop.untopD_coe (0 : ℕ) (tau omega)
  rw [h]

theorem measurable_postStoppingSteps
    {tau : StepPath → ℕ} (htau : IsFiniteStoppingTime tau) :
    Measurable (postStoppingSteps tau) := by
  have h := measurable_postWithTopStoppingSteps
    (tau := fun omega ↦ (tau omega : WithTop ℕ)) htau
  rw [postWithTopStoppingSteps_coe] at h
  exact h

/-- Full-tail strong Markov factorization at a natural-valued stopping time. -/
theorem strongMarkov_fullTail
    {tau : StepPath → ℕ} {A : Set StepPath}
    (htau : IsFiniteStoppingTime tau)
    (hA : IsMeasurableAtStopping tau A)
    {C : Set StepPath} (hC : MeasurableSet C) :
    fairSteps (A ∩ postStoppingSteps tau ⁻¹' C) =
      fairSteps A * fairSteps C := by
  have hA' : IsMeasurableAtWithTopStopping
      (fun omega ↦ (tau omega : WithTop ℕ)) A := by
    intro n
    simpa using hA n
  have hfinite : ∀ᵐ omega ∂fairSteps,
      (tau omega : WithTop ℕ) < ⊤ :=
    Filter.Eventually.of_forall fun omega ↦ WithTop.coe_lt_top (tau omega)
  have h := strongMarkov_withTop_fullTail_of_ae_finite
      (tau := fun omega ↦ (tau omega : WithTop ℕ))
      htau hA' hfinite hC
  rw [postWithTopStoppingSteps_coe] at h
  exact h

/-- Measure-valued form of full-tail strong Markov. -/
theorem map_restrict_postStoppingSteps
    {tau : StepPath → ℕ} {A : Set StepPath}
    (htau : IsFiniteStoppingTime tau)
    (hA : IsMeasurableAtStopping tau A) :
    (fairSteps.restrict A).map (postStoppingSteps tau) =
      (fairSteps A) • fairSteps := by
  apply Measure.ext
  intro C hC
  rw [Measure.map_apply (measurable_postStoppingSteps htau) hC,
    Measure.restrict_apply (hC.preimage (measurable_postStoppingSteps htau)),
    Measure.smul_apply, smul_eq_mul, inter_comm]
  exact strongMarkov_fullTail htau hA hC

/-- Disintegrate a future event whose parameter is a countable-valued
quantity observable at the stopping time.  This is the form used for random
spatial translations: take `location` to be the stopped position and `K x`
to be the fresh-walk event translated by `x`. -/
theorem strongMarkov_fullTail_countable_partition
    {tau : StepPath → ℕ} {A : Set StepPath} {X : Type*} [Countable X]
    (htau : IsFiniteStoppingTime tau) (location : StepPath → X)
    (hfiber : ∀ x, IsMeasurableAtStopping tau
      (A ∩ {omega | location omega = x}))
    (K : X → Set StepPath) (hK : ∀ x, MeasurableSet (K x)) :
    fairSteps {omega | omega ∈ A ∧ postStoppingSteps tau omega ∈ K (location omega)} =
      ∑' x, fairSteps (A ∩ {omega | location omega = x}) * fairSteps (K x) := by
  let D : X → Set StepPath := fun x ↦
    (A ∩ {omega | location omega = x}) ∩ postStoppingSteps tau ⁻¹' K x
  have hunion : {omega | omega ∈ A ∧
      postStoppingSteps tau omega ∈ K (location omega)} = ⋃ x, D x := by
    ext omega
    simp [D]
  have hDmeas : ∀ x, MeasurableSet (D x) := fun x ↦
    (hfiber x).measurableSet.inter
      ((hK x).preimage (measurable_postStoppingSteps htau))
  have hDdisjoint : Pairwise fun x y ↦ Disjoint (D x) (D y) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro omega hx hy
    exact hxy (hx.1.2.symm.trans hy.1.2)
  rw [hunion, measure_iUnion hDdisjoint hDmeas]
  apply tsum_congr
  intro x
  exact strongMarkov_fullTail htau (hfiber x) (hK x)

end

end Erdos1165
