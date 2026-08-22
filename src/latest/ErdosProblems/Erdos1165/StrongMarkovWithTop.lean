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

import ErdosProblems.Erdos1165.Basic
import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.Clock

/-!
# Strong Markov at possibly infinite clocks

`Markov.lean` proves the finite-dimensional strong Markov property for a
natural-valued stopping time.  First-hitting clocks such as `thresholdTime`
naturally take values in `WithTop ℕ`.  This file bridges the two forms.

The proof truncates a `WithTop ℕ` stopping time at a deterministic level,
applies the finite theorem on `{τ ≤ N}`, and exhausts `{τ < ⊤}` by these
bounded events.  No pointwise finiteness assumption is made.  The final
specialization removes `{τ < ⊤}` under the explicitly supplied hypothesis
that `τ` is almost surely finite.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165

variable {τ : StepPath → WithTop ℕ} {A : Set StepPath}

/-! ## Deterministic truncation -/

/-- The natural-valued clock obtained by replacing `τ` by `min τ N` and
removing the (now impossible) value `⊤`. -/
def truncateStoppingTime (τ : StepPath → WithTop ℕ) (N : ℕ) : StepPath → ℕ :=
  fun ω ↦ (min (τ ω) (N : WithTop ℕ)).untop
    ((min_le_right (τ ω) (N : WithTop ℕ)).trans_lt (WithTop.coe_lt_top N)).ne

@[simp] theorem coe_truncateStoppingTime (τ : StepPath → WithTop ℕ) (N : ℕ)
    (ω : StepPath) :
    (truncateStoppingTime τ N ω : WithTop ℕ) = min (τ ω) N := by
  exact WithTop.coe_untop _ _

/-- Truncating a `WithTop` stopping time produces a finite stopping time. -/
theorem isFiniteStoppingTime_truncate
    (hτ : IsStoppingTime incrementFiltration τ) (N : ℕ) :
    IsFiniteStoppingTime (truncateStoppingTime τ N) := by
  change IsStoppingTime incrementFiltration
    (fun ω ↦ (truncateStoppingTime τ N ω : WithTop ℕ))
  intro n
  change MeasurableSet[incrementFiltration n]
    {ω | (truncateStoppingTime τ N ω : WithTop ℕ) ≤ (n : WithTop ℕ)}
  by_cases hNn : N ≤ n
  · have hall : {ω : StepPath | (truncateStoppingTime τ N ω : WithTop ℕ) ≤ n} =
        Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      rw [coe_truncateStoppingTime]
      exact (min_le_right (τ ω) N).trans (by exact_mod_cast hNn)
    rw [hall]
    exact MeasurableSet.univ
  · have heq : {ω : StepPath | (truncateStoppingTime τ N ω : WithTop ℕ) ≤ n} =
        {ω | τ ω ≤ n} := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, coe_truncateStoppingTime]
      simp only [min_le_iff]
      norm_cast
      simp [hNn]
    rw [heq]
    exact hτ n

@[simp] theorem truncateStoppingTime_eq_of_le {N : ℕ} {ω : StepPath}
    (hτN : τ ω ≤ N) :
    (truncateStoppingTime τ N ω : WithTop ℕ) = τ ω := by
  rw [coe_truncateStoppingTime, min_eq_left hτN]

/-! ## Events observable at an extended stopping time -/

/-- Concrete atomwise form of measurability at a possibly-infinite stopping
time.  The value-`n` part must be observable from the first `n` increments.
No condition at `⊤` is needed for a theorem restricted to `{τ < ⊤}`. -/
def IsMeasurableAtWithTopStopping (τ : StepPath → WithTop ℕ)
    (A : Set StepPath) : Prop :=
  ∀ n, MeasurableSet[incrementFiltration n] (A ∩ {ω | τ ω = n})

/-- Mathlib's stopped sigma-algebra implies the atomwise formulation used in
this file. -/
theorem isMeasurableAtWithTopStopping_of_measurableSet_stopping
    (hτ : IsStoppingTime incrementFiltration τ)
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    IsMeasurableAtWithTopStopping τ A := by
  intro n
  exact (hτ.measurableSet_inter_eq_iff A n).mp
    (hA.inter (hτ.measurableSet_eq' n))

/-! ## Future blocks and bounded stopped events -/

/-- The first `k` increments after a `WithTop ℕ` clock.  Its value on
`{τ = ⊤}` is deliberately arbitrary (the default time is zero); every theorem
below either restricts to `{τ < ⊤}` or assumes this exceptional event is null. -/
def postWithTopStoppingBlock (τ : StepPath → WithTop ℕ) (k : ℕ)
    (ω : StepPath) : Fin k → Direction :=
  fun j ↦ ω ((τ ω).untopD 0 + j)

private theorem postWithTopStoppingBlock_eq_truncate_of_le (N k : ℕ)
    {ω : StepPath} (hτN : τ ω ≤ N) :
    postWithTopStoppingBlock τ k ω =
      postStoppingBlock (truncateStoppingTime τ N) k ω := by
  cases h : τ ω with
  | top => simp [h] at hτN
  | coe n =>
      have hnN : n ≤ N := WithTop.coe_le_coe.mp (h ▸ hτN)
      have htrunc : truncateStoppingTime τ N ω = n := by
        apply WithTop.coe_injective
        calc
          (truncateStoppingTime τ N ω : WithTop ℕ) = min (τ ω) N :=
            coe_truncateStoppingTime τ N ω
          _ = min (n : WithTop ℕ) N :=
            congrArg (fun q : WithTop ℕ ↦ min q (N : WithTop ℕ)) h
          _ = n := by simp [hnN]
      funext j
      simp only [postWithTopStoppingBlock, postStoppingBlock, h, htrunc]
      rw [WithTop.untopD_coe]

/-- Restricting an event observable at `τ` to `{τ ≤ N}` makes it observable
at the natural-valued truncated clock. -/
theorem isMeasurableAtStopping_inter_le_truncate
    (hA : IsMeasurableAtWithTopStopping τ A) (N : ℕ) :
    IsMeasurableAtStopping (truncateStoppingTime τ N)
      (A ∩ {ω | τ ω ≤ N}) := by
  intro n
  by_cases hnN : n ≤ N
  · have heq :
        (A ∩ {ω | τ ω ≤ N}) ∩ {ω | truncateStoppingTime τ N ω = n} =
          A ∩ {ω | τ ω = n} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hωA, hτN⟩, htrunc⟩
        refine ⟨hωA, ?_⟩
        have hcoetrunc := congrArg (fun q : ℕ ↦ (q : WithTop ℕ)) htrunc
        rw [coe_truncateStoppingTime, min_eq_left hτN] at hcoetrunc
        exact hcoetrunc
      · rintro ⟨hωA, hτn⟩
        have hτN : τ ω ≤ (N : WithTop ℕ) := by
          rw [hτn]
          exact_mod_cast hnN
        refine ⟨⟨hωA, hτN⟩, ?_⟩
        apply WithTop.coe_injective
        calc
          (truncateStoppingTime τ N ω : WithTop ℕ) = min (τ ω) N :=
            coe_truncateStoppingTime τ N ω
          _ = τ ω := min_eq_left hτN
          _ = n := hτn
    rw [heq]
    exact hA n
  · have heq :
        (A ∩ {ω | τ ω ≤ N}) ∩ {ω | truncateStoppingTime τ N ω = n} =
          ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨⟨_, _⟩, htrunc⟩
        have htrunc_le : truncateStoppingTime τ N ω ≤ N := by
          apply WithTop.coe_le_coe.mp
          calc
            (truncateStoppingTime τ N ω : WithTop ℕ) = min (τ ω) N :=
              coe_truncateStoppingTime τ N ω
            _ ≤ N := min_le_right _ _
        exact hnN (htrunc ▸ htrunc_le)
      · exact False.elim
    rw [heq]
    exact @MeasurableSet.empty StepPath (incrementFiltration n)

/-- Strong Markov factorization on the bounded finite-value event `{τ ≤ N}`.
This is exactly the finite theorem after deterministic truncation. -/
theorem strongMarkov_withTop_bounded
    (hτ : IsStoppingTime incrementFiltration τ)
    (hA : IsMeasurableAtWithTopStopping τ A) (N k : ℕ)
    (C : Set (Fin k → Direction)) :
    fairSteps ((A ∩ {ω | τ ω ≤ N}) ∩ postWithTopStoppingBlock τ k ⁻¹' C) =
      fairSteps (A ∩ {ω | τ ω ≤ N}) * fairBlock k C := by
  have heq :
      (A ∩ {ω | τ ω ≤ N}) ∩ postWithTopStoppingBlock τ k ⁻¹' C =
        (A ∩ {ω | τ ω ≤ N}) ∩
          postStoppingBlock (truncateStoppingTime τ N) k ⁻¹' C := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hω, hblock⟩
      exact ⟨hω,
        (postWithTopStoppingBlock_eq_truncate_of_le N k hω.2) ▸ hblock⟩
    · rintro ⟨hω, hblock⟩
      exact ⟨hω,
        (postWithTopStoppingBlock_eq_truncate_of_le N k hω.2).symm ▸ hblock⟩
  rw [heq]
  exact strongMarkov_stoppedEvent_set
    (isFiniteStoppingTime_truncate hτ N)
    (isMeasurableAtStopping_inter_le_truncate hA N) k C

/-! ## Exhaustion of the finite-value event -/

/-- **Strong Markov factorization for a possibly infinite clock.**  The
factorization is exact after intersecting the stopped-past event with the
finite-value event `{τ < ⊤}`. -/
theorem strongMarkov_withTop_finiteEvent
    (hτ : IsStoppingTime incrementFiltration τ)
    (hA : IsMeasurableAtWithTopStopping τ A) (k : ℕ)
    (C : Set (Fin k → Direction)) :
    fairSteps ((A ∩ {ω | τ ω < ⊤}) ∩ postWithTopStoppingBlock τ k ⁻¹' C) =
      fairSteps (A ∩ {ω | τ ω < ⊤}) * fairBlock k C := by
  let B : ℕ → Set StepPath := fun N ↦ A ∩ {ω | τ ω ≤ N}
  let D : ℕ → Set StepPath := fun N ↦ B N ∩ postWithTopStoppingBlock τ k ⁻¹' C
  have hBmono : Monotone B := by
    intro n m hnm ω hω
    exact ⟨hω.1, hω.2.trans (WithTop.coe_le_coe.mpr hnm)⟩
  have hDmono : Monotone D := by
    intro n m hnm ω hω
    exact ⟨hBmono hnm hω.1, hω.2⟩
  have hBunion : (⋃ N, B N) = A ∩ {ω | τ ω < ⊤} := by
    ext ω
    simp only [Set.mem_iUnion, B, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N, hωA, hτN⟩
      exact ⟨hωA, hτN.trans_lt (WithTop.coe_lt_top N)⟩
    · rintro ⟨hωA, hτfinite⟩
      have hne : τ ω ≠ ⊤ := WithTop.lt_top_iff_ne_top.mp hτfinite
      lift τ ω to ℕ using hne with n hn
      exact ⟨n, hωA, le_rfl⟩
  have hDunion :
      (⋃ N, D N) =
        (A ∩ {ω | τ ω < ⊤}) ∩ postWithTopStoppingBlock τ k ⁻¹' C := by
    calc
      (⋃ N, D N) = (⋃ N, B N) ∩ postWithTopStoppingBlock τ k ⁻¹' C := by
        exact (Set.iUnion_inter (postWithTopStoppingBlock τ k ⁻¹' C) B).symm
      _ = (A ∩ {ω | τ ω < ⊤}) ∩ postWithTopStoppingBlock τ k ⁻¹' C := by
        rw [hBunion]
  have hfactor (N : ℕ) :
      fairSteps (D N) = fairSteps (B N) * fairBlock k C := by
    exact strongMarkov_withTop_bounded hτ hA N k C
  calc
    fairSteps ((A ∩ {ω | τ ω < ⊤}) ∩ postWithTopStoppingBlock τ k ⁻¹' C) =
        fairSteps (⋃ N, D N) := congrArg fairSteps hDunion.symm
    _ = ⨆ N, fairSteps (D N) := hDmono.measure_iUnion
    _ = ⨆ N, fairSteps (B N) * fairBlock k C := by
      congr 1
      funext N
      exact hfactor N
    _ = (⨆ N, fairSteps (B N)) * fairBlock k C :=
      (ENNReal.iSup_mul (fun N ↦ fairSteps (B N)) (fairBlock k C)).symm
    _ = fairSteps (⋃ N, B N) * fairBlock k C := by
      rw [hBmono.measure_iUnion]
    _ = fairSteps (A ∩ {ω | τ ω < ⊤}) * fairBlock k C := by
      rw [hBunion]

/-- Version of `strongMarkov_withTop_finiteEvent` whose measurability
hypothesis is stated using Mathlib's stopped sigma-algebra. -/
theorem strongMarkov_withTop_finiteEvent_of_measurableSet_stopping
    (hτ : IsStoppingTime incrementFiltration τ)
    (hA : MeasurableSet[hτ.measurableSpace] A) (k : ℕ)
    (C : Set (Fin k → Direction)) :
    fairSteps ((A ∩ {ω | τ ω < ⊤}) ∩ postWithTopStoppingBlock τ k ⁻¹' C) =
      fairSteps (A ∩ {ω | τ ω < ⊤}) * fairBlock k C :=
  strongMarkov_withTop_finiteEvent hτ
    (isMeasurableAtWithTopStopping_of_measurableSet_stopping hτ hA) k C

/-- The finite-value event itself factors from every finite future block. -/
theorem strongMarkov_withTop_finiteEvent_univ
    (hτ : IsStoppingTime incrementFiltration τ) (k : ℕ)
    (C : Set (Fin k → Direction)) :
    fairSteps ({ω | τ ω < ⊤} ∩ postWithTopStoppingBlock τ k ⁻¹' C) =
      fairSteps {ω | τ ω < ⊤} * fairBlock k C := by
  have hU : IsMeasurableAtWithTopStopping τ (Set.univ : Set StepPath) := by
    intro n
    simpa using hτ.measurableSet_eq n
  simpa using
    (strongMarkov_withTop_finiteEvent (τ := τ) (A := Set.univ) hτ hU k C)

/-! ## Almost-surely finite clocks -/

/-- If the stopping time is almost surely finite, the exceptional
`{τ = ⊤}` part can be removed from both sides of the exact finite-event
factorization. -/
theorem strongMarkov_withTop_of_ae_finite
    (hτ : IsStoppingTime incrementFiltration τ)
    (hA : IsMeasurableAtWithTopStopping τ A)
    (hfinite : ∀ᵐ ω ∂fairSteps, τ ω < ⊤) (k : ℕ)
    (C : Set (Fin k → Direction)) :
    fairSteps (A ∩ postWithTopStoppingBlock τ k ⁻¹' C) =
      fairSteps A * fairBlock k C := by
  have hAeq : (A : Set StepPath) =ᵐ[fairSteps]
      (A ∩ {ω | τ ω < ⊤} : Set StepPath) := by
    filter_upwards [hfinite] with ω hω
    exact propext (and_iff_left hω).symm
  have hleft :
      (A ∩ postWithTopStoppingBlock τ k ⁻¹' C : Set StepPath) =ᵐ[fairSteps]
        ((A ∩ {ω | τ ω < ⊤}) ∩
          postWithTopStoppingBlock τ k ⁻¹' C : Set StepPath) :=
    hAeq.inter (ae_eq_refl _)
  rw [measure_congr hleft,
    strongMarkov_withTop_finiteEvent hτ hA k C,
    measure_congr hAeq]

/-- Almost-surely finite specialization with a Mathlib stopped-sigma-algebra
hypothesis for the past event. -/
theorem strongMarkov_withTop_of_ae_finite_of_measurableSet_stopping
    (hτ : IsStoppingTime incrementFiltration τ)
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (hfinite : ∀ᵐ ω ∂fairSteps, τ ω < ⊤) (k : ℕ)
    (C : Set (Fin k → Direction)) :
    fairSteps (A ∩ postWithTopStoppingBlock τ k ⁻¹' C) =
      fairSteps A * fairBlock k C :=
  strongMarkov_withTop_of_ae_finite hτ
    (isMeasurableAtWithTopStopping_of_measurableSet_stopping hτ hA)
    hfinite k C

/-- At an almost surely finite `WithTop ℕ` stopping time, a finite future
block has exactly its fresh product law. -/
theorem fairSteps_postWithTopStoppingBlock_of_ae_finite
    (hτ : IsStoppingTime incrementFiltration τ)
    (hfinite : ∀ᵐ ω ∂fairSteps, τ ω < ⊤) (k : ℕ)
    (C : Set (Fin k → Direction)) :
    fairSteps (postWithTopStoppingBlock τ k ⁻¹' C) = fairBlock k C := by
  have hU : IsMeasurableAtWithTopStopping τ (Set.univ : Set StepPath) := by
    intro n
    simpa using hτ.measurableSet_eq n
  simpa using
    (strongMarkov_withTop_of_ae_finite (τ := τ) (A := Set.univ)
      hτ hU hfinite k C)

end Erdos1165
