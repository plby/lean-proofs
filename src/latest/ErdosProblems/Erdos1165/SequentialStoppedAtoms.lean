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

import ErdosProblems.Erdos1165.TerminalExcursionBridge

/-!
# Iterating full-history stopped atoms

This module is the measure-theoretic induction used for successive annular
segments.  At stage `j`, `atomEvent` remembers the complete event exposed by
the preceding stopped segments.  The next fresh event may depend on the
position at the current clock.  Full-tail strong Markov gives its conditional
probability after every stopped-history atom; induction then multiplies
uniform one-step bounds.

No independence of a future entrance vector is asserted.  The sole
measurability premise says exactly that the already exposed history belongs to
the sigma algebra at the next clock.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Erdos1165.SequentialStoppedAtoms

open TerminalExcursionBridge

noncomputable section

/-- Successive stopped atoms generated from an initial stopped-past event.
The event at stage `j+1` includes finiteness of the `j`-th clock and a
measurable condition on the complete fresh increment tail after that clock. -/
def atomEvent (initial : Set StepPath)
    (tau : ℕ → StepPath → WithTop ℕ)
    (fresh : ℕ → Point → Set StepPath) : ℕ → Set StepPath
  | 0 => initial
  | j + 1 => {omega | omega ∈ atomEvent initial tau fresh j ∧
      tau j omega < ⊤ ∧
      postWithTopStoppingSteps (tau j) omega ∈
        fresh j (stoppedPosition (tau j) omega)}

@[simp] theorem atomEvent_zero
    (initial : Set StepPath) (tau : ℕ → StepPath → WithTop ℕ)
    (fresh : ℕ → Point → Set StepPath) :
    atomEvent initial tau fresh 0 = initial := rfl

@[simp] theorem atomEvent_succ
    (initial : Set StepPath) (tau : ℕ → StepPath → WithTop ℕ)
    (fresh : ℕ → Point → Set StepPath) (j : ℕ) :
    atomEvent initial tau fresh (j + 1) =
      {omega | omega ∈ atomEvent initial tau fresh j ∧
        tau j omega < ⊤ ∧
        postWithTopStoppingSteps (tau j) omega ∈
          fresh j (stoppedPosition (tau j) omega)} := rfl

/-- Pathwise normal form of a finite sequential atom. -/
theorem mem_atomEvent_iff
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath} {omega : StepPath} :
    ∀ m, omega ∈ atomEvent initial tau fresh m ↔
      omega ∈ initial ∧
        ∀ j < m, tau j omega < ⊤ ∧
          postWithTopStoppingSteps (tau j) omega ∈
            fresh j (stoppedPosition (tau j) omega) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [atomEvent_succ, Set.mem_ofPred_eq, ih]
      constructor
      · rintro ⟨⟨hinitial, hprefix⟩, hmfinite, hmfresh⟩
        refine ⟨hinitial, ?_⟩
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | rfl
        · exact hprefix j hjm
        · exact ⟨hmfinite, hmfresh⟩
      · rintro ⟨hinitial, hall⟩
        exact ⟨⟨hinitial, fun j hj ↦ hall j (hj.trans_le (Nat.le_succ m))⟩,
          (hall m (Nat.lt_succ_self m)).1,
          (hall m (Nat.lt_succ_self m)).2⟩

/-- One stopped-coordinate step, with a random current position and arbitrary
complete stopped history, multiplies uniform fresh-tail bounds. -/
theorem atomEvent_succ_measure_mem_Icc
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath} {j : ℕ}
    (htau : IsStoppingTime incrementFiltration (tau j))
    (hhistory : IsMeasurableAtWithTopStopping (tau j)
      (atomEvent initial tau fresh j))
    (hfresh : ∀ x, MeasurableSet (fresh j x))
    (lower upper : ℝ≥0∞)
    (hprob : ∀ x, fairSteps (fresh j x) ∈ Set.Icc lower upper) :
    fairSteps (atomEvent initial tau fresh (j + 1)) ∈
      Set.Icc
        (fairSteps (atomEvent initial tau fresh j ∩
          {omega | tau j omega < ⊤}) * lower)
        (fairSteps (atomEvent initial tau fresh j ∩
          {omega | tau j omega < ⊤}) * upper) := by
  simpa only [atomEvent_succ] using
    strongMarkov_withTop_stoppedPosition_bounds htau hhistory
      (fresh j) hfresh lower upper hprob

/-- One stopped-coordinate step when the fresh-kernel estimate is available
only on the geometrically valid set of stopped positions. -/
theorem atomEvent_succ_measure_mem_Icc_on
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath} {j : ℕ}
    (htau : IsStoppingTime incrementFiltration (tau j))
    (hhistory : IsMeasurableAtWithTopStopping (tau j)
      (atomEvent initial tau fresh j))
    (valid : Set Point)
    (hsupport : ∀ omega, omega ∈ atomEvent initial tau fresh j →
      tau j omega < ⊤ → stoppedPosition (tau j) omega ∈ valid)
    (hfresh : ∀ x, MeasurableSet (fresh j x))
    (lower upper : ℝ≥0∞)
    (hprob : ∀ x ∈ valid,
      fairSteps (fresh j x) ∈ Set.Icc lower upper) :
    fairSteps (atomEvent initial tau fresh (j + 1)) ∈
      Set.Icc
        (fairSteps (atomEvent initial tau fresh j ∩
          {omega | tau j omega < ⊤}) * lower)
        (fairSteps (atomEvent initial tau fresh j ∩
          {omega | tau j omega < ⊤}) * upper) := by
  simpa only [atomEvent_succ] using
    strongMarkov_withTop_stoppedPosition_bounds_on htau hhistory valid
      hsupport (fresh j) hfresh lower upper hprob

/-- Almost-sure finiteness removes the explicit finite-clock intersection
from the one-step bound. -/
theorem atomEvent_succ_measure_mem_Icc_of_ae_finite
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath} {j : ℕ}
    (htau : IsStoppingTime incrementFiltration (tau j))
    (hhistory : IsMeasurableAtWithTopStopping (tau j)
      (atomEvent initial tau fresh j))
    (hfinite : ∀ᵐ omega ∂fairSteps, tau j omega < ⊤)
    (hfresh : ∀ x, MeasurableSet (fresh j x))
    (lower upper : ℝ≥0∞)
    (hprob : ∀ x, fairSteps (fresh j x) ∈ Set.Icc lower upper) :
    fairSteps (atomEvent initial tau fresh (j + 1)) ∈
      Set.Icc
        (fairSteps (atomEvent initial tau fresh j) * lower)
        (fairSteps (atomEvent initial tau fresh j) * upper) := by
  have hcongr :
      (atomEvent initial tau fresh j ∩ {omega | tau j omega < ⊤} : Set StepPath)
        =ᵐ[fairSteps] atomEvent initial tau fresh j := by
    filter_upwards [hfinite] with omega homega
    exact propext (and_iff_left homega)
  have hstep := atomEvent_succ_measure_mem_Icc htau hhistory hfresh
    lower upper hprob
  simpa only [measure_congr hcongr] using hstep

/-- Localized one-step estimate with an almost-surely finite clock. -/
theorem atomEvent_succ_measure_mem_Icc_on_of_ae_finite
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath} {j : ℕ}
    (htau : IsStoppingTime incrementFiltration (tau j))
    (hhistory : IsMeasurableAtWithTopStopping (tau j)
      (atomEvent initial tau fresh j))
    (hfinite : ∀ᵐ omega ∂fairSteps, tau j omega < ⊤)
    (valid : Set Point)
    (hsupport : ∀ omega, omega ∈ atomEvent initial tau fresh j →
      tau j omega < ⊤ → stoppedPosition (tau j) omega ∈ valid)
    (hfresh : ∀ x, MeasurableSet (fresh j x))
    (lower upper : ℝ≥0∞)
    (hprob : ∀ x ∈ valid,
      fairSteps (fresh j x) ∈ Set.Icc lower upper) :
    fairSteps (atomEvent initial tau fresh (j + 1)) ∈
      Set.Icc
        (fairSteps (atomEvent initial tau fresh j) * lower)
        (fairSteps (atomEvent initial tau fresh j) * upper) := by
  have hcongr :
      (atomEvent initial tau fresh j ∩ {omega | tau j omega < ⊤} : Set StepPath)
        =ᵐ[fairSteps] atomEvent initial tau fresh j := by
    filter_upwards [hfinite] with omega homega
    exact propext (and_iff_left homega)
  have hstep := atomEvent_succ_measure_mem_Icc_on htau hhistory valid
    hsupport hfresh lower upper hprob
  simpa only [measure_congr hcongr] using hstep

/-- Finite iteration of the preceding one-step estimate.  The bounds may
depend on the coordinate but are uniform over its random stopped position. -/
theorem atomEvent_measure_mem_Icc_prod
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath}
    (htau : ∀ j, IsStoppingTime incrementFiltration (tau j))
    (hhistory : ∀ j, IsMeasurableAtWithTopStopping (tau j)
      (atomEvent initial tau fresh j))
    (hfinite : ∀ j, ∀ᵐ omega ∂fairSteps, tau j omega < ⊤)
    (hfresh : ∀ j x, MeasurableSet (fresh j x))
    (lower upper : ℕ → ℝ≥0∞)
    (hprob : ∀ j x, fairSteps (fresh j x) ∈ Set.Icc (lower j) (upper j)) :
    ∀ m, fairSteps (atomEvent initial tau fresh m) ∈
      Set.Icc
        (fairSteps initial * ∏ j ∈ Finset.range m, lower j)
        (fairSteps initial * ∏ j ∈ Finset.range m, upper j) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := atomEvent_succ_measure_mem_Icc_of_ae_finite
        (htau m) (hhistory m) (hfinite m) (hfresh m)
        (lower m) (upper m) (hprob m)
      constructor
      · calc
          fairSteps initial * ∏ j ∈ Finset.range (m + 1), lower j =
              (fairSteps initial * ∏ j ∈ Finset.range m, lower j) * lower m := by
                rw [Finset.prod_range_succ]
                ac_rfl
          _ ≤ fairSteps (atomEvent initial tau fresh m) * lower m :=
            by simpa [mul_comm] using mul_le_mul_right ih.1 (lower m)
          _ ≤ fairSteps (atomEvent initial tau fresh (m + 1)) := hstep.1
      · calc
          fairSteps (atomEvent initial tau fresh (m + 1)) ≤
              fairSteps (atomEvent initial tau fresh m) * upper m := hstep.2
          _ ≤ (fairSteps initial * ∏ j ∈ Finset.range m, upper j) * upper m :=
            by simpa [mul_comm] using mul_le_mul_right ih.2 (upper m)
          _ = fairSteps initial * ∏ j ∈ Finset.range (m + 1), upper j := by
            rw [Finset.prod_range_succ]
            ac_rfl

/-- Finite iteration with a coordinate-dependent set of geometrically valid
stopped positions.  This is the annular-shell form of the sequential atom
estimate. -/
theorem atomEvent_measure_mem_Icc_prod_on
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath}
    (htau : ∀ j, IsStoppingTime incrementFiltration (tau j))
    (hhistory : ∀ j, IsMeasurableAtWithTopStopping (tau j)
      (atomEvent initial tau fresh j))
    (hfinite : ∀ j, ∀ᵐ omega ∂fairSteps, tau j omega < ⊤)
    (valid : ℕ → Set Point)
    (hsupport : ∀ j omega, omega ∈ atomEvent initial tau fresh j →
      tau j omega < ⊤ → stoppedPosition (tau j) omega ∈ valid j)
    (hfresh : ∀ j x, MeasurableSet (fresh j x))
    (lower upper : ℕ → ℝ≥0∞)
    (hprob : ∀ j x, x ∈ valid j →
      fairSteps (fresh j x) ∈ Set.Icc (lower j) (upper j)) :
    ∀ m, fairSteps (atomEvent initial tau fresh m) ∈
      Set.Icc
        (fairSteps initial * ∏ j ∈ Finset.range m, lower j)
        (fairSteps initial * ∏ j ∈ Finset.range m, upper j) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := atomEvent_succ_measure_mem_Icc_on_of_ae_finite
        (htau m) (hhistory m) (hfinite m) (valid m) (hsupport m)
        (hfresh m) (lower m) (upper m) (hprob m)
      constructor
      · calc
          fairSteps initial * ∏ j ∈ Finset.range (m + 1), lower j =
              (fairSteps initial * ∏ j ∈ Finset.range m, lower j) * lower m := by
                rw [Finset.prod_range_succ]
                ac_rfl
          _ ≤ fairSteps (atomEvent initial tau fresh m) * lower m :=
            by simpa [mul_comm] using mul_le_mul_right ih.1 (lower m)
          _ ≤ fairSteps (atomEvent initial tau fresh (m + 1)) := hstep.1
      · calc
          fairSteps (atomEvent initial tau fresh (m + 1)) ≤
              fairSteps (atomEvent initial tau fresh m) * upper m := hstep.2
          _ ≤ (fairSteps initial * ∏ j ∈ Finset.range m, upper j) * upper m :=
            by simpa [mul_comm] using mul_le_mul_right ih.2 (upper m)
          _ = fairSteps initial * ∏ j ∈ Finset.range (m + 1), upper j := by
            rw [Finset.prod_range_succ]
            ac_rfl

/-- Finite iteration with hypotheses required only at the coordinates that
are actually traversed.  In particular, the zero-stage case carries no
artificial stopping-time data. -/
theorem atomEvent_measure_mem_Icc_prod_on_bounded
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath}
    (m : ℕ)
    (htau : ∀ j < m, IsStoppingTime incrementFiltration (tau j))
    (hhistory : ∀ j < m, IsMeasurableAtWithTopStopping (tau j)
      (atomEvent initial tau fresh j))
    (hfinite : ∀ j < m, ∀ᵐ omega ∂fairSteps, tau j omega < ⊤)
    (valid : ℕ → Set Point)
    (hsupport : ∀ j < m, ∀ omega, omega ∈ atomEvent initial tau fresh j →
      tau j omega < ⊤ → stoppedPosition (tau j) omega ∈ valid j)
    (hfresh : ∀ j < m, ∀ x, MeasurableSet (fresh j x))
    (lower upper : ℕ → ℝ≥0∞)
    (hprob : ∀ j < m, ∀ x, x ∈ valid j →
      fairSteps (fresh j x) ∈ Set.Icc (lower j) (upper j)) :
    fairSteps (atomEvent initial tau fresh m) ∈
      Set.Icc
        (fairSteps initial * ∏ j ∈ Finset.range m, lower j)
        (fairSteps initial * ∏ j ∈ Finset.range m, upper j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := atomEvent_succ_measure_mem_Icc_on_of_ae_finite
        (htau m (Nat.lt_succ_self m))
        (hhistory m (Nat.lt_succ_self m))
        (hfinite m (Nat.lt_succ_self m)) (valid m)
        (hsupport m (Nat.lt_succ_self m))
        (hfresh m (Nat.lt_succ_self m)) (lower m) (upper m)
        (hprob m (Nat.lt_succ_self m))
      have ih' := ih
        (fun j hj ↦ htau j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hhistory j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hfinite j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hsupport j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hfresh j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hprob j (hj.trans (Nat.lt_succ_self m)))
      constructor
      · calc
          fairSteps initial * ∏ j ∈ Finset.range (m + 1), lower j =
              (fairSteps initial * ∏ j ∈ Finset.range m, lower j) * lower m := by
                rw [Finset.prod_range_succ]
                ac_rfl
          _ ≤ fairSteps (atomEvent initial tau fresh m) * lower m :=
            by simpa [mul_comm] using mul_le_mul_right ih'.1 (lower m)
          _ ≤ fairSteps (atomEvent initial tau fresh (m + 1)) := hstep.1
      · calc
          fairSteps (atomEvent initial tau fresh (m + 1)) ≤
              fairSteps (atomEvent initial tau fresh m) * upper m := hstep.2
          _ ≤ (fairSteps initial * ∏ j ∈ Finset.range m, upper j) * upper m :=
            by simpa [mul_comm] using mul_le_mul_right ih'.2 (upper m)
          _ = fairSteps initial * ∏ j ∈ Finset.range (m + 1), upper j := by
            rw [Finset.prod_range_succ]
            ac_rfl

/-- Exact factorization is the degenerate case in which every stopped
position has the same fresh-tail probability. -/
theorem atomEvent_measure_eq_prod
    {initial : Set StepPath} {tau : ℕ → StepPath → WithTop ℕ}
    {fresh : ℕ → Point → Set StepPath}
    (htau : ∀ j, IsStoppingTime incrementFiltration (tau j))
    (hhistory : ∀ j, IsMeasurableAtWithTopStopping (tau j)
      (atomEvent initial tau fresh j))
    (hfinite : ∀ j, ∀ᵐ omega ∂fairSteps, tau j omega < ⊤)
    (hfresh : ∀ j x, MeasurableSet (fresh j x))
    (probability : ℕ → ℝ≥0∞)
    (hprob : ∀ j x, fairSteps (fresh j x) = probability j) (m : ℕ) :
    fairSteps (atomEvent initial tau fresh m) =
      fairSteps initial * ∏ j ∈ Finset.range m, probability j := by
  have hbounds := atomEvent_measure_mem_Icc_prod htau hhistory hfinite hfresh
    probability probability (fun j x ↦ by simp [hprob j x]) m
  exact le_antisymm hbounds.2 hbounds.1

end

end Erdos1165.SequentialStoppedAtoms
