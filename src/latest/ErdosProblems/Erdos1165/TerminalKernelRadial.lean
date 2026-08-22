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

import ErdosProblems.Erdos1165.SharpAnnulusHarnack
import ErdosProblems.Erdos1165.AppendixLocalTimeTransfer

/-!
# From one-hit Harnack to terminal Bernoulli--geometric kernels

This module supplies the finite-vector bridge between the sharp annular
one-hit comparison and the terminal local-time kernel.  Conditional on its
entrance point, one terminal excursion has the Bernoulli--positive-geometric
law `AppendixLocalTime.visitMass`.  A Harnack comparison for the Bernoulli
hit parameter therefore compares every one-excursion visit-count atom.  The
product comparison is then summed over an arbitrary terminal-success event.

The actual stopped-walk disintegration into the finite entrance vector and
these conditionally independent visit counts remains a separate strong-Markov
identity: this file states no such identity without its path-law hypotheses.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.TerminalKernelRadial

noncomputable section

/-- The product law of terminal-excursion visit counts when the hit
probability can vary with both the excursion and its entrance datum. -/
def varyingVisitMeasure {Entrance : Type*} {m : ℕ}
    (hit : Fin m → Entrance → ℝ) (escape : Fin m → ℝ)
    (hhit0 : ∀ j u, 0 ≤ hit j u) (hhit1 : ∀ j u, hit j u ≤ 1)
    (hescape0 : ∀ j, 0 < escape j) (hescape1 : ∀ j, escape j ≤ 1)
    (u : Fin m → Entrance) : Measure (Fin m → ℕ) :=
  Measure.pi fun j ↦
    (AppendixLocalTime.visitLaw (hit j (u j)) (escape j)
      (hhit0 j (u j)) (hhit1 j (u j)) (hescape0 j) (hescape1 j)).toMeasure

noncomputable instance varyingVisitMeasure.instIsProbabilityMeasure
    {Entrance : Type*} {m : ℕ}
    (hit : Fin m → Entrance → ℝ) (escape : Fin m → ℝ)
    (hhit0 : ∀ j u, 0 ≤ hit j u) (hhit1 : ∀ j u, hit j u ≤ 1)
    (hescape0 : ∀ j, 0 < escape j) (hescape1 : ∀ j, escape j ≤ 1)
    (u : Fin m → Entrance) :
    IsProbabilityMeasure
      (varyingVisitMeasure hit escape hhit0 hhit1 hescape0 hescape1 u) := by
  unfold varyingVisitMeasure
  infer_instance

/-- Probability of an arbitrary measurable terminal visit-vector event under
the entrance-dependent Bernoulli--geometric product law. -/
def terminalVisitKernel {Entrance : Type*} {m : ℕ}
    (hit : Fin m → Entrance → ℝ) (escape : Fin m → ℝ)
    (hhit0 : ∀ j u, 0 ≤ hit j u) (hhit1 : ∀ j u, hit j u ≤ 1)
    (hescape0 : ∀ j, 0 < escape j) (hescape1 : ∀ j, escape j ≤ 1)
    (success : Set (Fin m → ℕ)) (u : Fin m → Entrance) : ℝ :=
  (varyingVisitMeasure hit escape hhit0 hhit1 hescape0 hescape1 u).real success

/-- If the hit probability is at most one half, multiplicative Harnack for
the hit event also compares the zero-visit atom.  Positive visit-count atoms
are simply the hit probability times an entrance-independent geometric
factor. -/
theorem visitMass_conditionStar
    {Entrance : Type*} [Fintype Entrance]
    {epsilon p : ℝ} {hit : Entrance → ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hhit0 : ∀ u, 0 ≤ hit u) (hhitHalf : ∀ u, hit u ≤ 1 / 2)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hstar : AppendixDecoupling.ConditionStar epsilon hit) (k : ℕ) :
    AppendixDecoupling.ConditionStar epsilon
      (fun u ↦ AppendixLocalTime.visitMass (hit u) p k) := by
  intro y z
  have hy0 := hhit0 y
  have hz0 := hhit0 z
  have hyHalf := hhitHalf y
  have hzHalf := hhitHalf z
  have hhit := hstar y z
  cases k with
  | zero =>
      simp only [AppendixLocalTime.visitMass_zero]
      constructor <;> nlinarith
  | succ k =>
      change
        (1 - epsilon) * AppendixLocalTime.visitMass (hit y) p (k + 1) ≤
            AppendixLocalTime.visitMass (hit z) p (k + 1) ∧
          AppendixLocalTime.visitMass (hit z) p (k + 1) ≤
            (1 + epsilon) * AppendixLocalTime.visitMass (hit y) p (k + 1)
      rw [AppendixLocalTime.visitMass_succ_formula,
        AppendixLocalTime.visitMass_succ_formula]
      have hgeom : 0 ≤ p * (1 - p) ^ k :=
        mul_nonneg hp0.le (pow_nonneg (sub_nonneg.mpr hp1) _)
      constructor
      · nlinarith
      · nlinarith

private theorem varyingVisitMeasure_singleton
    {Entrance : Type*} {m : ℕ}
    (hit : Fin m → Entrance → ℝ) (escape : Fin m → ℝ)
    (hhit0 : ∀ j u, 0 ≤ hit j u) (hhit1 : ∀ j u, hit j u ≤ 1)
    (hescape0 : ∀ j, 0 < escape j) (hescape1 : ∀ j, escape j ≤ 1)
    (u : Fin m → Entrance) (v : Fin m → ℕ) :
    varyingVisitMeasure hit escape hhit0 hhit1 hescape0 hescape1 u {v} =
      ∏ j, ENNReal.ofReal
        (AppendixLocalTime.visitMass (hit j (u j)) (escape j) (v j)) := by
  rw [varyingVisitMeasure, Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact AppendixLocalTime.visitLaw_apply _ _ _ _ _ _ _

private theorem measure_eq_tsum_singletons_of_countable
    {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (mu : Measure α) (s : Set α) :
    mu s = ∑' x : s, mu {x.1} := by
  symm
  simpa only [preimage_id] using
    (tsum_measure_preimage_singleton (μ := mu) (f := id)
      (Set.to_countable s) (fun _ _ ↦ measurableSet_singleton _))

/-- An arbitrary terminal visit-vector event has the same product Harnack
comparison as its individual atoms.  This is the summation step needed for
the Bernoulli--geometric terminal-success kernel. -/
theorem terminalVisitKernel_mem_Icc_power
    {Entrance : Type*} [Fintype Entrance] {m : ℕ}
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hit : Fin m → Entrance → ℝ) (escape : Fin m → ℝ)
    (hhit0 : ∀ j u, 0 ≤ hit j u) (hhitHalf : ∀ j u, hit j u ≤ 1 / 2)
    (hescape0 : ∀ j, 0 < escape j) (hescape1 : ∀ j, escape j ≤ 1)
    (hstar : ∀ j, AppendixDecoupling.ConditionStar epsilon (hit j))
    (success : Set (Fin m → ℕ)) (reference u : Fin m → Entrance) :
    terminalVisitKernel hit escape hhit0
        (fun j a ↦ (hhitHalf j a).trans (by norm_num))
        hescape0 hescape1 success u ∈
      Set.Icc
        ((1 - epsilon) ^ m *
          terminalVisitKernel hit escape hhit0
            (fun j a ↦ (hhitHalf j a).trans (by norm_num))
            hescape0 hescape1 success reference)
        ((1 + epsilon) ^ m *
          terminalVisitKernel hit escape hhit0
            (fun j a ↦ (hhitHalf j a).trans (by norm_num))
            hescape0 hescape1 success reference) := by
  let hhit1 : ∀ j u, hit j u ≤ 1 :=
    fun j u ↦ (hhitHalf j u).trans (by norm_num)
  let muU := varyingVisitMeasure hit escape hhit0 hhit1 hescape0 hescape1 u
  let muR := varyingVisitMeasure hit escape hhit0 hhit1 hescape0 hescape1 reference
  have hfacLower : 0 ≤ (1 - epsilon) ^ m :=
    pow_nonneg (sub_nonneg.mpr hepsilon1) _
  have hfacUpper : 0 ≤ (1 + epsilon) ^ m :=
    pow_nonneg (by linarith) _
  have hmass0 : ∀ j a k,
      0 ≤ AppendixLocalTime.visitMass (hit j a) (escape j) k := by
    intro j a k
    exact AppendixLocalTime.visitMass_nonneg (hhit0 j a) (hhit1 j a)
      (hescape0 j).le (hescape1 j) k
  have hatomReal (w : Fin m → ℕ) :
      (∏ j, AppendixLocalTime.visitMass
          (hit j (u j)) (escape j) (w j)) ∈
        Set.Icc
          ((1 - epsilon) ^ m *
            ∏ j, AppendixLocalTime.visitMass
              (hit j (reference j)) (escape j) (w j))
          ((1 + epsilon) ^ m *
            ∏ j, AppendixLocalTime.visitMass
              (hit j (reference j)) (escape j) (w j)) := by
    let atom : Fin m → Entrance → ℝ := fun j a ↦
      AppendixLocalTime.visitMass (hit j a) (escape j) (w j)
    have hatomStar : ∀ j, AppendixDecoupling.ConditionStar epsilon (atom j) := by
      intro j
      exact visitMass_conditionStar hepsilon0 hepsilon1
        (hhit0 j) (hhitHalf j) (hescape0 j) (hescape1 j) (hstar j) (w j)
    have hbounds : ∀ j a, atom j a ∈ Set.Icc
        ((1 - epsilon) * atom j (reference j))
        ((1 + epsilon) * atom j (reference j)) := by
      intro j a
      exact hatomStar j (reference j) a
    have hprod := AppendixDecoupling.productKernel_mem_Icc
      (q := atom)
      (lower := fun j ↦ (1 - epsilon) * atom j (reference j))
      (upper := fun j ↦ (1 + epsilon) * atom j (reference j))
      (fun j ↦ mul_nonneg (sub_nonneg.mpr hepsilon1)
        (hmass0 j (reference j) (w j))) hbounds u
    simpa [AppendixDecoupling.productKernel, atom,
      Finset.prod_mul_distrib] using hprod
  have hatomENN (w : Fin m → ℕ) :
      ENNReal.ofReal ((1 - epsilon) ^ m) * muR {w} ≤ muU {w} ∧
        muU {w} ≤ ENNReal.ofReal ((1 + epsilon) ^ m) * muR {w} := by
    have hreal := hatomReal w
    have hprod0 : 0 ≤ ∏ j, AppendixLocalTime.visitMass
        (hit j (reference j)) (escape j) (w j) :=
      Finset.prod_nonneg fun j _ ↦ hmass0 j (reference j) (w j)
    have hliftLower := ENNReal.ofReal_le_ofReal hreal.1
    have hliftUpper := ENNReal.ofReal_le_ofReal hreal.2
    dsimp only [muU, muR]
    rw [varyingVisitMeasure_singleton, varyingVisitMeasure_singleton,
      ← ENNReal.ofReal_prod_of_nonneg
        (fun j _ ↦ hmass0 j (u j) (w j)),
      ← ENNReal.ofReal_prod_of_nonneg
        (fun j _ ↦ hmass0 j (reference j) (w j))]
    constructor
    · simpa only [ENNReal.ofReal_mul hfacLower] using hliftLower
    · simpa only [ENNReal.ofReal_mul hfacUpper] using hliftUpper
  have hsums := AppendixDecoupling.tsum_comparison
    (ENNReal.ofReal ((1 - epsilon) ^ m))
    (ENNReal.ofReal ((1 + epsilon) ^ m))
    (fun w : success ↦ muU {w.1}) (fun w : success ↦ muR {w.1})
    (fun w ↦ hatomENN w.1)
  have hmeasure :
      ENNReal.ofReal ((1 - epsilon) ^ m) * muR success ≤ muU success ∧
        muU success ≤ ENNReal.ofReal ((1 + epsilon) ^ m) * muR success := by
    simpa only [← measure_eq_tsum_singletons_of_countable muU success,
      ← measure_eq_tsum_singletons_of_countable muR success] using hsums
  have hlowerReal := ENNReal.toReal_mono (measure_ne_top muU success) hmeasure.1
  have hupperTop :
      ENNReal.ofReal ((1 + epsilon) ^ m) * muR success ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top muR success)
  have hupperReal := ENNReal.toReal_mono hupperTop hmeasure.2
  change
    (varyingVisitMeasure hit escape hhit0 hhit1 hescape0 hescape1 u).real success ∈
      Set.Icc
        ((1 - epsilon) ^ m *
          (varyingVisitMeasure hit escape hhit0 hhit1 hescape0 hescape1 reference).real
            success)
        ((1 + epsilon) ^ m *
          (varyingVisitMeasure hit escape hhit0 hhit1 hescape0 hescape1 reference).real
            success)
  constructor
  · simpa [measureReal_def, ENNReal.toReal_ofReal hfacLower] using hlowerReal
  · simpa [measureReal_def, ENNReal.toReal_ofReal hfacUpper] using hupperReal

/-- Linearized finite-vector comparison.  A one-excursion error `epsilon`
produces the symmetric terminal-kernel error `2 m epsilon`. -/
theorem terminalKernelComparison_of_visitHit_conditionStar
    {Entrance : Type*} [Fintype Entrance] {m : ℕ}
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hit : Fin m → Entrance → ℝ) (escape : Fin m → ℝ)
    (hhit0 : ∀ j u, 0 ≤ hit j u) (hhitHalf : ∀ j u, hit j u ≤ 1 / 2)
    (hescape0 : ∀ j, 0 < escape j) (hescape1 : ∀ j, escape j ≤ 1)
    (hstar : ∀ j, AppendixDecoupling.ConditionStar epsilon (hit j))
    (success : Set (Fin m → ℕ)) (reference : Fin m → Entrance)
    (hsmall : (1 + epsilon) ^ m ≤ 2) :
    AppendixLocalTimeTransfer.TerminalKernelComparison
      (2 * (m : ℝ) * epsilon)
      (terminalVisitKernel hit escape hhit0
        (fun j a ↦ (hhitHalf j a).trans (by norm_num))
        hescape0 hescape1 success reference)
      (terminalVisitKernel hit escape hhit0
        (fun j a ↦ (hhitHalf j a).trans (by norm_num))
        hescape0 hescape1 success) := by
  intro u
  have hpower := terminalVisitKernel_mem_Icc_power hepsilon0 hepsilon1
    hit escape hhit0 hhitHalf hescape0 hescape1 hstar success reference u
  have href0 : 0 ≤ terminalVisitKernel hit escape hhit0
      (fun j a ↦ (hhitHalf j a).trans (by norm_num))
      hescape0 hescape1 success reference := measureReal_nonneg
  have hlowerFactor : 1 - 2 * (m : ℝ) * epsilon ≤ (1 - epsilon) ^ m := by
    have hbern := AppendixDecoupling.one_sub_nat_mul_le_pow_one_sub hepsilon1 m
    have hm : 0 ≤ (m : ℝ) * epsilon := mul_nonneg (Nat.cast_nonneg m) hepsilon0
    linarith
  have hupperFactor : (1 + epsilon) ^ m ≤ 1 + 2 * (m : ℝ) * epsilon :=
    AppendixDecoupling.pow_one_add_le_one_add_two_nat_mul hepsilon0 hsmall
  exact ⟨
    (mul_le_mul_of_nonneg_right hlowerFactor href0).trans hpower.1,
    hpower.2.trans (mul_le_mul_of_nonneg_right hupperFactor href0)⟩

/-- At a reference entrance vector with constant hit and escape parameters,
the varying product law is definitionally the iid law used by
`AppendixLocalTime`. -/
theorem terminalVisitKernel_reference_eq_iid
    {Entrance : Type*} {m : ℕ}
    (hit : Fin m → Entrance → ℝ) (escape : Fin m → ℝ)
    (hhit0 : ∀ j u, 0 ≤ hit j u) (hhit1 : ∀ j u, hit j u ≤ 1)
    (hescape0 : ∀ j, 0 < escape j) (hescape1 : ∀ j, escape j ≤ 1)
    (reference : Fin m → Entrance) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hrefHit : ∀ j, hit j (reference j) = q)
    (hrefEscape : ∀ j, escape j = p)
    (success : Set (Fin m → ℕ)) :
    terminalVisitKernel hit escape hhit0 hhit1 hescape0 hescape1 success reference =
      (AppendixLocalTime.iidVisitMeasure m q p hq0 hq1 hp0 hp1).real success := by
  unfold terminalVisitKernel varyingVisitMeasure AppendixLocalTime.iidVisitMeasure
  congr 2
  funext j
  simp only [hrefHit j, hrefEscape j]

/-- Concrete Appendix reference-law specialization.  It converts a uniform
one-hit `ConditionStar` estimate into the exact `TerminalKernelComparison`
consumed by `AppendixTerminalThick`, for the threshold event used in (A.7). -/
theorem terminalKernelComparison_referenceSuccess_of_visitHit_conditionStar
    {Entrance : Type*} [Fintype Entrance]
    {scale : ℕ} {profileDelta thickDelta q p epsilon : ℝ}
    (hit : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
      Entrance → ℝ)
    (hhit0 : ∀ j u, 0 ≤ hit j u) (hhitHalf : ∀ j u, hit j u ≤ 1 / 2)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hstar : ∀ j, AppendixDecoupling.ConditionStar epsilon (hit j))
    (reference : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) →
      Entrance)
    (hrefHit : ∀ j, hit j (reference j) = q)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsmall : (1 + epsilon) ^
      AppendixLocalTime.requiredTerminalCount scale profileDelta ≤ 2) :
    AppendixLocalTimeTransfer.TerminalKernelComparison
      (2 * (AppendixLocalTime.requiredTerminalCount scale profileDelta : ℝ) * epsilon)
      (AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta)
      (terminalVisitKernel hit (fun _ ↦ p) hhit0
        (fun j a ↦ (hhitHalf j a).trans (by norm_num))
        (fun _ ↦ hp0) (fun _ ↦ hp1)
        {v | ThickPoint.thickThreshold scale thickDelta ≤
          AppendixLocalTime.totalVisits v}) := by
  let success : Set
      (Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ) :=
    {v | ThickPoint.thickThreshold scale thickDelta ≤
      AppendixLocalTime.totalVisits v}
  have hcompare := terminalKernelComparison_of_visitHit_conditionStar
    hepsilon0 hepsilon1 hit (fun _ ↦ p) hhit0 hhitHalf
    (fun _ ↦ hp0) (fun _ ↦ hp1) hstar success reference hsmall
  have href : terminalVisitKernel hit (fun _ ↦ p) hhit0
      (fun j a ↦ (hhitHalf j a).trans (by norm_num))
      (fun _ ↦ hp0) (fun _ ↦ hp1) success reference =
      AppendixLocalTimeTransfer.referenceTerminalSuccessProbability
        scale profileDelta q p hq0 hq1 hp0 hp1 thickDelta := by
    exact terminalVisitKernel_reference_eq_iid hit (fun _ ↦ p) hhit0
      (fun j a ↦ (hhitHalf j a).trans (by norm_num))
      (fun _ ↦ hp0) (fun _ ↦ hp1) reference q p hq0 hq1 hp0 hp1
      hrefHit (fun _ ↦ rfl) success
  simpa only [success, href] using hcompare

end

end Erdos1165.TerminalKernelRadial
