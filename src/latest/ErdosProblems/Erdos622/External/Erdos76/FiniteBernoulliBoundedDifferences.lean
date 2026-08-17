/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos622.External.Erdos76.Kahn
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# Bounded differences for an explicit finite Bernoulli product

This file proves the moment-generating-function form of McDiarmid's
inequality directly for the explicit masses `FiniteNibble.bernoulliMass`.
It then derives upper and lower exponential tails.  The proof is a finite
induction over the ground set; the only analytic input is Mathlib's
two-point instance of Hoeffding's lemma.
-/

open Finset MeasureTheory Real ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteNibble

variable {E : Type*} [DecidableEq E]

/-- Expectation of a function of the explicit Bernoulli subset. -/
def bernoulliExpectation (U : Finset E) (p : E → ℝ) (F : Finset E → ℝ) : ℝ :=
  ∑ S ∈ U.powerset, bernoulliMass U p S * F S

/-- Total mass of outcomes on which `F` is at least `r`. -/
def bernoulliUpperTailMass (U : Finset E) (p : E → ℝ)
    (F : Finset E → ℝ) (r : ℝ) : ℝ :=
  ∑ S ∈ U.powerset with r ≤ F S, bernoulliMass U p S

/-- Total mass of outcomes on which `F` is at most `r`. -/
def bernoulliLowerTailMass (U : Finset E) (p : E → ℝ)
    (F : Finset E → ℝ) (r : ℝ) : ℝ :=
  ∑ S ∈ U.powerset with F S ≤ r, bernoulliMass U p S

/-- Coordinatewise bounded differences, stated using the canonical
representative `T` not containing the toggled coordinate. -/
def HasBoundedDifferences (U : Finset E) (F : Finset E → ℝ) (c : E → ℝ) : Prop :=
  ∀ e ∈ U, ∀ T ⊆ U.erase e, |F (insert e T) - F T| ≤ c e

private lemma bernoulliMass_notMem_insert {U T : Finset E} {p : E → ℝ} {e : E}
    (heU : e ∉ U) (hT : T ⊆ U) :
    bernoulliMass (insert e U) p T =
      (1 - p e) * bernoulliMass U p T := by
  have heT : e ∉ T := fun heT ↦ heU (hT heT)
  have hdiff : insert e U \ T = insert e (U \ T) := by
    ext x
    simp only [mem_sdiff, mem_insert]
    constructor
    · rintro ⟨hx | hx, hxT⟩
      · exact Or.inl hx
      · exact Or.inr ⟨hx, hxT⟩
    · rintro (hx | ⟨hxU, hxT⟩)
      · exact ⟨Or.inl hx, fun hxT ↦ heT (hx.symm ▸ hxT)⟩
      · exact ⟨Or.inr hxU, hxT⟩
  simp only [bernoulliMass, hdiff]
  rw [prod_insert]
  · ring
  · exact fun h ↦ heU (mem_sdiff.mp h).1

private lemma bernoulliMass_mem_insert {U T : Finset E} {p : E → ℝ} {e : E}
    (heU : e ∉ U) (hT : T ⊆ U) :
    bernoulliMass (insert e U) p (insert e T) =
      p e * bernoulliMass U p T := by
  simpa [erase_insert heU] using
    (bernoulliMass_insert (p := p) (mem_insert_self e U)
      (show T ⊆ (insert e U).erase e by simpa [erase_insert heU] using hT))

/-- Split an expectation according to the Bernoulli coordinate `e`. -/
lemma bernoulliExpectation_insert {U : Finset E} {p : E → ℝ}
    (F : Finset E → ℝ) {e : E} (heU : e ∉ U) :
    bernoulliExpectation (insert e U) p F =
      (1 - p e) * bernoulliExpectation U p F +
        p e * bernoulliExpectation U p (fun T ↦ F (insert e T)) := by
  rw [bernoulliExpectation, sum_powerset_insert heU]
  simp only [bernoulliExpectation]
  calc
    (∑ T ∈ U.powerset, bernoulliMass (insert e U) p T * F T) +
          ∑ T ∈ U.powerset,
            bernoulliMass (insert e U) p (insert e T) * F (insert e T) =
        (∑ T ∈ U.powerset, (1 - p e) * (bernoulliMass U p T * F T)) +
          ∑ T ∈ U.powerset, p e *
            (bernoulliMass U p T * F (insert e T)) := by
      apply congrArg₂ (fun x y : ℝ ↦ x + y)
      · apply sum_congr rfl
        intro T hT
        rw [bernoulliMass_notMem_insert heU (mem_powerset.mp hT)]
        ring
      · apply sum_congr rfl
        intro T hT
        rw [bernoulliMass_mem_insert heU (mem_powerset.mp hT)]
        ring
    _ = (1 - p e) * (∑ T ∈ U.powerset, bernoulliMass U p T * F T) +
          p e * (∑ T ∈ U.powerset,
            bernoulliMass U p T * F (insert e T)) := by
      simp only [mul_sum]

/-- The elementary two-point centered MGF estimate used at each induction
step.  It is Hoeffding's lemma specialized to a Bernoulli law. -/
private lemma two_point_hoeffding {q x₀ x₁ c s : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hc : |x₁ - x₀| ≤ c) :
    (1 - q) * exp (s * (x₀ - ((1 - q) * x₀ + q * x₁))) +
        q * exp (s * (x₁ - ((1 - q) * x₀ + q * x₁))) ≤
      exp (c ^ 2 * s ^ 2 / 8) := by
  let w : Bool → ℝ := fun b ↦ if b then q else 1 - q
  let X : Bool → ℝ := fun b ↦ if b then x₁ else x₀
  let μ : Measure Bool := Measure.sum fun b ↦ ENNReal.ofReal (w b) • Measure.dirac b
  have hw₀ : ∀ b, 0 ≤ w b := by
    intro b
    cases b <;> simp [w, hq₀, sub_nonneg.mpr hq₁]
  have hwsum : HasSum w 1 := by
    convert hasSum_fintype w using 1
    simp [w]
  letI : IsProbabilityMeasure μ :=
    HasSum.isProbabilityMeasure_sum_dirac hw₀ hwsum
  have hXmeas : AEMeasurable X μ := by fun_prop
  have hXrange : ∀ᵐ b ∂μ, X b ∈ Set.Icc (min x₀ x₁) (max x₀ x₁) := by
    filter_upwards [] with b
    cases b <;> simp [X]
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hXmeas hXrange
  have hmgf := hsub.mgf_le s
  have hintegral (f : Bool → ℝ) :
      ∫ b, f b ∂μ = (1 - q) * f false + q * f true := by
    simp only [μ]
    rw [integral_sum_dirac (f := f) (fun _ ↦ ENNReal.ofReal_ne_top)]
    simp [w, ENNReal.toReal_ofReal hq₀,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hq₁)]
    ring
  have hmean : μ[X] = (1 - q) * x₀ + q * x₁ := by
    rw [hintegral]
    simp [X]
  rw [ProbabilityTheory.mgf, hmean] at hmgf
  rw [hintegral] at hmgf
  simp only [X, Bool.false_eq_true, ↓reduceIte, Bool.true_eq] at hmgf
  calc
    (1 - q) * exp (s * (x₀ - ((1 - q) * x₀ + q * x₁))) +
          q * exp (s * (x₁ - ((1 - q) * x₀ + q * x₁))) ≤
        exp ((|max x₀ x₁ - min x₀ x₁| / 2) ^ 2 * s ^ 2 / 2) := hmgf
    _ = exp (|x₁ - x₀| ^ 2 * s ^ 2 / 8) := by
      congr 1
      rw [abs_of_nonneg (sub_nonneg.mpr (min_le_max : min x₀ x₁ ≤ max x₀ x₁)),
        max_sub_min_eq_abs]
      ring
    _ ≤ exp (c ^ 2 * s ^ 2 / 8) := by
      apply Real.exp_le_exp.mpr
      have habs₀ : 0 ≤ |x₁ - x₀| := abs_nonneg _
      have hc₀ : 0 ≤ c := habs₀.trans hc
      have hsquare : |x₁ - x₀| ^ 2 ≤ c ^ 2 := by nlinarith
      gcongr

private lemma averaged_boundedDifference {q x₀ x₁ y₀ y₁ c : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hx : |x₁ - x₀| ≤ c) (hy : |y₁ - y₀| ≤ c) :
    |((1 - q) * x₁ + q * y₁) - ((1 - q) * x₀ + q * y₀)| ≤ c := by
  rw [abs_le] at hx hy ⊢
  constructor <;> nlinarith

/-- McDiarmid's centered MGF estimate for an explicit finite Bernoulli
product.  The parameter is `(∑ e∈U, c e²) / 4`, hence the displayed
exponent `s² (∑ c e²) / 8`. -/
theorem sum_bernoulliMass_mul_exp_centered_le
    {U : Finset E} {p : E → ℝ} {F : Finset E → ℝ} {c : E → ℝ}
    (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1)
    (hbd : HasBoundedDifferences U F c) (s : ℝ) :
    ∑ S ∈ U.powerset, bernoulliMass U p S *
        exp (s * (F S - bernoulliExpectation U p F)) ≤
      exp (s ^ 2 * (∑ e ∈ U, c e ^ 2) / 8) := by
  induction U using Finset.induction_on generalizing F with
  | empty =>
      simp [bernoulliExpectation, bernoulliMass]
  | @insert e U heU ih =>
      let G : Finset E → ℝ := fun T ↦
        (1 - p e) * F T + p e * F (insert e T)
      have hq₀ : 0 ≤ p e := hp₀ e (mem_insert_self e U)
      have hq₁ : p e ≤ 1 := hp₁ e (mem_insert_self e U)
      have hmean : bernoulliExpectation (insert e U) p F =
          bernoulliExpectation U p G := by
        rw [bernoulliExpectation_insert F heU]
        simp only [G, bernoulliExpectation, mul_sum]
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro T _
        ring
      have hbdG : HasBoundedDifferences U G c := by
        intro i hiU T hT
        have hie : i ≠ e := fun hie ↦ heU (hie ▸ hiU)
        have hTbig : T ⊆ (insert e U).erase i := by
          intro x hx
          have hx' := mem_erase.mp (hT hx)
          exact mem_erase.mpr ⟨hx'.1, mem_insert_of_mem hx'.2⟩
        have heT : e ∉ T := by
          intro heT
          exact heU ((erase_subset i U) (hT heT))
        have heTbig : insert e T ⊆ (insert e U).erase i := by
          intro x hx
          rcases mem_insert.mp hx with hxe | hxT
          · exact mem_erase.mpr ⟨fun hxi ↦ hie (hxi.symm.trans hxe),
              mem_insert.mpr (Or.inl hxe)⟩
          · have hx' := mem_erase.mp (hT hxT)
            exact mem_erase.mpr ⟨hx'.1, mem_insert_of_mem hx'.2⟩
        have h₀ := hbd i (mem_insert_of_mem hiU) T hTbig
        have h₁ := hbd i (mem_insert_of_mem hiU) (insert e T) heTbig
        have hins : insert i (insert e T) = insert e (insert i T) := by
          ext x
          simp [or_comm, or_left_comm]
        rw [hins] at h₁
        change |((1 - p e) * F (insert i T) + p e * F (insert e (insert i T))) -
          ((1 - p e) * F T + p e * F (insert e T))| ≤ c i
        exact averaged_boundedDifference hq₀ hq₁ h₀ h₁
      have hih := ih (fun i hi ↦ hp₀ i (mem_insert_of_mem hi))
        (fun i hi ↦ hp₁ i (mem_insert_of_mem hi)) hbdG
      rw [hmean]
      rw [sum_powerset_insert heU]
      calc
        (∑ T ∈ U.powerset, bernoulliMass (insert e U) p T *
              exp (s * (F T - bernoulliExpectation U p G))) +
            ∑ T ∈ U.powerset, bernoulliMass (insert e U) p (insert e T) *
              exp (s * (F (insert e T) - bernoulliExpectation U p G)) =
          ∑ T ∈ U.powerset, bernoulliMass U p T *
            ((1 - p e) * exp (s * (F T - bernoulliExpectation U p G)) +
              p e * exp (s * (F (insert e T) - bernoulliExpectation U p G))) := by
            rw [← sum_add_distrib]
            apply sum_congr rfl
            intro T hT
            rw [bernoulliMass_notMem_insert heU (mem_powerset.mp hT),
              bernoulliMass_mem_insert heU (mem_powerset.mp hT)]
            ring
        _ ≤ ∑ T ∈ U.powerset, bernoulliMass U p T *
            (exp (s * (G T - bernoulliExpectation U p G)) *
              exp (c e ^ 2 * s ^ 2 / 8)) := by
          apply sum_le_sum
          intro T hT
          apply mul_le_mul_of_nonneg_left _
            (bernoulliMass_nonneg (mem_powerset.mp hT)
              (fun i hi ↦ hp₀ i (mem_insert_of_mem hi))
              (fun i hi ↦ hp₁ i (mem_insert_of_mem hi)))
          have htwo := two_point_hoeffding hq₀ hq₁
            (hbd e (mem_insert_self e U) T (by simpa [erase_insert heU] using
              (mem_powerset.mp hT))) (s := s)
          calc
            (1 - p e) * exp (s * (F T - bernoulliExpectation U p G)) +
                p e * exp (s * (F (insert e T) - bernoulliExpectation U p G)) =
              exp (s * (G T - bernoulliExpectation U p G)) *
                ((1 - p e) * exp (s * (F T - G T)) +
                  p e * exp (s * (F (insert e T) - G T))) := by
                have hfactor (x : ℝ) :
                    exp (s * (x - bernoulliExpectation U p G)) =
                      exp (s * (G T - bernoulliExpectation U p G)) *
                        exp (s * (x - G T)) := by
                  rw [← exp_add]
                  congr 1
                  ring
                rw [hfactor (F T), hfactor (F (insert e T))]
                ring
            _ ≤ exp (s * (G T - bernoulliExpectation U p G)) *
                exp (c e ^ 2 * s ^ 2 / 8) :=
              mul_le_mul_of_nonneg_left htwo (exp_nonneg _)
        _ = (∑ T ∈ U.powerset, bernoulliMass U p T *
              exp (s * (G T - bernoulliExpectation U p G))) *
            exp (c e ^ 2 * s ^ 2 / 8) := by
          rw [sum_mul]
          apply sum_congr rfl
          intro T _
          ring
        _ ≤ exp (s ^ 2 * (∑ i ∈ U, c i ^ 2) / 8) *
            exp (c e ^ 2 * s ^ 2 / 8) :=
          mul_le_mul_of_nonneg_right hih (exp_nonneg _)
        _ = exp (s ^ 2 * (∑ i ∈ insert e U, c i ^ 2) / 8) := by
          rw [← exp_add, sum_insert heU]
          congr 1
          ring

private lemma boundedDifference_nonneg {U : Finset E} {F : Finset E → ℝ}
    {c : E → ℝ} (hbd : HasBoundedDifferences U F c) {e : E} (heU : e ∈ U) :
    0 ≤ c e := by
  exact (abs_nonneg (F {e} - F ∅)).trans
    (by simpa using hbd e heU ∅ (by simp))

private lemma bernoulliUpperTailMass_le_one
    {U : Finset E} {p : E → ℝ} {F : Finset E → ℝ} {r : ℝ}
    (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1) :
    bernoulliUpperTailMass U p F r ≤ 1 := by
  calc
    bernoulliUpperTailMass U p F r ≤
        ∑ S ∈ U.powerset, bernoulliMass U p S := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun S hS _ ↦ bernoulliMass_nonneg (mem_powerset.mp hS) hp₀ hp₁)
    _ = 1 := sum_bernoulliMass U p

private lemma exp_mul_upperTailMass_le_mgf
    {U : Finset E} {p : E → ℝ} {F : Finset E → ℝ} {t s : ℝ}
    (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1)
    (hs : 0 ≤ s) :
    exp (s * t) *
        bernoulliUpperTailMass U p F (bernoulliExpectation U p F + t) ≤
      ∑ S ∈ U.powerset, bernoulliMass U p S *
        exp (s * (F S - bernoulliExpectation U p F)) := by
  rw [bernoulliUpperTailMass, mul_sum]
  calc
    ∑ S ∈ U.powerset with bernoulliExpectation U p F + t ≤ F S,
          exp (s * t) * bernoulliMass U p S =
        ∑ S ∈ U.powerset with bernoulliExpectation U p F + t ≤ F S,
          bernoulliMass U p S * exp (s * t) := by
      apply sum_congr rfl
      intro S _
      ring
    _ ≤ ∑ S ∈ U.powerset with bernoulliExpectation U p F + t ≤ F S,
          bernoulliMass U p S * exp (s * (F S - bernoulliExpectation U p F)) := by
      apply sum_le_sum
      intro S hS
      apply mul_le_mul_of_nonneg_left _
        (bernoulliMass_nonneg (mem_powerset.mp (mem_filter.mp hS).1) hp₀ hp₁)
      apply Real.exp_le_exp.mpr
      have ht := (mem_filter.mp hS).2
      nlinarith
    _ ≤ ∑ S ∈ U.powerset, bernoulliMass U p S *
          exp (s * (F S - bernoulliExpectation U p F)) := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun S hS _ ↦ mul_nonneg
          (bernoulliMass_nonneg (mem_powerset.mp hS) hp₀ hp₁) (exp_nonneg _))

/-- Upper-tail McDiarmid inequality for the explicit product mass. -/
theorem bernoulliUpperTailMass_le_exp
    {U : Finset E} {p : E → ℝ} {F : Finset E → ℝ} {c : E → ℝ} {t : ℝ}
    (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1)
    (hbd : HasBoundedDifferences U F c) (ht : 0 ≤ t) :
    bernoulliUpperTailMass U p F (bernoulliExpectation U p F + t) ≤
      exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) := by
  let C : ℝ := ∑ e ∈ U, c e ^ 2
  have hC₀ : 0 ≤ C := by
    exact sum_nonneg fun e he ↦ sq_nonneg (c e)
  by_cases hC : C = 0
  · simpa [C, hC] using bernoulliUpperTailMass_le_one hp₀ hp₁
  · have hCpos : 0 < C := lt_of_le_of_ne hC₀ (Ne.symm hC)
    let s : ℝ := 4 * t / C
    have hs : 0 ≤ s := div_nonneg (mul_nonneg (by norm_num) ht) hC₀
    have hprod :
        exp (s * t) *
            bernoulliUpperTailMass U p F (bernoulliExpectation U p F + t) ≤
          exp (s ^ 2 * C / 8) := by
      exact (exp_mul_upperTailMass_le_mgf hp₀ hp₁ hs).trans
        (by simpa only [C] using
          sum_bernoulliMass_mul_exp_centered_le hp₀ hp₁ hbd s)
    calc
      bernoulliUpperTailMass U p F (bernoulliExpectation U p F + t) =
          exp (-s * t) * (exp (s * t) *
            bernoulliUpperTailMass U p F (bernoulliExpectation U p F + t)) := by
        rw [← mul_assoc, ← exp_add]
        ring_nf
        simp
      _ ≤ exp (-s * t) * exp (s ^ 2 * C / 8) :=
        mul_le_mul_of_nonneg_left hprod (exp_nonneg _)
      _ = exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) := by
        rw [← exp_add]
        congr 1
        change -s * t + s ^ 2 * C / 8 = -2 * t ^ 2 / C
        dsimp [s]
        field_simp
        ring

private lemma bernoulliExpectation_neg (U : Finset E) (p : E → ℝ)
    (F : Finset E → ℝ) :
    bernoulliExpectation U p (fun S ↦ -F S) = -bernoulliExpectation U p F := by
  simp [bernoulliExpectation, mul_neg, sum_neg_distrib]

/-- Lower-tail McDiarmid inequality for the explicit product mass. -/
theorem bernoulliLowerTailMass_le_exp
    {U : Finset E} {p : E → ℝ} {F : Finset E → ℝ} {c : E → ℝ} {t : ℝ}
    (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1)
    (hbd : HasBoundedDifferences U F c) (ht : 0 ≤ t) :
    bernoulliLowerTailMass U p F (bernoulliExpectation U p F - t) ≤
      exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) := by
  let G : Finset E → ℝ := fun S ↦ -F S
  have hbdG : HasBoundedDifferences U G c := by
    intro e he T hT
    simpa only [G, neg_sub_neg, abs_sub_comm] using hbd e he T hT
  have h := bernoulliUpperTailMass_le_exp hp₀ hp₁ hbdG ht
  have htail :
      bernoulliLowerTailMass U p F (bernoulliExpectation U p F - t) =
        bernoulliUpperTailMass U p G (bernoulliExpectation U p G + t) := by
    simp only [bernoulliLowerTailMass, bernoulliUpperTailMass]
    congr 1
    ext S
    simp only [mem_filter, G, bernoulliExpectation_neg]
    constructor <;> rintro ⟨hSU, hineq⟩ <;> exact ⟨hSU, by linarith⟩
  rw [htail]
  exact h

/-- If the exponential upper-tail bound is strictly below one, at least one
actual subset realizes the corresponding strict upper bound. -/
theorem exists_sample_lt_expectation_add
    {U : Finset E} {p : E → ℝ} {F : Finset E → ℝ} {c : E → ℝ} {t : ℝ}
    (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1)
    (hbd : HasBoundedDifferences U F c) (ht : 0 < t)
    (hC : 0 < ∑ e ∈ U, c e ^ 2) :
    ∃ S ⊆ U, F S < bernoulliExpectation U p F + t := by
  have htail := bernoulliUpperTailMass_le_exp hp₀ hp₁ hbd ht.le
  have hexp : exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) < 1 := by
    rw [exp_lt_one_iff]
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) ht2) hC
  by_contra h
  push Not at h
  have hall : ∀ S ∈ U.powerset, bernoulliExpectation U p F + t ≤ F S := by
    intro S hS
    exact h S (mem_powerset.mp hS)
  have hfilter : U.powerset.filter
      (fun S ↦ bernoulliExpectation U p F + t ≤ F S) = U.powerset := by
    exact filter_eq_self.mpr hall
  have htail_one :
      bernoulliUpperTailMass U p F (bernoulliExpectation U p F + t) = 1 := by
    rw [bernoulliUpperTailMass, hfilter, sum_bernoulliMass]
  rw [htail_one] at htail
  exact (htail.trans_lt hexp).false

end FiniteNibble

end

end Erdos76
