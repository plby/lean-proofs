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

import ErdosProblems.Erdos1165.ThickPoint
import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.NegativeBinomial

/-!
# The terminal-excursion local-time estimate in the HLOZ appendix

This file isolates the probability calculation in the proof of equation
(A.7) of Hao--Li--Okada--Zheng.  During one terminal excursion, the number of
visits to the centre is zero unless the excursion hits the centre.  Conditional
on a hit, it is one plus a geometric number of returns.  Thus its exact law is
a Bernoulli variable times an independent positive-geometric variable.

We give the exact mass, normalization, first two moments, and the finite-iid
Chebyshev estimate used to show that a successful terminal excursion profile
produces the desired local time with high probability.  The Harnack comparison
which transfers this calculation to excursions with varying entrance points is
kept in `AppendixDecoupling`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.AppendixLocalTime

noncomputable section

/-! ## One excursion: Bernoulli times positive geometric -/

/-- Mass of the number of visits to the centre in one excursion.  Here `q` is
the probability to hit the centre and `p` is the probability to escape before
the next return after a visit. -/
def visitMass (q p : ℝ) : ℕ → ℝ
  | 0 => 1 - q
  | k + 1 => q * NegativeBinomial.mass p 1 k

@[simp] lemma visitMass_zero (q p : ℝ) : visitMass q p 0 = 1 - q := rfl

@[simp] lemma visitMass_succ (q p : ℝ) (k : ℕ) :
    visitMass q p (k + 1) = q * NegativeBinomial.mass p 1 k := rfl

/-- The positive part is exactly `q p (1-p)^k`: first hit the centre, then
make `k` returns before the first escape. -/
lemma visitMass_succ_formula (q p : ℝ) (k : ℕ) :
    visitMass q p (k + 1) = q * p * (1 - p) ^ k := by
  simp [visitMass, NegativeBinomial.mass, NegativeBinomial.coefficient]
  ring

lemma visitMass_nonneg {q p : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ visitMass q p k := by
  cases k with
  | zero => simp [visitMass, sub_nonneg.mpr hq1]
  | succ k =>
      exact mul_nonneg hq0 (NegativeBinomial.mass_nonneg hp0 hp1 1 k)

lemma hasSum_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (visitMass q p) 1 := by
  have htail := (NegativeBinomial.hasSum_mass hp0 hp1 (show 0 < (1 : ℕ) by omega)).mul_left q
  have hshift : HasSum (fun k : ℕ => visitMass q p (k + 1)) q := by
    simpa only [visitMass_succ, mul_one] using htail
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, visitMass_zero, sub_sub_cancel] using hshift

lemma summable_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Summable (visitMass q p) := (hasSum_visitMass hp0 hp1).summable

@[simp] lemma tsum_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' k, visitMass q p k = 1 := (hasSum_visitMass hp0 hp1).tsum_eq

/-- The exact Bernoulli--positive-geometric visit-count law. -/
noncomputable def visitLaw (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (visitMass q p k), by
    apply ENNReal.hasSum_coe.mpr
    simpa using
      (hasSum_visitMass hp0 hp1).toNNReal (visitMass_nonneg hq0 hq1 hp0.le hp1)⟩

@[simp] lemma visitLaw_apply (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    visitLaw q p hq0 hq1 hp0 hp1 k = ENNReal.ofReal (visitMass q p k) := rfl

@[simp] lemma visitLaw_apply_zero (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    visitLaw q p hq0 hq1 hp0 hp1 0 = ENNReal.ofReal (1 - q) := rfl

/-- Exact product formula: a positive visit count requires the Bernoulli hit,
and, after that hit, its number of further returns has the one-success
negative-binomial (equivalently geometric) law. -/
lemma visitLaw_apply_succ_eq_bernoulli_mul_geometric
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    visitLaw q p hq0 hq1 hp0 hp1 (k + 1) =
      ENNReal.ofReal q * NegativeBinomial.law p hp0 hp1 1 (by omega) k := by
  rw [visitLaw_apply, visitMass_succ, NegativeBinomial.law_apply,
    ENNReal.ofReal_mul hq0]

/-! ## Exact moments -/

/-- A positive-geometric variable with escape parameter `p` has mean `1/p`. -/
lemma hasSum_positiveGeometric_first {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * NegativeBinomial.mass p 1 k)
      (1 / p) := by
  have h0 := NegativeBinomial.hasSum_mass hp0 hp1 (show 0 < (1 : ℕ) by omega)
  have h1 := NegativeBinomial.hasSum_weighted_mass hp0 hp1
    (show 0 < (1 : ℕ) by omega)
  have h := h1.add h0
  have heq :
      (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * NegativeBinomial.mass p 1 k) =
        (fun k : ℕ => (k : ℝ) * NegativeBinomial.mass p 1 k +
          NegativeBinomial.mass p 1 k) := by
    funext k
    push_cast
    ring
  rw [heq]
  convert h using 1
  field_simp
  ring

/-- A positive-geometric variable with escape parameter `p` has raw second
moment `(2-p)/p²`. -/
lemma hasSum_positiveGeometric_second {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2) *
      NegativeBinomial.mass p 1 k) ((2 - p) / p ^ 2) := by
  have h0 := NegativeBinomial.hasSum_mass hp0 hp1 (show 0 < (1 : ℕ) by omega)
  have h1 := NegativeBinomial.hasSum_weighted_mass hp0 hp1
    (show 0 < (1 : ℕ) by omega)
  have h2 := NegativeBinomial.hasSum_square_mass hp0 hp1
    (show 0 < (1 : ℕ) by omega)
  have h := (h2.add (h1.mul_left 2)).add h0
  have heq :
      (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2) *
          NegativeBinomial.mass p 1 k) =
        (fun k : ℕ => (k : ℝ) ^ 2 * NegativeBinomial.mass p 1 k +
          2 * ((k : ℝ) * NegativeBinomial.mass p 1 k) +
          NegativeBinomial.mass p 1 k) := by
    funext k
    push_cast
    ring
  rw [heq]
  convert h using 1
  field_simp
  ring

/-- Exact first moment of one excursion's visit count. -/
lemma hasSum_weighted_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => (k : ℝ) * visitMass q p k) (q / p) := by
  have htail := (hasSum_positiveGeometric_first hp0 hp1).mul_left q
  have ht : HasSum
      (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
        (q * NegativeBinomial.mass p 1 k)) (q / p) := by
    have hc : HasSum
        (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
          (q * NegativeBinomial.mass p 1 k)) (q * (1 / p)) :=
      htail.congr_fun (fun k => by
      push_cast
      ring)
    simpa [div_eq_mul_inv] using hc
  apply (hasSum_nat_add_iff' 1).mp
  simpa [visitMass] using ht

/-- Exact raw second moment of one excursion's visit count. -/
lemma hasSum_square_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * visitMass q p k)
      (q * (2 - p) / p ^ 2) := by
  have htail := (hasSum_positiveGeometric_second hp0 hp1).mul_left q
  have ht : HasSum
      (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2) *
        (q * NegativeBinomial.mass p 1 k)) (q * (2 - p) / p ^ 2) := by
    have hc : HasSum
        (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2) *
          (q * NegativeBinomial.mass p 1 k)) (q * ((2 - p) / p ^ 2)) :=
      htail.congr_fun (fun k => by
        push_cast
        ring)
    convert hc using 1
    ring
  apply (hasSum_nat_add_iff' 1).mp
  simpa [visitMass] using ht

lemma summable_weighted_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Summable (fun k : ℕ => (k : ℝ) * visitMass q p k) :=
  (hasSum_weighted_visitMass hp0 hp1).summable

lemma summable_square_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Summable (fun k : ℕ => (k : ℝ) ^ 2 * visitMass q p k) :=
  (hasSum_square_visitMass hp0 hp1).summable

@[simp] lemma tsum_weighted_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' k : ℕ, (k : ℝ) * visitMass q p k = q / p :=
  (hasSum_weighted_visitMass hp0 hp1).tsum_eq

@[simp] lemma tsum_square_visitMass {q p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' k : ℕ, (k : ℝ) ^ 2 * visitMass q p k = q * (2 - p) / p ^ 2 :=
  (hasSum_square_visitMass hp0 hp1).tsum_eq

/-! ## Moments of the packaged law -/

/-- The real-valued visit count on the canonical space `ℕ`. -/
def visitCount (k : ℕ) : ℝ := k

lemma visitCount_memLp_two (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    MemLp visitCount 2 (visitLaw q p hq0 hq1 hp0 hp1).toMeasure := by
  let μ := (visitLaw q p hq0 hq1 hp0 hp1).toMeasure
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  change Integrable (fun k => visitCount k ^ 2) μ
  rw [← Measure.sum_smul_dirac μ]
  apply integrable_sum_dirac (fun k => measure_ne_top μ {k})
  have hnonneg (k : ℕ) : 0 ≤ visitMass q p k :=
    visitMass_nonneg hq0 hq1 hp0.le hp1 k
  simpa [μ, visitCount, PMF.toMeasure_apply_singleton, ENNReal.toReal_ofReal,
    hnonneg, abs_of_nonneg, mul_comm] using summable_square_visitMass (q := q) hp0 hp1

lemma integral_visitCount (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫ k, visitCount k ∂(visitLaw q p hq0 hq1 hp0 hp1).toMeasure = q / p := by
  let law := visitLaw q p hq0 hq1 hp0 hp1
  have hLp := visitCount_memLp_two q p hq0 hq1 hp0 hp1
  rw [PMF.integral_eq_tsum law visitCount (hLp.integrable one_le_two)]
  have hnonneg (k : ℕ) : 0 ≤ visitMass q p k :=
    visitMass_nonneg hq0 hq1 hp0.le hp1 k
  simpa [law, visitCount, ENNReal.toReal_ofReal, hnonneg, mul_comm] using
    tsum_weighted_visitMass (q := q) hp0 hp1

lemma integral_visitCount_sq (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫ k, visitCount k ^ 2 ∂(visitLaw q p hq0 hq1 hp0 hp1).toMeasure =
      q * (2 - p) / p ^ 2 := by
  let law := visitLaw q p hq0 hq1 hp0 hp1
  have hLp := visitCount_memLp_two q p hq0 hq1 hp0 hp1
  rw [PMF.integral_eq_tsum law (fun k => visitCount k ^ 2) hLp.integrable_sq]
  have hnonneg (k : ℕ) : 0 ≤ visitMass q p k :=
    visitMass_nonneg hq0 hq1 hp0.le hp1 k
  simpa [law, visitCount, ENNReal.toReal_ofReal, hnonneg, mul_comm] using
    tsum_square_visitMass (q := q) hp0 hp1

/-- Exact variance of the Bernoulli--positive-geometric visit count. -/
lemma variance_visitCount (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Var[visitCount; (visitLaw q p hq0 hq1 hp0 hp1).toMeasure] =
      q * (2 - p - q) / p ^ 2 := by
  rw [variance_eq_sub (visitCount_memLp_two q p hq0 hq1 hp0 hp1)]
  change
    (∫ k, visitCount k ^ 2 ∂(visitLaw q p hq0 hq1 hp0 hp1).toMeasure) -
      (∫ k, visitCount k ∂(visitLaw q p hq0 hq1 hp0 hp1).toMeasure) ^ 2 =
        q * (2 - p - q) / p ^ 2
  rw [
    integral_visitCount_sq q p hq0 hq1 hp0 hp1,
    integral_visitCount q p hq0 hq1 hp0 hp1]
  field_simp

/-! ## A finite iid family and Chebyshev concentration -/

/-- Product law of the visit counts in `m` conditionally independent terminal
excursions. -/
noncomputable def iidVisitMeasure (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Measure (Fin m → ℕ) :=
  Measure.pi fun _ : Fin m => (visitLaw q p hq0 hq1 hp0 hp1).toMeasure

noncomputable instance iidVisitMeasure.instIsProbabilityMeasure
    (m : ℕ) (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (iidVisitMeasure m q p hq0 hq1 hp0 hp1) := by
  unfold iidVisitMeasure
  infer_instance

/-- Total visits made by the `m` terminal excursions. -/
def totalVisits {m : ℕ} (v : Fin m → ℕ) : ℝ :=
  ∑ i, (v i : ℝ)

lemma measurable_totalVisits (m : ℕ) : Measurable (@totalVisits m) := by
  fun_prop

lemma memLp_visitCoordinate_two (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) (i : Fin m) :
    MemLp (fun v : Fin m → ℕ => (v i : ℝ)) 2
      (iidVisitMeasure m q p hq0 hq1 hp0 hp1) := by
  exact (visitCount_memLp_two q p hq0 hq1 hp0 hp1).comp_measurePreserving
    (measurePreserving_eval
      (fun _ : Fin m => (visitLaw q p hq0 hq1 hp0 hp1).toMeasure) i)

lemma totalVisits_memLp_two (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    MemLp (@totalVisits m) 2 (iidVisitMeasure m q p hq0 hq1 hp0 hp1) := by
  change MemLp (fun v : Fin m → ℕ => ∑ i, (v i : ℝ)) 2
    (iidVisitMeasure m q p hq0 hq1 hp0 hp1)
  exact memLp_finsetSum Finset.univ
    (fun i _ => memLp_visitCoordinate_two m q p hq0 hq1 hp0 hp1 i)

/-- The total expected number of visits is `m q / p`. -/
lemma integral_totalVisits (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫ v, totalVisits v ∂(iidVisitMeasure m q p hq0 hq1 hp0 hp1) =
      (m : ℝ) * q / p := by
  unfold totalVisits iidVisitMeasure
  rw [integral_finsetSum Finset.univ]
  · have heval (i : Fin m) :
        ∫ v : Fin m → ℕ, (v i : ℝ)
            ∂Measure.pi (fun _ : Fin m =>
              (visitLaw q p hq0 hq1 hp0 hp1).toMeasure) = q / p := by
      change ∫ v : Fin m → ℕ, visitCount (v i)
          ∂Measure.pi (fun _ : Fin m =>
            (visitLaw q p hq0 hq1 hp0 hp1).toMeasure) = q / p
      rw [integral_comp_eval
        (μ := fun _ : Fin m => (visitLaw q p hq0 hq1 hp0 hp1).toMeasure)
        (i := i) (f := visitCount)
        (visitCount_memLp_two q p hq0 hq1 hp0 hp1).1,
        integral_visitCount q p hq0 hq1 hp0 hp1]
    simp_rw [heval]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro i _
    exact (memLp_visitCoordinate_two m q p hq0 hq1 hp0 hp1 i).integrable one_le_two

/-- Variances add exactly across the independent terminal excursions. -/
lemma variance_totalVisits (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Var[@totalVisits m; iidVisitMeasure m q p hq0 hq1 hp0 hp1] =
      (m : ℝ) * (q * (2 - p - q) / p ^ 2) := by
  have h := variance_sum_pi
    (X := fun _ : Fin m => visitCount)
    (μ := fun _ : Fin m => (visitLaw q p hq0 hq1 hp0 hp1).toMeasure)
    (fun _ => visitCount_memLp_two q p hq0 hq1 hp0 hp1)
  change Var[(fun v : Fin m → ℕ => ∑ i, (v i : ℝ));
      Measure.pi (fun _ : Fin m => (visitLaw q p hq0 hq1 hp0 hp1).toMeasure)] =
    (m : ℝ) * (q * (2 - p - q) / p ^ 2)
  have hfun :
      (∑ i : Fin m, fun v : Fin m → ℕ => visitCount (v i)) =
        (fun v : Fin m → ℕ => ∑ i, (v i : ℝ)) := by
    funext v
    simp [visitCount]
  rw [hfun] at h
  simpa [variance_visitCount q p hq0 hq1 hp0 hp1] using h

/-- One-sided lower-tail bound for the exact iid Bernoulli--geometric model.
This is Chebyshev's inequality with the exact mean and variance substituted. -/
theorem measure_lower_tail_totalVisits_le (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {c : ℝ} (hc : 0 < c) :
    iidVisitMeasure m q p hq0 hq1 hp0 hp1
        {v | totalVisits v < (m : ℝ) * q / p - c} ≤
      ENNReal.ofReal (((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2) := by
  let μ := iidVisitMeasure m q p hq0 hq1 hp0 hp1
  have hcheb := meas_ge_le_variance_div_sq
    (totalVisits_memLp_two m q p hq0 hq1 hp0 hp1) hc
  rw [integral_totalVisits m q p hq0 hq1 hp0 hp1,
    variance_totalVisits m q p hq0 hq1 hp0 hp1] at hcheb
  exact (measure_mono (fun v hv => by
    change totalVisits v < (m : ℝ) * q / p - c at hv
    change c ≤ |totalVisits v - (m : ℝ) * q / p|
    rw [abs_of_nonpos (by linarith)]
    linarith)).trans hcheb

/-- Real-probability form of the same lower-tail estimate. -/
theorem measureReal_lower_tail_totalVisits_le (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {c : ℝ} (hc : 0 < c) :
    (iidVisitMeasure m q p hq0 hq1 hp0 hp1).real
        {v | totalVisits v < (m : ℝ) * q / p - c} ≤
      ((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2 := by
  have h := measure_lower_tail_totalVisits_le m q p hq0 hq1 hp0 hp1 hc
  rw [measureReal_def]
  calc
    (iidVisitMeasure m q p hq0 hq1 hp0 hp1
        {v | totalVisits v < (m : ℝ) * q / p - c}).toReal
        ≤ (ENNReal.ofReal (((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = ((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2 := by
      have hnonneg :
          0 ≤ ((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2 := by
        rw [← variance_totalVisits m q p hq0 hq1 hp0 hp1]
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg c)
      exact ENNReal.toReal_ofReal hnonneg

/-- Any threshold lying `c` below the exact mean has the same Chebyshev
failure bound. -/
theorem measureReal_totalVisits_lt_threshold_le (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {threshold c : ℝ} (hc : 0 < c)
    (hthreshold : threshold ≤ (m : ℝ) * q / p - c) :
    (iidVisitMeasure m q p hq0 hq1 hp0 hp1).real
        {v | totalVisits v < threshold} ≤
      ((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2 := by
  exact (measureReal_mono (fun _ hv => lt_of_lt_of_le hv hthreshold)).trans
    (measureReal_lower_tail_totalVisits_le m q p hq0 hq1 hp0 hp1 hc)

/-- Probability that the terminal excursions supply a prescribed local-time
threshold.  This is the precise finite version of the concentration step in
HLOZ (A.7). -/
theorem one_sub_variance_ratio_le_measureReal_totalVisits_ge
    (m : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {threshold c : ℝ} (hc : 0 < c)
    (hthreshold : threshold ≤ (m : ℝ) * q / p - c) :
    1 - ((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2 ≤
      (iidVisitMeasure m q p hq0 hq1 hp0 hp1).real
        {v | threshold ≤ totalVisits v} := by
  let μ := iidVisitMeasure m q p hq0 hq1 hp0 hp1
  let success : Set (Fin m → ℕ) := {v | threshold ≤ totalVisits v}
  have hmeas : MeasurableSet success := by
    exact measurableSet_le measurable_const (measurable_totalVisits m)
  have hcompl : successᶜ = {v | totalVisits v < threshold} := by
    ext v
    simp [success]
  have hsplit := probReal_compl_eq_one_sub (μ := μ) hmeas
  rw [hcompl] at hsplit
  have hfail := measureReal_totalVisits_lt_threshold_le m q p hq0 hq1 hp0 hp1
    hc hthreshold
  change 1 - ((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2 ≤ μ.real success
  change μ.real {v | totalVisits v < threshold} ≤
    ((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2 at hfail
  linarith

/-- Convenient `1-1/n` consequence used verbatim in HLOZ (A.7). -/
theorem one_sub_inv_nat_le_measureReal_totalVisits_ge
    (m n : ℕ) (q p : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {threshold c : ℝ} (hc : 0 < c)
    (hthreshold : threshold ≤ (m : ℝ) * q / p - c)
    (hratio : ((m : ℝ) * (q * (2 - p - q) / p ^ 2)) / c ^ 2 ≤ (n : ℝ)⁻¹) :
    1 - (n : ℝ)⁻¹ ≤
      (iidVisitMeasure m q p hq0 hq1 hp0 hp1).real
        {v | threshold ≤ totalVisits v} := by
  exact (sub_le_sub_left hratio 1).trans
    (one_sub_variance_ratio_le_measureReal_totalVisits_ge
      m q p hq0 hq1 hp0 hp1 hc hthreshold)

/-! ## Connection to successful profiles and pathwise local time -/

/-- A successful profile contains at least the advertised number of terminal
excursions. -/
lemma successfulProfile_terminalLower {n : ℕ} {δ : ℝ}
    {N : Fin (n + 2) → ℕ} (hN : ThickPoint.SuccessfulProfile n δ N) :
    ThickPoint.terminalLower n δ ≤ (N ⟨n + 1, by omega⟩ : ℝ) :=
  hN.2.2.1

/-- The terminal entry `N⁽ˣ⁾ₙ,ₙ₊₁` of an excursion profile. -/
def terminalCount {n : ℕ} (N : Fin (n + 2) → ℕ) : ℕ :=
  N ⟨n + 1, by omega⟩

/-- Deterministic number of terminal excursions selected in HLOZ (A.8): the
least natural number above the lower endpoint of the successful window.  A
successful profile always contains at least this many terminal excursions. -/
noncomputable def requiredTerminalCount (n : ℕ) (δ : ℝ) : ℕ :=
  ⌈ThickPoint.terminalLower n δ⌉₊

lemma requiredTerminalCount_le_terminalCount
    {n : ℕ} {δ : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N) :
    requiredTerminalCount n δ ≤ terminalCount N := by
  exact Nat.ceil_le.mpr hN.2.2.1

/-- Exact mean of the Bernoulli--geometric visits contributed by the terminal
excursions of a profile. -/
def terminalVisitMean {n : ℕ} (N : Fin (n + 2) → ℕ) (q p : ℝ) : ℝ :=
  (terminalCount N : ℝ) * q / p

/-- Exact variance of those visits under the iid reference law. -/
def terminalVisitVariance {n : ℕ} (N : Fin (n + 2) → ℕ) (q p : ℝ) : ℝ :=
  (terminalCount N : ℝ) * (q * (2 - p - q) / p ^ 2)

/-- Gap between the exact reference mean and HLOZ's thick-point threshold. -/
def hlozTerminalMargin {n : ℕ} (N : Fin (n + 2) → ℕ)
    (q p : ℝ) (δ' : ℝ) : ℝ :=
  terminalVisitMean N q p - ThickPoint.thickThreshold n δ'

/-- Exact iid mean for the deterministic initial block of terminal excursions
selected in HLOZ (A.8). -/
noncomputable def requiredTerminalVisitMean (n : ℕ) (δ : ℝ)
    (q p : ℝ) : ℝ :=
  (requiredTerminalCount n δ : ℝ) * q / p

/-- Exact iid variance for the selected initial terminal-excursion block. -/
noncomputable def requiredTerminalVisitVariance (n : ℕ) (δ : ℝ)
    (q p : ℝ) : ℝ :=
  (requiredTerminalCount n δ : ℝ) * (q * (2 - p - q) / p ^ 2)

/-- Gap between that selected block's exact mean and HLOZ's threshold. -/
noncomputable def requiredHLOZTerminalMargin
    (n : ℕ) (δ δ' q p : ℝ) : ℝ :=
  requiredTerminalVisitMean n δ q p - ThickPoint.thickThreshold n δ'

lemma thickThreshold_eq_terminalVisitMean_sub_margin
    {n : ℕ} (N : Fin (n + 2) → ℕ) (q p δ' : ℝ) :
    ThickPoint.thickThreshold n δ' =
      terminalVisitMean N q p - hlozTerminalMargin N q p δ' := by
  simp [hlozTerminalMargin]

lemma thickThreshold_eq_requiredMean_sub_margin
    (n : ℕ) (δ δ' q p : ℝ) :
    ThickPoint.thickThreshold n δ' =
      requiredTerminalVisitMean n δ q p -
        requiredHLOZTerminalMargin n δ δ' q p := by
  simp [requiredHLOZTerminalMargin]

/-- Exact iid terminal concentration for the deterministic initial block.
Unlike the successful-profile wrapper below, this probability calculation
does not depend on a particular excursion profile: successfulness is needed
only later to certify that the actual path contains this many excursions. -/
theorem required_hlozThreshold_concentrate
    (n : ℕ) (δ δ' : ℝ)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < requiredHLOZTerminalMargin n δ δ' q p) :
    1 - requiredTerminalVisitVariance n δ q p /
        (requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤
      (iidVisitMeasure (requiredTerminalCount n δ) q p hq0 hq1 hp0 hp1).real
        {v | ThickPoint.thickThreshold n δ' ≤ totalVisits v} := by
  simpa [requiredTerminalVisitMean, requiredTerminalVisitVariance] using
    one_sub_variance_ratio_le_measureReal_totalVisits_ge
      (requiredTerminalCount n δ) q p hq0 hq1 hp0 hp1 hmargin
        (thickThreshold_eq_requiredMean_sub_margin n δ δ' q p).le

/-- `1-1/n` form of the profile-independent iid terminal calculation. -/
theorem required_hlozThreshold_probability_ge_one_sub_inv
    (n : ℕ) (δ δ' : ℝ)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < requiredHLOZTerminalMargin n δ δ' q p)
    (hratio : requiredTerminalVisitVariance n δ q p /
      (requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤ (n : ℝ)⁻¹) :
    1 - (n : ℝ)⁻¹ ≤
      (iidVisitMeasure (requiredTerminalCount n δ) q p hq0 hq1 hp0 hp1).real
        {v | ThickPoint.thickThreshold n δ' ≤ totalVisits v} := by
  exact (sub_le_sub_left hratio 1).trans
    (required_hlozThreshold_concentrate n δ δ' q p hq0 hq1 hp0 hp1 hmargin)

/-- Exact version of HLOZ (A.8), using only the deterministic initial number
of excursions guaranteed by successfulness. -/
theorem successfulProfile_required_hlozThreshold_concentrate
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < requiredHLOZTerminalMargin n δ δ' q p) :
    requiredTerminalCount n δ ≤ terminalCount N ∧
      1 - requiredTerminalVisitVariance n δ q p /
          (requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤
        (iidVisitMeasure (requiredTerminalCount n δ) q p hq0 hq1 hp0 hp1).real
          {v | ThickPoint.thickThreshold n δ' ≤ totalVisits v} := by
  refine ⟨requiredTerminalCount_le_terminalCount hN, ?_⟩
  exact required_hlozThreshold_concentrate
    n δ δ' q p hq0 hq1 hp0 hp1 hmargin

/-- `1-1/n` consequence for the selected initial block. -/
theorem successfulProfile_required_hlozThreshold_probability_ge_one_sub_inv
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (_hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < requiredHLOZTerminalMargin n δ δ' q p)
    (hratio : requiredTerminalVisitVariance n δ q p /
      (requiredHLOZTerminalMargin n δ δ' q p) ^ 2 ≤ (n : ℝ)⁻¹) :
    1 - (n : ℝ)⁻¹ ≤
      (iidVisitMeasure (requiredTerminalCount n δ) q p hq0 hq1 hp0 hp1).real
        {v | ThickPoint.thickThreshold n δ' ≤ totalVisits v} := by
  exact required_hlozThreshold_probability_ge_one_sub_inv
    n δ δ' q p hq0 hq1 hp0 hp1 hmargin hratio

/-- Exact HLOZ-scale specialization: once the reference mean is above the
threshold, the successful terminal count yields the displayed probability
bound with no asymptotic notation. -/
theorem successfulProfile_hlozThreshold_concentrate
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < hlozTerminalMargin N q p δ') :
    ThickPoint.terminalLower n δ ≤ (terminalCount N : ℝ) ∧
      1 - terminalVisitVariance N q p / (hlozTerminalMargin N q p δ') ^ 2 ≤
        (iidVisitMeasure (terminalCount N) q p hq0 hq1 hp0 hp1).real
          {v | ThickPoint.thickThreshold n δ' ≤ totalVisits v} := by
  refine ⟨successfulProfile_terminalLower hN, ?_⟩
  simpa [terminalCount, terminalVisitMean, terminalVisitVariance] using
    one_sub_variance_ratio_le_measureReal_totalVisits_ge
      (terminalCount N) q p hq0 hq1 hp0 hp1 hmargin
        (thickThreshold_eq_terminalVisitMean_sub_margin N q p δ').le

/-- `1-1/n` form of the exact HLOZ-threshold specialization. -/
theorem successfulProfile_hlozThreshold_probability_ge_one_sub_inv
    {n : ℕ} {δ δ' : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hmargin : 0 < hlozTerminalMargin N q p δ')
    (hratio : terminalVisitVariance N q p /
      (hlozTerminalMargin N q p δ') ^ 2 ≤ (n : ℝ)⁻¹) :
    1 - (n : ℝ)⁻¹ ≤
      (iidVisitMeasure (terminalCount N) q p hq0 hq1 hp0 hp1).real
        {v | ThickPoint.thickThreshold n δ' ≤ totalVisits v} := by
  exact (sub_le_sub_left hratio 1).trans
    (successfulProfile_hlozThreshold_concentrate hN q p hq0 hq1 hp0 hp1 hmargin).2

/-- Applying the iid terminal-excursion calculation at the terminal count of
a successful profile.  The only remaining numerical input is that the chosen
threshold lies `c` below the exact Bernoulli--geometric mean. -/
theorem successfulProfile_terminalVisits_concentrate
    {n : ℕ} {δ : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : ThickPoint.SuccessfulProfile n δ N)
    (q p : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    {threshold c : ℝ} (hc : 0 < c)
    (hthreshold : threshold ≤
      (N ⟨n + 1, by omega⟩ : ℝ) * q / p - c) :
    ThickPoint.terminalLower n δ ≤ (N ⟨n + 1, by omega⟩ : ℝ) ∧
      1 - ((N ⟨n + 1, by omega⟩ : ℝ) *
          (q * (2 - p - q) / p ^ 2)) / c ^ 2 ≤
        (iidVisitMeasure (N ⟨n + 1, by omega⟩) q p hq0 hq1 hp0 hp1).real
          {v | threshold ≤ totalVisits v} := by
  exact ⟨successfulProfile_terminalLower hN,
    one_sub_variance_ratio_le_measureReal_totalVisits_ge
      (N ⟨n + 1, by omega⟩) q p hq0 hq1 hp0 hp1 hc hthreshold⟩

/-- Deterministic last step: if disjoint excursion visit counts are all
contained in the path's local time and exceed the thick threshold, the
successful point is thick-successful. -/
theorem thickSuccessfulPoint_of_excursionVisits
    {s : ThickPoint.WalkPath} {n horizon m : ℕ} {δ δ' : ℝ}
    {x : ThickPoint.Point} (hx : ThickPoint.SuccessfulPoint s n horizon δ x)
    (visits : Fin m → ℕ)
    (hcontained : ∑ i, visits i ≤ ThickPoint.localTimeThrough s horizon x)
    (hthreshold : ThickPoint.thickThreshold n δ' ≤ ∑ i, (visits i : ℝ)) :
    ThickPoint.ThickSuccessfulPoint s n horizon δ δ' x := by
  refine ⟨hx, hthreshold.trans ?_⟩
  exact_mod_cast hcontained

end

end Erdos1165.AppendixLocalTime
