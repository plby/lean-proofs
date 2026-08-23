/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166Core
import ErdosProblems.Erdos1166.Erdos1166HLOZUrn
import ErdosProblems.Erdos1166.Erdos1166HLOZScreeningAssembly

/-!
Quantitative finite-union estimates used for the exceptional events in
Hao--Li--Okada--Zheng Proposition 4.5 and the screening bridge.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Erdos1166
namespace HLOZProp45Union

open HLOZScreeningAssembly

variable {Ω ι κ : Type*} [MeasurableSpace Ω]

/-- A finite union of events inherits the cardinality times pointwise bound. -/
theorem measure_finite_union_le_card_mul
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) (a : ℝ≥0∞)
    (hE : ∀ i ∈ s, μ (E i) ≤ a) :
    μ (⋃ i ∈ s, E i) ≤ s.card * a := by
  calc
    μ (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, μ (E i) :=
      measure_biUnion_finset_le s E
    _ ≤ ∑ _i ∈ s, a := by
      gcongr with i hi
      exact hE i hi
    _ = s.card * a := by simp [nsmul_eq_mul]

/-- Abstract exponential-gap union bound: `exp(A*r)` candidates, each of
mass at most `exp(-B*r)`, cost at most `exp((A-B)*r)`. -/
theorem finite_union_exp_gap
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) (target : Set Ω)
    (A B r : ℝ)
    (hcover : target ⊆ ⋃ i ∈ s, E i)
    (hcard : (s.card : ℝ) ≤ Real.exp (A * r))
    (hE : ∀ i ∈ s, μ (E i) ≤ ENNReal.ofReal (Real.exp (-B * r))) :
    μ target ≤ ENNReal.ofReal (Real.exp ((A - B) * r)) := by
  have hcardENN : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (A * r)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  calc
    μ target ≤ μ (⋃ i ∈ s, E i) := measure_mono hcover
    _ ≤ s.card * ENNReal.ofReal (Real.exp (-B * r)) :=
      measure_finite_union_le_card_mul μ s E _ hE
    _ ≤ ENNReal.ofReal (Real.exp (A * r)) *
          ENNReal.ofReal (Real.exp (-B * r)) := by gcongr
    _ = ENNReal.ofReal (Real.exp ((A - B) * r)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring

/-- The numerical `16` versus `17` gap used in HLOZ Proposition 4.5. -/
theorem finite_union_exp_sixteen_seventeen
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) (target : Set Ω)
    (r : ℝ)
    (hcover : target ⊆ ⋃ i ∈ s, E i)
    (hcard : (s.card : ℝ) ≤ Real.exp (16 * r))
    (hE : ∀ i ∈ s, μ (E i) ≤ ENNReal.ofReal (Real.exp (-17 * r))) :
    μ target ≤ ENNReal.ofReal (Real.exp (-r)) := by
  simpa only [show (16 : ℝ) - 17 = -1 by norm_num, neg_one_mul] using
    finite_union_exp_gap μ s E target 16 17 r hcover hcard hE

/-- The same estimate packaged exactly as a `badError` hypothesis for the
screening assembly. -/
theorem finite_union_le_badError
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) (bad : Set Ω)
    (r : ℝ) (badError : ℝ≥0∞)
    (hcover : bad ⊆ ⋃ i ∈ s, E i)
    (hcard : (s.card : ℝ) ≤ Real.exp (16 * r))
    (hE : ∀ i ∈ s, μ (E i) ≤ ENNReal.ofReal (Real.exp (-17 * r)))
    (habsorb : ENNReal.ofReal (Real.exp (-r)) ≤ badError) :
    μ bad ≤ badError :=
  (finite_union_exp_sixteen_seventeen μ s E bad r hcover hcard hE).trans habsorb

/-- A clean one-stage bound plus an exponentially small finite family of bad
events supplies a `StageBound` with that common exceptional error. -/
theorem stageBound_of_clean_and_exp_bad
    (μ : Measure Ω) (previous next clean : Set Ω)
    (s : Finset ι) (badEvent : ι → Set Ω)
    (q badError : ℝ≥0∞) (r : ℝ)
    (hnested : next ⊆ previous)
    (hcover : next ⊆ clean ∪ ⋃ i ∈ s, badEvent i)
    (hclean : μ clean ≤ q * μ previous)
    (hcard : (s.card : ℝ) ≤ Real.exp (16 * r))
    (hbad : ∀ i ∈ s,
      μ (badEvent i) ≤ ENNReal.ofReal (Real.exp (-17 * r)))
    (habsorb : ENNReal.ofReal (Real.exp (-r)) ≤ badError) :
    StageBound μ q badError previous next := by
  refine ⟨hnested, ?_⟩
  calc
    μ next ≤ μ (clean ∪ ⋃ i ∈ s, badEvent i) := measure_mono hcover
    _ ≤ μ clean + μ (⋃ i ∈ s, badEvent i) := measure_union_le _ _
    _ ≤ q * μ previous + ENNReal.ofReal (Real.exp (-r)) := by
      gcongr
      exact finite_union_exp_sixteen_seventeen μ s badEvent _ r
        (Set.Subset.rfl) hcard hbad
    _ ≤ q * μ previous + badError := by gcongr

/-- Real-valued probability form, matching the `Measure.real` convention of
the surrounding HLOZ estimates. -/
theorem finite_union_exp_sixteen_seventeen_real
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Finset ι) (E : ι → Set Ω) (target : Set Ω) (r : ℝ)
    (hcover : target ⊆ ⋃ i ∈ s, E i)
    (hcard : (s.card : ℝ) ≤ Real.exp (16 * r))
    (hE : ∀ i ∈ s, μ.real (E i) ≤ Real.exp (-17 * r)) :
    μ.real target ≤ Real.exp (-r) := by
  have hE' : ∀ i ∈ s,
      μ (E i) ≤ ENNReal.ofReal (Real.exp (-17 * r)) := by
    intro i hi
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ (E i))
      ENNReal.ofReal_ne_top).mp
    simpa only [measureReal_def,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hE i hi
  have hmain := finite_union_exp_sixteen_seventeen μ s E target r
    hcover hcard hE'
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top μ target)
    ENNReal.ofReal_ne_top).mpr hmain
  simpa only [measureReal_def,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hreal

/-- Conditional-probability form: the union estimate applies unchanged to
the conditional measure. -/
theorem cond_finite_union_exp_sixteen_seventeen
    (μ : Measure Ω) (C : Set Ω)
    (s : Finset ι) (E : ι → Set Ω) (target : Set Ω) (r : ℝ)
    (hcover : target ⊆ ⋃ i ∈ s, E i)
    (hcard : (s.card : ℝ) ≤ Real.exp (16 * r))
    (hE : ∀ i ∈ s,
      μ[|C] (E i) ≤ ENNReal.ofReal (Real.exp (-17 * r))) :
    μ[|C] target ≤ ENNReal.ofReal (Real.exp (-r)) :=
  finite_union_exp_sixteen_seventeen μ[|C] s E target r hcover hcard hE

open scoped Classical in
/-- Product-index version for the block/time grids appearing in HLOZ
equations (4.22)--(4.24). -/
theorem cond_product_grid_exp_sixteen_seventeen
    (μ : Measure Ω) (C : Set Ω)
    (blocks : Finset ι) (times : Finset κ) (E : ι → κ → Set Ω)
    (target : Set Ω) (r : ℝ)
    (hcover : target ⊆
      ⋃ z ∈ blocks.product times, E z.1 z.2)
    (hcard : ((blocks.card * times.card : ℕ) : ℝ) ≤ Real.exp (16 * r))
    (hE : ∀ i ∈ blocks, ∀ j ∈ times,
      μ[|C] (E i j) ≤ ENNReal.ofReal (Real.exp (-17 * r))) :
    μ[|C] target ≤ ENNReal.ofReal (Real.exp (-r)) := by
  apply cond_finite_union_exp_sixteen_seventeen μ C
    (blocks.product times) (fun z ↦ E z.1 z.2) target r hcover
  · simpa using hcard
  · intro z hz
    exact hE z.1 (Finset.mem_product.mp hz).1 z.2 (Finset.mem_product.mp hz).2

open scoped Classical in
/-- Product-grid estimate packaged as the common `badError` consumed by the
screening bridge. -/
theorem cond_product_grid_le_badError
    (μ : Measure Ω) (C : Set Ω)
    (blocks : Finset ι) (times : Finset κ) (E : ι → κ → Set Ω)
    (bad : Set Ω) (r : ℝ) (badError : ℝ≥0∞)
    (hcover : bad ⊆
      ⋃ z ∈ blocks.product times, E z.1 z.2)
    (hcard : ((blocks.card * times.card : ℕ) : ℝ) ≤ Real.exp (16 * r))
    (hE : ∀ i ∈ blocks, ∀ j ∈ times,
      μ[|C] (E i j) ≤ ENNReal.ofReal (Real.exp (-17 * r)))
    (habsorb : ENNReal.ofReal (Real.exp (-r)) ≤ badError) :
    μ[|C] bad ≤ badError :=
  (cond_product_grid_exp_sixteen_seventeen μ C blocks times E bad r
    hcover hcard hE).trans habsorb

open scoped Classical in
/-- Real-valued conditional/product-grid form. -/
theorem cond_product_grid_exp_sixteen_seventeen_real
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : Set Ω)
    (blocks : Finset ι) (times : Finset κ) (E : ι → κ → Set Ω)
    (target : Set Ω) (r : ℝ)
    (hcover : target ⊆
      ⋃ z ∈ blocks.product times, E z.1 z.2)
    (hcard : ((blocks.card * times.card : ℕ) : ℝ) ≤ Real.exp (16 * r))
    (hE : ∀ i ∈ blocks, ∀ j ∈ times,
      μ[|C].real (E i j) ≤ Real.exp (-17 * r)) :
    μ[|C].real target ≤ Real.exp (-r) := by
  apply finite_union_exp_sixteen_seventeen_real μ[|C]
    (blocks.product times) (fun z ↦ E z.1 z.2) target r hcover
  · simpa using hcard
  · intro z hz
    exact hE z.1 (Finset.mem_product.mp hz).1 z.2 (Finset.mem_product.mp hz).2

/-- Horizon-indexed form at scale `sqrt m`: if the horizon itself is at most
`exp(16*sqrt m)` and every bad time has mass at most
`exp(-17*sqrt m)`, their union has mass at most `exp(-sqrt m)`. -/
theorem horizon_union_le_exp_neg_sqrt
    (μ : Measure Ω) (horizon m : ℕ) (E : Fin horizon → Set Ω)
    (target : Set Ω)
    (hcover : target ⊆ ⋃ i, E i)
    (hhorizon : (horizon : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hE : ∀ i, μ (E i) ≤
      ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ)))) :
    μ target ≤ ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  apply finite_union_exp_sixteen_seventeen μ Finset.univ E target
    (Real.sqrt (m : ℝ))
  · simpa using hcover
  · simpa using hhorizon
  · intro i _hi
    exact hE i

/-- Conditional version of the horizon-sized estimate. -/
theorem cond_horizon_union_le_exp_neg_sqrt
    (μ : Measure Ω) (C : Set Ω) (horizon m : ℕ)
    (E : Fin horizon → Set Ω) (target : Set Ω)
    (hcover : target ⊆ ⋃ i, E i)
    (hhorizon : (horizon : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hE : ∀ i, μ[|C] (E i) ≤
      ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ)))) :
    μ[|C] target ≤ ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) :=
  horizon_union_le_exp_neg_sqrt μ[|C] horizon m E target hcover hhorizon hE

/-- Horizon-sized estimate packaged as a common `badError`. -/
theorem cond_horizon_union_le_badError
    (μ : Measure Ω) (C : Set Ω) (horizon m : ℕ)
    (E : Fin horizon → Set Ω) (bad : Set Ω) (badError : ℝ≥0∞)
    (hcover : bad ⊆ ⋃ i, E i)
    (hhorizon : (horizon : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hE : ∀ i, μ[|C] (E i) ≤
      ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ))))
    (habsorb : ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) ≤ badError) :
    μ[|C] bad ≤ badError :=
  (cond_horizon_union_le_exp_neg_sqrt μ C horizon m E bad
    hcover hhorizon hE).trans habsorb

/-- Real-valued conditional horizon estimate. -/
theorem cond_horizon_union_le_exp_neg_sqrt_real
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : Set Ω) (horizon m : ℕ)
    (E : Fin horizon → Set Ω) (target : Set Ω)
    (hcover : target ⊆ ⋃ i, E i)
    (hhorizon : (horizon : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hE : ∀ i, μ[|C].real (E i) ≤
      Real.exp (-17 * Real.sqrt (m : ℝ))) :
    μ[|C].real target ≤ Real.exp (-Real.sqrt (m : ℝ)) := by
  apply finite_union_exp_sixteen_seventeen_real μ[|C]
    Finset.univ E target (Real.sqrt (m : ℝ))
  · simpa using hcover
  · simpa using hhorizon
  · intro i _hi
    exact hE i

end HLOZProp45Union
end Erdos1166
