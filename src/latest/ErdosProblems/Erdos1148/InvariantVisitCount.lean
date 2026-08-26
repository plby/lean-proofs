import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Invariant visit counts and their elementary Markov bound -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

noncomputable def orbitVisitPattern {X : Type*} (f : X → X) (Q : Set X) (n : ℕ) (x : X) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i : Fin n => f^[i.val] x ∈ Q)

noncomputable def orbitVisitCount {X : Type*} (f : X → X) (Q : Set X) (n : ℕ) (x : X) : ℝ :=
  (orbitVisitPattern f Q n x).card

lemma orbitVisitCount_eq_sum_indicator {X : Type*} (f : X → X) (Q : Set X) (n : ℕ) (x : X) :
    orbitVisitCount f Q n x = ∑ i : Fin n,
      ((f^[i.val]) ⁻¹' Q).indicator (fun _ : X => (1 : ℝ)) x := by
  classical
  simp only [orbitVisitCount, orbitVisitPattern, Finset.natCast_card_filter,
    Set.indicator_apply, Set.mem_preimage]

variable {X : Type*} [MeasurableSpace X] {f : X → X} {Q : Set X} {μ : Measure X}

lemma measurable_orbitVisitCount (hf : Measurable f) (hQ : MeasurableSet Q) (n : ℕ) :
    Measurable (orbitVisitCount f Q n) := by
  have heq := funext (orbitVisitCount_eq_sum_indicator f Q n)
  rw [heq]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hQ.preimage (hf.iterate i.val)))

lemma integrable_orbitVisitCount [IsFiniteMeasure μ] (hf : Measurable f) (hQ : MeasurableSet Q)
    (n : ℕ) : Integrable (orbitVisitCount f Q n) μ := by
  have heq := funext (orbitVisitCount_eq_sum_indicator f Q n)
  rw [heq]
  exact integrable_finsetSum _ (fun i _ => (integrable_const (1 : ℝ)).indicator
    (hQ.preimage (hf.iterate i.val)))

theorem integral_orbitVisitCount [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hQ : MeasurableSet Q) (n : ℕ) :
    (∫ x, orbitVisitCount f Q n x ∂μ) = (n : ℝ) * μ.real Q := by
  have heq := funext (orbitVisitCount_eq_sum_indicator f Q n)
  rw [heq, integral_finsetSum _ (fun i _ => (integrable_const (1 : ℝ)).indicator
    (hQ.preimage (hf.measurable.iterate i.val)))]
  have hterm (i : Fin n) : (∫ x, ((f^[i.val]) ⁻¹' Q).indicator (fun _ : X => (1 : ℝ)) x ∂μ) =
      μ.real Q := by
    rw [integral_indicator_const (μ := μ) (1 : ℝ) (hQ.preimage (hf.measurable.iterate i.val))]
    simp only [smul_eq_mul, mul_one, Measure.real]
    congr 1
    rw [← Measure.map_apply (hf.measurable.iterate i.val) hQ, (hf.iterate i.val).map_eq]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem orbitVisitCount_exceedance_mass_le [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hQ : MeasurableSet Q) {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 0 < n) :
    μ.real {x | κ * n ≤ orbitVisitCount f Q n x} ≤ μ.real Q / κ := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => Nat.cast_nonneg (orbitVisitPattern f Q n x).card))
    (integrable_orbitVisitCount (μ := μ) hf.measurable hQ n) (κ * n)
  change κ * n * μ.real {x | κ * n ≤ orbitVisitCount f Q n x} ≤
    ∫ x, orbitVisitCount f Q n x ∂μ at hmarkov
  rw [integral_orbitVisitCount hf hQ] at hmarkov
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscaled : (n : ℝ) * (κ * μ.real {x | κ * n ≤ orbitVisitCount f Q n x}) ≤
      (n : ℝ) * μ.real Q := by nlinarith only [hmarkov]
  have hbound := (mul_le_mul_iff_right₀ hnR).mp hscaled
  apply (le_div_iff₀ hκ).mpr
  simpa only [mul_comm] using hbound

theorem orbitVisitCount_below_mass_lower [IsProbabilityMeasure μ] (hf : MeasurePreserving f μ μ)
    (hQ : MeasurableSet Q) {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 0 < n) :
    1 - μ.real Q / κ ≤ μ.real {x | orbitVisitCount f Q n x ≤ κ * n} := by
  have hm : MeasurableSet {x | orbitVisitCount f Q n x ≤ κ * n} :=
    measurableSet_le (measurable_orbitVisitCount hf.measurable hQ n) measurable_const
  have hsub : {x | orbitVisitCount f Q n x ≤ κ * n}ᶜ ⊆ {x | κ * n ≤ orbitVisitCount f Q n x} := by
    intro x hx
    change ¬ orbitVisitCount f Q n x ≤ κ * n at hx
    exact (lt_of_not_ge hx).le
  have hbound := (measureReal_mono (μ := μ) hsub).trans (orbitVisitCount_exceedance_mass_le hf hQ hκ hn)
  rw [measureReal_compl hm, probReal_univ] at hbound
  linarith only [hbound]

end Erdos1148.DukeArithmetic
