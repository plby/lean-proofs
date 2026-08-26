import ErdosProblems.Erdos1038.EmpiricalPotential
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Empirical root probability measures

An admissible polynomial determines the uniform probability measure on its
root multiset, with multiplicity.  This file constructs that measure as a
genuine `ProbabilityMeasure`, proves its support is `[-1,1]`, and identifies
its logarithmic potential exactly with `empiricalPotential`.  The final
measure identity is the bridge to probability-measure formulations of the
upper and lower problems.
-/

open scoped ENNReal Real BigOperators
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

theorem roots_ne_zero {f : Polynomial ℝ} (hf : IsAdmissible f) :
    f.roots ≠ 0 := by
  intro hz
  have hdegree : f.natDegree = 0 := by
    rw [← hf.2.2]
    simp [hz]
  exact (hf.1.natDegree_pos.mpr hf.2.1).ne' hdegree

def empiricalRootPMF (f : Polynomial ℝ) (hf : IsAdmissible f) : PMF ℝ :=
  PMF.ofMultiset f.roots (roots_ne_zero hf)

def empiricalRootProbability (f : Polynomial ℝ) (hf : IsAdmissible f) :
    ProbabilityMeasure ℝ :=
  ⟨(empiricalRootPMF f hf).toMeasure, inferInstance⟩

theorem empiricalRootPMF_support (f : Polynomial ℝ) (hf : IsAdmissible f) :
    (empiricalRootPMF f hf).support = rootSet f := by
  simp [empiricalRootPMF, PMF.support_ofMultiset, rootSet]

theorem empiricalRootProbability_apply_rootSet (f : Polynomial ℝ)
    (hf : IsAdmissible f) :
    (empiricalRootProbability f hf : Measure ℝ) (rootSet f) = 1 := by
  change (empiricalRootPMF f hf).toMeasure (rootSet f) = 1
  rw [← empiricalRootPMF_support f hf]
  have hmeas : MeasurableSet (empiricalRootPMF f hf).support :=
    (empiricalRootPMF f hf).support_countable.measurableSet
  rw [← Measure.restrict_apply_univ, PMF.restrict_toMeasure_support]
  simp

theorem empiricalRootProbability_supported_Icc (f : Polynomial ℝ)
    (hf : IsAdmissible f) :
    (empiricalRootProbability f hf : Measure ℝ) (Icc (-1 : ℝ) 1) = 1 := by
  have hroot : rootSet f ⊆ Icc (-1 : ℝ) 1 := by
    intro r hr
    exact hf.root_mem_Icc (mem_rootSet_iff.mp hr)
  apply le_antisymm
  · calc
      (empiricalRootProbability f hf : Measure ℝ) (Icc (-1 : ℝ) 1) ≤
          (empiricalRootProbability f hf : Measure ℝ) univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  · calc
      1 = (empiricalRootProbability f hf : Measure ℝ) (rootSet f) :=
        (empiricalRootProbability_apply_rootSet f hf).symm
      _ ≤ (empiricalRootProbability f hf : Measure ℝ) (Icc (-1 : ℝ) 1) :=
        measure_mono hroot

theorem integral_empiricalRootProbability (f : Polynomial ℝ)
    (hf : IsAdmissible f) (g : ℝ → ℝ) :
    ∫ r, g r ∂(empiricalRootProbability f hf : Measure ℝ) =
      (f.roots.map g).sum / (f.natDegree : ℝ) := by
  let p : PMF ℝ := empiricalRootPMF f hf
  have hfinite : p.support.Finite := by
    rw [empiricalRootPMF_support f hf]
    exact rootSet_finite f
  have hintOn : IntegrableOn g p.support p.toMeasure :=
    MeasureTheory.IntegrableOn.of_finite hfinite
  have hint : Integrable g p.toMeasure := by
    rw [← p.restrict_toMeasure_support]
    exact hintOn
  change ∫ r, g r ∂p.toMeasure = _
  rw [PMF.integral_eq_tsum p g hint]
  classical
  rw [tsum_eq_sum (s := f.roots.toFinset)]
  · rw [Finset.sum_multiset_map_count]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [p, empiricalRootPMF]
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    rw [hf.card_roots_eq_natDegree]
    simp only [nsmul_eq_mul]
    ring
  · intro r hr
    have hr' : r ∉ f.roots := by simpa using! hr
    dsimp [p, empiricalRootPMF]
    rw [Multiset.count_eq_zero.mpr hr']
    simp

theorem integral_logKernel_empiricalRootProbability (f : Polynomial ℝ)
    (hf : IsAdmissible f) (x : ℝ) :
    ∫ r, Real.log |x - r| ∂(empiricalRootProbability f hf : Measure ℝ) =
      empiricalPotential f x := by
  rw [integral_empiricalRootProbability]
  rw [empiricalPotential]
  have hn : (f.natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (hf.monic.natDegree_pos.mpr hf.ne_one).ne'
  field_simp

/-- Tao's sign convention for logarithmic potentials: the kernel is
`log (1 / |x-r|)`, hence the negative of `log |x-r|`. -/
def taoEmpiricalPotential (f : Polynomial ℝ) (hf : IsAdmissible f)
    (x : ℝ) : ℝ :=
  -∫ r, Real.log |x - r| ∂(empiricalRootProbability f hf : Measure ℝ)

theorem taoEmpiricalPotential_eq_neg_empiricalPotential
    (f : Polynomial ℝ) (hf : IsAdmissible f) (x : ℝ) :
    taoEmpiricalPotential f hf x = -empiricalPotential f x := by
  rw [taoEmpiricalPotential, integral_logKernel_empiricalRootProbability]

theorem taoEmpiricalPotential_pos_iff_sublevel {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∉ rootSet f) :
    0 < taoEmpiricalPotential f hf x ↔ x ∈ sublevelSet f := by
  rw [taoEmpiricalPotential_eq_neg_empiricalPotential, neg_pos]
  exact empiricalPotential_neg_iff_sublevel hf hx

/-- The positive-potential set in Tao's normalization has exactly the
polynomial sublevel volume. -/
theorem sublevelVolume_eq_volume_taoEmpiricalPotential_pos
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    sublevelVolume f = volume {x | 0 < taoEmpiricalPotential f hf x} := by
  rw [sublevelVolume]
  apply MeasureTheory.measure_congr
  have hae : ∀ᵐ x : ℝ ∂volume, x ∉ rootSet f := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not] using! volume_rootSet f
  filter_upwards [hae] with x hx
  exact propext (taoEmpiricalPotential_pos_iff_sublevel hf hx).symm

end

end Erdos1038
