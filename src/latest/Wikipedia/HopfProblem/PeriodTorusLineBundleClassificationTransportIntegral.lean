import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportCutoff
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Smooth dependence of compact-interval integrals on parameters

An actual smooth compactly supported time cutoff reduces the integral to the
existing parametric convolution theorem, using the restricted interval measure.
The measure need not be translation invariant for that theorem. This proves
all real derivatives at once without increasing computational limits.
-/

noncomputable section

open Function Set Topology MeasureTheory
open scoped ContDiff Convolution

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem contDiff_parametric_intervalIntegral_of_le (F : P × ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (a b : ℝ) (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, F (p, t)) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := exists_interval_cutoff a b
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  let L := ContinuousLinearMap.mul ℝ ℂ
  let g : P → ℝ → ℂ := fun p t => χ (-t) • F (p, -t)
  have hg : ContDiff ℝ ∞ (fun q : P × ℝ => g q.1 q.2) :=
    (hχ.comp contDiff_snd.neg).smul
      (hF.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hk : IsCompact (-tsupport χ) := hχc.isCompact.neg
  have hgs : ∀ p t, p ∈ (univ : Set P) → t ∉ -tsupport χ → g p t = 0 := by
    intro p t _ ht
    have ht' : -t ∉ tsupport χ := by simpa using ht
    change χ (-t) • F (p, -t) = 0
    rw [image_eq_zero_of_notMem_tsupport ht', zero_smul]
  have hf : LocallyIntegrable (fun _ : ℝ => (1 : ℂ)) μ := locallyIntegrable_const _
  have hc := contDiffOn_convolution_right_with_param_comp (μ := μ) (n := (⊤ : ℕ∞)) L
    (v := fun _ : P => (0 : ℝ)) contDiffOn_const isOpen_univ hk hgs hf hg.contDiffOn
  have heq (p : P) : ((fun _ : ℝ => (1 : ℂ)) ⋆[L, μ] g p) 0 =
      ∫ t in a..b, F (p, t) := by
    rw [intervalIntegral.integral_of_le hab]
    change (∫ t, (1 : ℂ) * (χ (-(0 - t)) • F (p, -(0 - t))) ∂μ) =
      ∫ t in Ioc a b, F (p, t)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hχt : χ t = 1 := hχone (mem_uIcc_of_le ht.1.le ht.2)
    simp only [zero_sub, neg_neg, hχt, one_smul, one_mul]
  have hfun : (fun p => ((fun _ : ℝ => (1 : ℂ)) ⋆[L, μ] g p) 0) =
      (fun p => ∫ t in a..b, F (p, t)) := funext heq
  rw [← hfun]
  exact contDiffOn_univ.mp hc

/-- Integration on a fixed compact interval preserves joint real smoothness
with respect to an arbitrary normed real parameter space. -/
theorem contDiff_parametric_intervalIntegral (F : P × ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, F (p, t)) := by
  rcases le_total a b with hab | hba
  · exact contDiff_parametric_intervalIntegral_of_le F hF a b hab
  · have he : (fun p => ∫ t in a..b, F (p, t)) =
        (fun p => -(∫ t in b..a, F (p, t))) :=
      funext fun _ => intervalIntegral.integral_symm b a
    rw [he]
    exact (contDiff_parametric_intervalIntegral_of_le F hF b a hba).neg

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
