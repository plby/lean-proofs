import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportCutoff
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Smooth compact-interval integrals with a normed-space target

A constructed smooth time cutoff reduces the integral to Mathlib's
parametric convolution theorem. The target may be any real normed space,
in particular the space of continuous bilinear forms.
-/

noncomputable section

open Function Set Topology MeasureTheory
open scoped ContDiff Convolution

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integration on an increasing compact interval preserves joint smoothness. -/
theorem contDiff_parametric_intervalIntegral_of_le (G : P × ℝ → F)
    (hG : ContDiff ℝ ∞ G) (a b : ℝ) (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, G (p, t)) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ :=
    PeriodTorusLineBundleClassificationTransport.exists_interval_cutoff a b
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  let g : P → ℝ → F := fun p t => χ (-t) • G (p, -t)
  have hg : ContDiff ℝ ∞ (fun q : P × ℝ => g q.1 q.2) :=
    (hχ.comp contDiff_snd.neg).smul
      (hG.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hk : IsCompact (-tsupport χ) := hχc.isCompact.neg
  have hgs : ∀ p t, p ∈ (univ : Set P) → t ∉ -tsupport χ → g p t = 0 := by
    intro p t _ ht
    have ht' : -t ∉ tsupport χ := by simpa using ht
    change χ (-t) • G (p, -t) = 0
    rw [image_eq_zero_of_notMem_tsupport ht', zero_smul]
  have hf : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) μ := locallyIntegrable_const _
  have hc := contDiffOn_convolution_right_with_param_comp (μ := μ) (n := (⊤ : ℕ∞)) L
    (v := fun _ : P => (0 : ℝ)) contDiffOn_const isOpen_univ hk hgs hf hg.contDiffOn
  have heq (p : P) : ((fun _ : ℝ => (1 : ℝ)) ⋆[L, μ] g p) 0 =
      ∫ t in a..b, G (p, t) := by
    rw [intervalIntegral.integral_of_le hab]
    change (∫ t, (1 : ℝ) • (χ (-(0 - t)) • G (p, -(0 - t))) ∂μ) =
      ∫ t in Ioc a b, G (p, t)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hχt : χ t = 1 := hχone (mem_uIcc_of_le ht.1.le ht.2)
    simp only [zero_sub, neg_neg, hχt, one_smul]
  have hfun : (fun p => ((fun _ : ℝ => (1 : ℝ)) ⋆[L, μ] g p) 0) =
      (fun p => ∫ t in a..b, G (p, t)) := funext heq
  rw [← hfun]
  exact contDiffOn_univ.mp hc

/-- A fixed compact interval integral is smooth in arbitrary normed real parameters. -/
theorem contDiff_parametric_intervalIntegral (G : P × ℝ → F)
    (hG : ContDiff ℝ ∞ G) (a b : ℝ) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, G (p, t)) := by
  rcases le_total a b with hab | hba
  · exact contDiff_parametric_intervalIntegral_of_le G hG a b hab
  · have he : (fun p => ∫ t in a..b, G (p, t)) =
        (fun p => -(∫ t in b..a, G (p, t))) :=
      funext fun _ => intervalIntegral.integral_symm b a
    rw [he]
    exact (contDiff_parametric_intervalIntegral_of_le G hG b a hba).neg

end Wikipedia.HopfProblem.SmoothMorseLemma
