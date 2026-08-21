import ErdosProblems.Erdos239.External.Erdos67.MRGranvilleSoundararajanHR
import ErdosProblems.Erdos239.External.Erdos67.LogPhaseSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# A uniform power-sum input for Granville--Soundararajan Lemma 7.1

The elementary power sum in the convolution proof needs a uniform
sum--integral estimate for `x ↦ x^(it)`.  A first-derivative comparison loses
`|t| log X`; the source-uniform estimate instead follows from the trapezoidal
rule because the second derivative is summable.  This file develops that
second-order comparison for complex-valued functions.
-/

open scoped BigOperators ComplexConjugate Interval
open Finset Set MeasureTheory intervalIntegral

namespace Erdos67

noncomputable section

private theorem hasDerivAt_re_of_hasDerivAt
    {f f' : ℝ → ℂ} {x : ℝ} (h : HasDerivAt f (f' x) x) :
    HasDerivAt (fun y => (f y).re) (f' x).re x := by
  have hc : HasDerivAt (fun _ : ℝ => Complex.reCLM) 0 x :=
    hasDerivAt_const x Complex.reCLM
  simpa only [Complex.reCLM_apply, zero_apply, zero_add] using hc.clm_apply h

private theorem hasDerivAt_im_of_hasDerivAt
    {f f' : ℝ → ℂ} {x : ℝ} (h : HasDerivAt f (f' x) x) :
    HasDerivAt (fun y => (f y).im) (f' x).im x := by
  have hc : HasDerivAt (fun _ : ℝ => Complex.imCLM) 0 x :=
    hasDerivAt_const x Complex.imCLM
  simpa only [Complex.imCLM_apply, zero_apply, zero_add] using hc.clm_apply h

/-
private theorem abs_re_complex_trapezoidal_cell_error_le
    {f f' f'' : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    {zeta : ℝ} (hzeta : 0 ≤ zeta)
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖f'' x‖ ≤ zeta) :
    |((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).re| ≤ zeta / 12 := by
  have htrap := abs_trapezoidal_error_re_le hderiv hderiv2 hzeta hbound
  have hfcont : ContinuousOn f (Set.Icc a (a + 1)) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a (a + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hfcont.integrableOn_Icc
  have hreal :
      ((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).re =
        trapezoidal_error (fun x => (f x).re) 1 a (a + 1) := by
    have hri : (∫ x in a..a + 1, f x).re = ∫ x in a..a + 1, (f x).re := by
      simpa only [RCLike.re_to_complex] using (intervalIntegral_re hfint).symm
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.add_re, hri]
    simp [trapezoidal_error, trapezoidal_integral_one]
    ring
  rw [hreal]
  exact htrap
/-
  let I : Set ℝ := Set.Icc a (a + 1)
  have hab : a < a + 1 := by linarith
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  let fr : ℝ → ℝ := fun x => (f x).re
  let f1r : ℝ → ℝ := fun x => (f' x).re
  let f2r : ℝ → ℝ := fun x => (f'' x).re
  have hfr (x : ℝ) (hx : x ∈ I) : HasDerivAt fr (f1r x) x :=
    hasDerivAt_re_of_hasDerivAt (hderiv x hx)
  have hf1r (x : ℝ) (hx : x ∈ I) : HasDerivAt f1r (f2r x) x :=
    hasDerivAt_re_of_hasDerivAt (hderiv2 x hx)
  have hdr (x : ℝ) (hx : x ∈ I) : derivWithin fr I x = f1r x :=
    (hfr x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
  have hdiffR : DifferentiableOn ℝ fr I := fun x hx =>
    (hfr x hx).differentiableAt.differentiableWithinAt
  have hdiffDR : DifferentiableOn ℝ (derivWithin fr I) I := by
    have hbase : DifferentiableOn ℝ f1r I := fun x hx =>
      (hf1r x hx).differentiableAt.differentiableWithinAt
    exact hbase.congr (fun x hx => hdr x hx)
  have hiterR (x : ℝ) : |iteratedDerivWithin 2 fr I x| ≤ zeta := by
    by_cases hacc : AccPt x (Filter.principal I)
    · have hxcl : x ∈ closure I := hacc.clusterPt.mem_closure
      have hx : x ∈ I := by simpa only [I, isClosed_Icc.closure_eq] using hxcl
      have hsecond : derivWithin (derivWithin fr I) I x = f2r x := by
        rw [derivWithin_congr (fun y hy => hdr y hy) (hdr x hx)]
        exact (hf1r x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
      have heq : iteratedDerivWithin 2 fr I x = f2r x := by
        rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ]
        simpa only [iteratedDerivWithin_succ, iteratedDerivWithin_zero] using hsecond
      rw [heq]
      exact (Complex.abs_re_le_norm (f'' x)).trans (hbound x hx)
    · rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ,
        derivWithin_zero_of_not_accPt hacc]
      simpa using hzeta
  have htrap := trapezoidal_error_le hdiffR hdiffDR hiterR (N := 1) (by omega)
  have hfcont : ContinuousOn f I := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a (a + 1) := hfcont.intervalIntegrable
  have hreal :
      ((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).re =
        trapezoidal_error fr 1 a (a + 1) := by
    rw [map_sub, map_div, map_add, map_intervalIntegral]
    · simp [trapezoidal_error, trapezoidal_integral_one, fr]
    · exact hfint
  rw [hreal]
  simpa using htrap
-/

private theorem abs_im_complex_trapezoidal_cell_error_le
    {f f' f'' : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    {zeta : ℝ} (hzeta : 0 ≤ zeta)
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖f'' x‖ ≤ zeta) :
    |((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).im| ≤ zeta / 12 := by
  have htrap := abs_trapezoidal_error_im_le hderiv hderiv2 hzeta hbound
  have hfcont : ContinuousOn f (Set.Icc a (a + 1)) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a (a + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hfcont.integrableOn_Icc
  have himag :
      ((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).im =
        trapezoidal_error (fun x => (f x).im) 1 a (a + 1) := by
    have hii : (∫ x in a..a + 1, f x).im = ∫ x in a..a + 1, (f x).im := by
      simpa only [RCLike.im_to_complex] using (intervalIntegral_im hfint).symm
    rw [Complex.sub_im, Complex.div_ofNat_im, Complex.add_im, hii]
    simp [trapezoidal_error, trapezoidal_integral_one]
    ring
  rw [himag]
  exact htrap
/-
  let I : Set ℝ := Set.Icc a (a + 1)
  have hab : a < a + 1 := by linarith
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  let fi : ℝ → ℝ := fun x => (f x).im
  let f1i : ℝ → ℝ := fun x => (f' x).im
  let f2i : ℝ → ℝ := fun x => (f'' x).im
  have hfi (x : ℝ) (hx : x ∈ I) : HasDerivAt fi (f1i x) x :=
    hasDerivAt_im_of_hasDerivAt (hderiv x hx)
  have hf1i (x : ℝ) (hx : x ∈ I) : HasDerivAt f1i (f2i x) x :=
    hasDerivAt_im_of_hasDerivAt (hderiv2 x hx)
  have hdi (x : ℝ) (hx : x ∈ I) : derivWithin fi I x = f1i x :=
    (hfi x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
  have hdiffI : DifferentiableOn ℝ fi I := fun x hx =>
    (hfi x hx).differentiableAt.differentiableWithinAt
  have hdiffDI : DifferentiableOn ℝ (derivWithin fi I) I := by
    have hbase : DifferentiableOn ℝ f1i I := fun x hx =>
      (hf1i x hx).differentiableAt.differentiableWithinAt
    exact hbase.congr (fun x hx => hdi x hx)
  have hiterI (x : ℝ) : |iteratedDerivWithin 2 fi I x| ≤ zeta := by
    by_cases hacc : AccPt x (Filter.principal I)
    · have hxcl : x ∈ closure I := hacc.clusterPt.mem_closure
      have hx : x ∈ I := by simpa only [I, isClosed_Icc.closure_eq] using hxcl
      have hsecond : derivWithin (derivWithin fi I) I x = f2i x := by
        rw [derivWithin_congr (fun y hy => hdi y hy) (hdi x hx)]
        exact (hf1i x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
      have heq : iteratedDerivWithin 2 fi I x = f2i x := by
        rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ]
        simpa only [iteratedDerivWithin_succ, iteratedDerivWithin_zero] using hsecond
      rw [heq]
      exact (Complex.abs_im_le_norm (f'' x)).trans (hbound x hx)
    · rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ,
        derivWithin_zero_of_not_accPt hacc]
      simpa using hzeta
  have htrap := trapezoidal_error_le hdiffI hdiffDI hiterI (N := 1) (by omega)
  have hfcont : ContinuousOn f I := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a (a + 1) := hfcont.intervalIntegrable
  have himag :
      ((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).im =
        trapezoidal_error fi 1 a (a + 1) := by
    rw [map_sub, map_div, map_add, map_intervalIntegral]
    · simp [trapezoidal_error, trapezoidal_integral_one, fi]
    · exact hfint
  rw [himag]
  simpa using htrap

-/
-/
private theorem iteratedDerivWithin_two_re_le
    {f f' f'' : ℝ → ℂ} {a zeta x : ℝ}
    (hderiv : ∀ y ∈ Set.Icc a (a + 1), HasDerivAt f (f' y) y)
    (hderiv2 : ∀ y ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' y) y)
    (hzeta : 0 ≤ zeta)
    (hbound : ∀ y ∈ Set.Icc a (a + 1), ‖f'' y‖ ≤ zeta) :
    |iteratedDerivWithin 2 (fun y => (f y).re) (Set.Icc a (a + 1)) x| ≤ zeta := by
  let I : Set ℝ := Set.Icc a (a + 1)
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  let fr : ℝ → ℝ := fun y => (f y).re
  let f1r : ℝ → ℝ := fun y => (f' y).re
  let f2r : ℝ → ℝ := fun y => (f'' y).re
  have hfr (y : ℝ) (hy : y ∈ I) : HasDerivAt fr (f1r y) y :=
    hasDerivAt_re_of_hasDerivAt (hderiv y hy)
  have hf1r (y : ℝ) (hy : y ∈ I) : HasDerivAt f1r (f2r y) y :=
    hasDerivAt_re_of_hasDerivAt (hderiv2 y hy)
  have hdr (y : ℝ) (hy : y ∈ I) : derivWithin fr I y = f1r y :=
    (hfr y hy).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hy)
  by_cases hacc : AccPt x (Filter.principal I)
  · have hxcl : x ∈ closure I := hacc.clusterPt.mem_closure
    have hx : x ∈ I := by simpa only [I, isClosed_Icc.closure_eq] using hxcl
    have hsecond : derivWithin (derivWithin fr I) I x = f2r x := by
      rw [derivWithin_congr (fun y hy => hdr y hy) (hdr x hx)]
      exact (hf1r x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
    have heq : iteratedDerivWithin 2 fr I x = f2r x := by
      rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ]
      simpa only [iteratedDerivWithin_succ, iteratedDerivWithin_zero] using hsecond
    rw [heq]
    exact (Complex.abs_re_le_norm (f'' x)).trans (hbound x hx)
  · rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ,
      derivWithin_zero_of_not_accPt hacc]
    simpa using hzeta

private theorem iteratedDerivWithin_two_im_le
    {f f' f'' : ℝ → ℂ} {a zeta x : ℝ}
    (hderiv : ∀ y ∈ Set.Icc a (a + 1), HasDerivAt f (f' y) y)
    (hderiv2 : ∀ y ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' y) y)
    (hzeta : 0 ≤ zeta)
    (hbound : ∀ y ∈ Set.Icc a (a + 1), ‖f'' y‖ ≤ zeta) :
    |iteratedDerivWithin 2 (fun y => (f y).im) (Set.Icc a (a + 1)) x| ≤ zeta := by
  let I : Set ℝ := Set.Icc a (a + 1)
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  let fi : ℝ → ℝ := fun y => (f y).im
  let f1i : ℝ → ℝ := fun y => (f' y).im
  let f2i : ℝ → ℝ := fun y => (f'' y).im
  have hfi (y : ℝ) (hy : y ∈ I) : HasDerivAt fi (f1i y) y :=
    hasDerivAt_im_of_hasDerivAt (hderiv y hy)
  have hf1i (y : ℝ) (hy : y ∈ I) : HasDerivAt f1i (f2i y) y :=
    hasDerivAt_im_of_hasDerivAt (hderiv2 y hy)
  have hdi (y : ℝ) (hy : y ∈ I) : derivWithin fi I y = f1i y :=
    (hfi y hy).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hy)
  by_cases hacc : AccPt x (Filter.principal I)
  · have hxcl : x ∈ closure I := hacc.clusterPt.mem_closure
    have hx : x ∈ I := by simpa only [I, isClosed_Icc.closure_eq] using hxcl
    have hsecond : derivWithin (derivWithin fi I) I x = f2i x := by
      rw [derivWithin_congr (fun y hy => hdi y hy) (hdi x hx)]
      exact (hf1i x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
    have heq : iteratedDerivWithin 2 fi I x = f2i x := by
      rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ]
      simpa only [iteratedDerivWithin_succ, iteratedDerivWithin_zero] using hsecond
    rw [heq]
    exact (Complex.abs_im_le_norm (f'' x)).trans (hbound x hx)
  · rw [show 2 = 1 + 1 by omega, iteratedDerivWithin_succ,
      derivWithin_zero_of_not_accPt hacc]
    simpa using hzeta

private theorem differentiableOn_derivWithin_re
    {f f' f'' : ℝ → ℂ} {a : ℝ}
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x) :
    DifferentiableOn ℝ
      (derivWithin (fun x => (f x).re) (Set.Icc a (a + 1)))
      (Set.Icc a (a + 1)) := by
  have huniq : UniqueDiffOn ℝ (Set.Icc a (a + 1)) := uniqueDiffOn_Icc (by linarith)
  have hdr (x : ℝ) (hx : x ∈ Set.Icc a (a + 1)) :
      derivWithin (fun y => (f y).re) (Set.Icc a (a + 1)) x = (f' x).re :=
    (hasDerivAt_re_of_hasDerivAt (hderiv x hx)).hasDerivWithinAt.derivWithin
      (huniq.uniqueDiffWithinAt hx)
  have hbase : DifferentiableOn ℝ (fun x => (f' x).re) (Set.Icc a (a + 1)) :=
    fun x hx => (hasDerivAt_re_of_hasDerivAt (hderiv2 x hx)).differentiableAt
      |>.differentiableWithinAt
  exact hbase.congr hdr

private theorem differentiableOn_derivWithin_im
    {f f' f'' : ℝ → ℂ} {a : ℝ}
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x) :
    DifferentiableOn ℝ
      (derivWithin (fun x => (f x).im) (Set.Icc a (a + 1)))
      (Set.Icc a (a + 1)) := by
  have huniq : UniqueDiffOn ℝ (Set.Icc a (a + 1)) := uniqueDiffOn_Icc (by linarith)
  have hdi (x : ℝ) (hx : x ∈ Set.Icc a (a + 1)) :
      derivWithin (fun y => (f y).im) (Set.Icc a (a + 1)) x = (f' x).im :=
    (hasDerivAt_im_of_hasDerivAt (hderiv x hx)).hasDerivWithinAt.derivWithin
      (huniq.uniqueDiffWithinAt hx)
  have hbase : DifferentiableOn ℝ (fun x => (f' x).im) (Set.Icc a (a + 1)) :=
    fun x hx => (hasDerivAt_im_of_hasDerivAt (hderiv2 x hx)).differentiableAt
      |>.differentiableWithinAt
  exact hbase.congr hdi

private theorem abs_trapezoidal_error_one_le
    {g : ℝ → ℝ} {a zeta : ℝ}
    (hdiff : DifferentiableOn ℝ g (Set.Icc a (a + 1)))
    (hdiffD : DifferentiableOn ℝ
      (derivWithin g (Set.Icc a (a + 1))) (Set.Icc a (a + 1)))
    (hiter : ∀ x, |iteratedDerivWithin 2 g (Set.Icc a (a + 1)) x| ≤ zeta) :
    |trapezoidal_error g 1 a (a + 1)| ≤ zeta / 12 := by
  rw [← uIcc_of_le (by linarith : a ≤ a + 1)] at hdiff hdiffD hiter
  have hraw := @trapezoidal_error_le g a (a + 1)
    hdiff hdiffD zeta hiter 1 (by omega)
  convert hraw using 1 <;> norm_num

private theorem abs_trapezoidal_error_re_le
    {f f' f'' : ℝ → ℂ} {a zeta : ℝ}
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    (hzeta : 0 ≤ zeta)
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖f'' x‖ ≤ zeta) :
    |trapezoidal_error (fun x => (f x).re) 1 a (a + 1)| ≤ zeta / 12 := by
  have hdiff : DifferentiableOn ℝ (fun x => (f x).re) (Set.Icc a (a + 1)) :=
    fun x hx => (hasDerivAt_re_of_hasDerivAt (hderiv x hx)).differentiableAt
      |>.differentiableWithinAt
  have hdiffD := differentiableOn_derivWithin_re hderiv hderiv2
  have hiter (x : ℝ) :
      |iteratedDerivWithin 2 (fun y => (f y).re) (Set.Icc a (a + 1)) x| ≤ zeta :=
    iteratedDerivWithin_two_re_le hderiv hderiv2 hzeta hbound
  exact abs_trapezoidal_error_one_le hdiff hdiffD hiter
/-
  let I : Set ℝ := Set.Icc a (a + 1)
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  let fr : ℝ → ℝ := fun x => (f x).re
  let f1r : ℝ → ℝ := fun x => (f' x).re
  have hfr (x : ℝ) (hx : x ∈ I) : HasDerivAt fr (f1r x) x :=
    hasDerivAt_re_of_hasDerivAt (hderiv x hx)
  have hf1r (x : ℝ) (hx : x ∈ I) :
      HasDerivAt f1r (f'' x).re x :=
    hasDerivAt_re_of_hasDerivAt (hderiv2 x hx)
  have hdr (x : ℝ) (hx : x ∈ I) : derivWithin fr I x = f1r x :=
    (hfr x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
  have hdiffR : DifferentiableOn ℝ fr I := fun x hx =>
    (hfr x hx).differentiableAt.differentiableWithinAt
  have hdiffDR : DifferentiableOn ℝ (derivWithin fr I) I := by
    have hbase : DifferentiableOn ℝ f1r I := fun x hx =>
      (hf1r x hx).differentiableAt.differentiableWithinAt
    exact hbase.congr (fun x hx => hdr x hx)
  have hiterR (x : ℝ) : |iteratedDerivWithin 2 fr I x| ≤ zeta :=
    iteratedDerivWithin_two_re_le hderiv hderiv2 hzeta hbound
  simpa only [fr, I] using
    (trapezoidal_error_le hdiffR hdiffDR hiterR (N := 1) (by omega))
-/

private theorem abs_trapezoidal_error_im_le
    {f f' f'' : ℝ → ℂ} {a zeta : ℝ}
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    (hzeta : 0 ≤ zeta)
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖f'' x‖ ≤ zeta) :
    |trapezoidal_error (fun x => (f x).im) 1 a (a + 1)| ≤ zeta / 12 := by
  have hdiff : DifferentiableOn ℝ (fun x => (f x).im) (Set.Icc a (a + 1)) :=
    fun x hx => (hasDerivAt_im_of_hasDerivAt (hderiv x hx)).differentiableAt
      |>.differentiableWithinAt
  have hdiffD := differentiableOn_derivWithin_im hderiv hderiv2
  have hiter (x : ℝ) :
      |iteratedDerivWithin 2 (fun y => (f y).im) (Set.Icc a (a + 1)) x| ≤ zeta :=
    iteratedDerivWithin_two_im_le hderiv hderiv2 hzeta hbound
  exact abs_trapezoidal_error_one_le hdiff hdiffD hiter
/-
  let I : Set ℝ := Set.Icc a (a + 1)
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  let fi : ℝ → ℝ := fun x => (f x).im
  let f1i : ℝ → ℝ := fun x => (f' x).im
  have hfi (x : ℝ) (hx : x ∈ I) : HasDerivAt fi (f1i x) x :=
    hasDerivAt_im_of_hasDerivAt (hderiv x hx)
  have hf1i (x : ℝ) (hx : x ∈ I) :
      HasDerivAt f1i (f'' x).im x :=
    hasDerivAt_im_of_hasDerivAt (hderiv2 x hx)
  have hdi (x : ℝ) (hx : x ∈ I) : derivWithin fi I x = f1i x :=
    (hfi x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
  have hdiffI : DifferentiableOn ℝ fi I := fun x hx =>
    (hfi x hx).differentiableAt.differentiableWithinAt
  have hdiffDI : DifferentiableOn ℝ (derivWithin fi I) I := by
    have hbase : DifferentiableOn ℝ f1i I := fun x hx =>
      (hf1i x hx).differentiableAt.differentiableWithinAt
    exact hbase.congr (fun x hx => hdi x hx)
  have hiterI (x : ℝ) : |iteratedDerivWithin 2 fi I x| ≤ zeta :=
    iteratedDerivWithin_two_im_le hderiv hderiv2 hzeta hbound
  simpa only [fi, I] using
    (trapezoidal_error_le hdiffI hdiffDI hiterI (N := 1) (by omega))
-/

private theorem abs_re_complex_trapezoidal_cell_error_le
    {f f' f'' : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    {zeta : ℝ} (hzeta : 0 ≤ zeta)
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖f'' x‖ ≤ zeta) :
    |((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).re| ≤ zeta / 12 := by
  have htrap := abs_trapezoidal_error_re_le hderiv hderiv2 hzeta hbound
  have hfcont : ContinuousOn f (Set.Icc a (a + 1)) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a (a + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hfcont.integrableOn_Icc
  have hreal :
      ((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).re =
        trapezoidal_error (fun x => (f x).re) 1 a (a + 1) := by
    have hri : (∫ x in a..a + 1, f x).re = ∫ x in a..a + 1, (f x).re := by
      simpa only [RCLike.re_to_complex] using (intervalIntegral_re hfint).symm
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.add_re, hri]
    simp [trapezoidal_error, trapezoidal_integral_one]
    ring
  rw [hreal]
  exact htrap
/-
  let I : Set ℝ := Set.Icc a (a + 1)
  have hab : a < a + 1 := by linarith
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  let fr : ℝ → ℝ := fun x => (f x).re
  let f1r : ℝ → ℝ := fun x => (f' x).re
  let f2r : ℝ → ℝ := fun x => (f'' x).re
  have hfr (x : ℝ) (hx : x ∈ I) : HasDerivAt fr (f1r x) x :=
    hasDerivAt_re_of_hasDerivAt (hderiv x hx)
  have hf1r (x : ℝ) (hx : x ∈ I) : HasDerivAt f1r (f2r x) x :=
    hasDerivAt_re_of_hasDerivAt (hderiv2 x hx)
  have hdr (x : ℝ) (hx : x ∈ I) : derivWithin fr I x = f1r x :=
    (hfr x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
  have hdiffR : DifferentiableOn ℝ fr I := fun x hx =>
    (hfr x hx).differentiableAt.differentiableWithinAt
  have hdiffDR : DifferentiableOn ℝ (derivWithin fr I) I := by
    have hbase : DifferentiableOn ℝ f1r I := fun x hx =>
      (hf1r x hx).differentiableAt.differentiableWithinAt
    exact hbase.congr (fun x hx => hdr x hx)
  have hiterR (x : ℝ) : |iteratedDerivWithin 2 fr I x| ≤ zeta := by
    exact iteratedDerivWithin_two_re_le hderiv hderiv2 hzeta hbound
  have htrap := trapezoidal_error_le hdiffR hdiffDR hiterR
    (N := 1) (by omega)
  have hfcont : ContinuousOn f I := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a (a + 1) := hfcont.intervalIntegrable
  have hreal :
      ((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).re =
        trapezoidal_error fr 1 a (a + 1) := by
    rw [map_sub, map_div, map_add, map_intervalIntegral]
    · simp [trapezoidal_error, trapezoidal_integral_one, fr]
    · exact hfint
  rw [hreal]
  simpa using htrap
-/

private theorem abs_im_complex_trapezoidal_cell_error_le
    {f f' f'' : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    {zeta : ℝ} (hzeta : 0 ≤ zeta)
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖f'' x‖ ≤ zeta) :
    |((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).im| ≤ zeta / 12 := by
  have htrap := abs_trapezoidal_error_im_le hderiv hderiv2 hzeta hbound
  have hfcont : ContinuousOn f (Set.Icc a (a + 1)) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a (a + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hfcont.integrableOn_Icc
  have himag :
      ((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).im =
        trapezoidal_error (fun x => (f x).im) 1 a (a + 1) := by
    have hii : (∫ x in a..a + 1, f x).im = ∫ x in a..a + 1, (f x).im := by
      simpa only [RCLike.im_to_complex] using (intervalIntegral_im hfint).symm
    rw [Complex.sub_im, Complex.div_ofNat_im, Complex.add_im, hii]
    simp [trapezoidal_error, trapezoidal_integral_one]
    ring
  rw [himag]
  exact htrap
/-
  let I : Set ℝ := Set.Icc a (a + 1)
  have hab : a < a + 1 := by linarith
  have huniq : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  let fi : ℝ → ℝ := fun x => (f x).im
  let f1i : ℝ → ℝ := fun x => (f' x).im
  let f2i : ℝ → ℝ := fun x => (f'' x).im
  have hfi (x : ℝ) (hx : x ∈ I) : HasDerivAt fi (f1i x) x :=
    hasDerivAt_im_of_hasDerivAt (hderiv x hx)
  have hf1i (x : ℝ) (hx : x ∈ I) : HasDerivAt f1i (f2i x) x :=
    hasDerivAt_im_of_hasDerivAt (hderiv2 x hx)
  have hdi (x : ℝ) (hx : x ∈ I) : derivWithin fi I x = f1i x :=
    (hfi x hx).hasDerivWithinAt.derivWithin (huniq.uniqueDiffWithinAt hx)
  have hdiffI : DifferentiableOn ℝ fi I := fun x hx =>
    (hfi x hx).differentiableAt.differentiableWithinAt
  have hdiffDI : DifferentiableOn ℝ (derivWithin fi I) I := by
    have hbase : DifferentiableOn ℝ f1i I := fun x hx =>
      (hf1i x hx).differentiableAt.differentiableWithinAt
    exact hbase.congr (fun x hx => hdi x hx)
  have hiterI (x : ℝ) : |iteratedDerivWithin 2 fi I x| ≤ zeta := by
    exact iteratedDerivWithin_two_im_le hderiv hderiv2 hzeta hbound
  have htrap := trapezoidal_error_le hdiffI hdiffDI hiterI
    (N := 1) (by omega)
  have hfcont : ContinuousOn f I := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a (a + 1) := hfcont.intervalIntegrable
  have himag :
      ((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).im =
        trapezoidal_error fi 1 a (a + 1) := by
    rw [map_sub, map_div, map_add, map_intervalIntegral]
    · simp [trapezoidal_error, trapezoidal_integral_one, fi]
    · exact hfint
  rw [himag]
  simpa using htrap
-/

/-- Complex-valued one-cell trapezoidal error, bounded using a uniform norm
bound for the second derivative. -/
theorem norm_complex_trapezoidal_cell_error_le
    {f f' f'' : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x ∈ Set.Icc a (a + 1), HasDerivAt f' (f'' x) x)
    {zeta : ℝ} (hzeta : 0 ≤ zeta)
    (hbound : ∀ x ∈ Set.Icc a (a + 1), ‖f'' x‖ ≤ zeta) :
    ‖(f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x‖ ≤ zeta / 6 := by
  have hRe := abs_re_complex_trapezoidal_cell_error_le
    ha hderiv hderiv2 hzeta hbound
  have hIm := abs_im_complex_trapezoidal_cell_error_le
    ha hderiv hderiv2 hzeta hbound
  calc
    ‖(f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x‖
        ≤ |((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).re| +
          |((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ zeta / 12 + zeta / 12 := add_le_add hRe hIm
    _ = zeta / 6 := by ring
/-
  have hRe := abs_re_complex_trapezoidal_cell_error_le
    ha hderiv hderiv2 hzeta hbound
  have hIm := abs_im_complex_trapezoidal_cell_error_le
    ha hderiv hderiv2 hzeta hbound
  calc
    ‖(f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x‖
        ≤ |((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).re| +
          |((f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ zeta / 12 + zeta / 12 := add_le_add hRe hIm
    _ = zeta / 6 := by ring
-/

private theorem sum_range_trapezoidal_endpoints
    (f : ℝ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        (f ((n : ℝ) + 1) + f ((n : ℝ) + 2)) / 2) +
        (f 1 + f ((N : ℝ) + 1)) / 2 =
      ∑ n ∈ Finset.range (N + 1), f ((n : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [← ih]
      ring

/-- Exact telescoping identity behind the composite trapezoidal rule, in the
form needed for a sum over the positive integers. -/
theorem sum_range_succ_sub_integral_eq_sum_trapezoidal_cell_error
    (f : ℝ → ℂ) (N : ℕ)
    (hint : ∀ n < N,
      IntervalIntegrable f volume ((n : ℝ) + 1) ((n : ℝ) + 2)) :
    (∑ n ∈ Finset.range (N + 1), f ((n : ℝ) + 1)) -
        (∫ x in (1 : ℝ)..(N : ℝ) + 1, f x) =
      (∑ n ∈ Finset.range N,
        ((f ((n : ℝ) + 1) + f ((n : ℝ) + 2)) / 2 -
          ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), f x)) +
        (f 1 + f ((N : ℝ) + 1)) / 2 := by
  have hintegral :
      (∑ n ∈ Finset.range N,
          ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), f x) =
        ∫ x in (1 : ℝ)..(N : ℝ) + 1, f x := by
    have hint' : ∀ n < N, IntervalIntegrable f volume
        ((n : ℝ) + 1) (((n + 1 : ℕ) : ℝ) + 1) := by
      intro n hn
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
        one_add_one_eq_two] using hint n hn
    have hsegments := intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (μ := volume) (a := fun n : ℕ => (n : ℝ) + 1)
      (n := N) hint'
    simpa only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two] using hsegments
  have htrap := sum_range_trapezoidal_endpoints f N
  rw [Finset.sum_sub_distrib, hintegral, ← htrap]
  abel

private theorem sum_range_inv_nat_succ_sq_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, ((((n : ℝ) + 1) ^ 2)⁻¹)) ≤ 2 := by
  have hset : Finset.Icc 1 N = (Finset.range N).image (fun n => n + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hn
      refine ⟨n - 1, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      omega
  have hinj : Set.InjOn (fun n : ℕ => n + 1) ↑(Finset.range N) := by
    intro m hm n hn h
    exact Nat.add_right_cancel h
  have hsum :
      (∑ n ∈ Finset.range N, ((((n : ℝ) + 1) ^ 2)⁻¹)) =
        ∑ n ∈ Finset.Icc 1 N, (((n : ℝ) ^ 2)⁻¹) := by
    rw [hset, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    rfl
  rw [hsum]
  have hset' : Finset.Icc 1 N = Finset.Ioo 0 (N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [hset']
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

/-- A uniform second-order sum--integral comparison for the logarithmic
phase.  Unlike the first-derivative comparison, its error is bounded
independently of the length of the sum. -/
theorem norm_sum_range_natLogTwist_sub_integral_le
    (t : ℝ) (N : ℕ) (ht : t ≠ 0) :
    ‖(∑ n ∈ Finset.range (N + 1),
          LogPhaseSum.natLogTwist (n + 1) t) -
        ∫ x in (1 : ℝ)..(N : ℝ) + 1, LogPhaseSum.logPhase t x‖ ≤
      |t| * Real.sqrt (t ^ 2 + 1) / 3 + 1 := by
  let f : ℝ → ℂ := LogPhaseSum.logPhase t
  let f' : ℝ → ℂ := fun x =>
    -(Complex.I * (t : ℂ)) *
      (x : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1)
  let f'' : ℝ → ℂ := fun x =>
    -(Complex.I * (t : ℂ)) * (-(Complex.I * (t : ℂ)) - 1) *
      (x : ℂ) ^ (-(Complex.I * (t : ℂ)) - 1 - 1)
  let K : ℝ := |t| * Real.sqrt (t ^ 2 + 1)
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hcell (n : ℕ) (hn : n < N) :
      ‖(f ((n : ℝ) + 1) + f ((n : ℝ) + 2)) / 2 -
          ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), f x‖ ≤
        (K / (((n : ℝ) + 1) ^ 2)) / 6 := by
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have hraw := norm_complex_trapezoidal_cell_error_le ha
        (f := f) (f' := f') (f'' := f'')
        (fun x hx =>
          LogPhaseSum.hasDerivAt_logPhase (ne_of_gt (ha.trans_le hx.1)) ht)
        (fun x hx =>
          LogPhaseSum.hasDerivAt_logPhase_deriv
            (ne_of_gt (ha.trans_le hx.1)))
        (div_nonneg hK (sq_nonneg _))
        (fun x hx => by
          have hxpos : 0 < x := ha.trans_le hx.1
          have hnorm : ‖f'' x‖ = K / x ^ 2 := by
            dsimp [f'', K]
            convert LogPhaseSum.norm_logPhase_secondDeriv (t := t) hxpos using 1 <;>
              ring
          rw [hnorm]
          exact div_le_div_of_nonneg_left hK (sq_pos_of_pos ha)
            ((sq_le_sq₀ ha.le (ha.le.trans hx.1)).2 hx.1))
    convert hraw using 1 <;> ring_nf
  have hint (n : ℕ) (hn : n < N) :
      IntervalIntegrable f volume ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have hcont : ContinuousOn f
        (Set.Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) := fun x hx =>
      (LogPhaseSum.hasDerivAt_logPhase
        (ne_of_gt (ha.trans_le hx.1)) ht).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by linarith)
  have hid := sum_range_succ_sub_integral_eq_sum_trapezoidal_cell_error f N hint
  have herrors :
      ‖∑ n ∈ Finset.range N,
          ((f ((n : ℝ) + 1) + f ((n : ℝ) + 2)) / 2 -
            ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), f x)‖ ≤ K / 3 := by
    calc
      ‖∑ n ∈ Finset.range N,
          ((f ((n : ℝ) + 1) + f ((n : ℝ) + 2)) / 2 -
            ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), f x)‖ ≤
          ∑ n ∈ Finset.range N,
            ‖(f ((n : ℝ) + 1) + f ((n : ℝ) + 2)) / 2 -
              ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), f x‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, (K / (((n : ℝ) + 1) ^ 2)) / 6 := by
        exact Finset.sum_le_sum fun n hn => hcell n (Finset.mem_range.mp hn)
      _ = (K / 6) * ∑ n ∈ Finset.range N, ((((n : ℝ) + 1) ^ 2)⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ (K / 6) * 2 := by
        gcongr
        exact sum_range_inv_nat_succ_sq_le_two N
      _ = K / 3 := by ring
  have hend : ‖(f 1 + f ((N : ℝ) + 1)) / 2‖ ≤ 1 := by
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    calc
      ‖(f 1 + f ((N : ℝ) + 1)) / 2‖ =
          ‖f 1 + f ((N : ℝ) + 1)‖ / 2 := by rw [norm_div, htwo]
      _ ≤
          (‖f 1‖ + ‖f ((N : ℝ) + 1)‖) / 2 := by
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      _ = 1 := by
        rw [show ‖f 1‖ = 1 by
          exact LogPhaseSum.norm_logPhase t (by positivity)]
        rw [show ‖f ((N : ℝ) + 1)‖ = 1 by
          exact LogPhaseSum.norm_logPhase t (by positivity)]
        norm_num
  have hsum : (∑ n ∈ Finset.range (N + 1),
      LogPhaseSum.natLogTwist (n + 1) t) =
      ∑ n ∈ Finset.range (N + 1), f ((n : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [f, LogPhaseSum.natLogTwist, Nat.cast_add, Nat.cast_one]
  rw [hsum, hid]
  exact (norm_add_le _ _).trans (by
    dsimp [K] at herrors
    linarith)

/-- The source-form power sum: the main term is the elementary integral
from zero, and the remainder is absolute for bounded `t`. -/
theorem norm_sum_range_natLogTwist_sub_main_le
    (t : ℝ) (N : ℕ) (ht : t ≠ 0) :
    ‖(∑ n ∈ Finset.range (N + 1),
          LogPhaseSum.natLogTwist (n + 1) t) -
        (((N + 1 : ℕ) : ℂ) ^
            (1 - Complex.I * (t : ℂ))) /
          (1 - Complex.I * (t : ℂ))‖ ≤
      |t| * Real.sqrt (t ^ 2 + 1) / 3 + 2 := by
  let S : ℂ := ∑ n ∈ Finset.range (N + 1),
    LogPhaseSum.natLogTwist (n + 1) t
  let I : ℂ := ∫ x in (1 : ℝ)..(N : ℝ) + 1,
    LogPhaseSum.logPhase t x
  let M : ℂ := (((N + 1 : ℕ) : ℂ) ^
      (1 - Complex.I * (t : ℂ))) / (1 - Complex.I * (t : ℂ))
  have hSI : ‖S - I‖ ≤ |t| * Real.sqrt (t ^ 2 + 1) / 3 + 1 := by
    exact norm_sum_range_natLogTwist_sub_integral_le t N ht
  have hden : 1 ≤ ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ := by
    have hsq : ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    nlinarith [sq_nonneg t,
      norm_nonneg ((1 : ℂ) - Complex.I * (t : ℂ))]
  have hIM : ‖I - M‖ ≤ 1 := by
    have hformula := LogPhaseSum.integral_logPhase
      (1 : ℝ) ((N : ℝ) + 1) t
    have hden0 : (1 : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
      intro h
      apply_fun Complex.re at h
      norm_num at h
    have heq : I - M = -((1 : ℂ) / (1 - Complex.I * (t : ℂ))) := by
      dsimp [I, M]
      rw [hformula]
      rw [sub_div]
      push_cast
      rw [Complex.one_cpow]
      field_simp
      ring
    rw [heq, norm_neg, norm_div, norm_one]
    exact (div_le_one (by positivity)).2 hden
  change ‖S - M‖ ≤ _
  calc
    ‖S - M‖ = ‖(S - I) + (I - M)‖ := by ring_nf
    _ ≤ ‖S - I‖ + ‖I - M‖ := norm_add_le _ _
    _ ≤ (|t| * Real.sqrt (t ^ 2 + 1) / 3 + 1) + 1 :=
      add_le_add hSI hIM
    _ = |t| * Real.sqrt (t ^ 2 + 1) / 3 + 2 := by ring

/-- On the small-twist range used in the real Granville--Soundararajan
branch, the logarithmic-phase power sum has an absolute remainder. -/
theorem norm_sum_range_natLogTwist_sub_main_le_three
    (t : ℝ) (N : ℕ) (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖(∑ n ∈ Finset.range (N + 1),
          LogPhaseSum.natLogTwist (n + 1) t) -
        (((N + 1 : ℕ) : ℂ) ^
            (1 - Complex.I * (t : ℂ))) /
          (1 - Complex.I * (t : ℂ))‖ ≤ 3 := by
  refine (norm_sum_range_natLogTwist_sub_main_le t N ht).trans ?_
  have ht_sq : t ^ 2 ≤ 1 := by
    have hsq :=
      (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)).2 ht_small
    simpa only [sq_abs, one_pow] using hsq
  have hsqrt : Real.sqrt (t ^ 2 + 1) ≤ 2 := by
    have hnonneg : 0 ≤ t ^ 2 + 1 := by positivity
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have habs : 0 ≤ |t| := abs_nonneg t
  nlinarith

/-- Positive-prefix form of the small-twist power-sum estimate. -/
theorem norm_sum_Ioc_natLogTwist_sub_main_le_three
    (t : ℝ) {M : ℕ} (hM : 0 < M) (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖(∑ m ∈ Finset.Ioc 0 M, LogPhaseSum.natLogTwist m t) -
        ((M : ℂ) ^ (1 - Complex.I * (t : ℂ))) /
          (1 - Complex.I * (t : ℂ))‖ ≤ 3 := by
  have hset : Finset.Ioc 0 M =
      (Finset.range M).image (fun n => n + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hn
      refine ⟨n - 1, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      omega
  have hinj : Set.InjOn (fun n : ℕ => n + 1) ↑(Finset.range M) := by
    intro m hm n hn h
    exact Nat.add_right_cancel h
  have hMpred : M - 1 + 1 = M := by omega
  rw [hset, Finset.sum_image hinj]
  simpa only [hMpred, Nat.cast_add, Nat.cast_one] using
    norm_sum_range_natLogTwist_sub_main_le_three t (M - 1) ht ht_small

/-- The form used after divisor convolution: the main term is evaluated at
the real quotient `N / d`, rather than at its floor. -/
theorem norm_sum_Ioc_natLogTwist_sub_realQuotient_main_le_four
    (t : ℝ) {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖(∑ m ∈ Finset.Ioc 0 (N / d), LogPhaseSum.natLogTwist m t) -
        ((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
            (1 - Complex.I * (t : ℂ))) /
          (1 - Complex.I * (t : ℂ))‖ ≤ 4 := by
  have hM : 0 < N / d := Nat.div_pos hdN hd
  let M : ℝ := (N / d : ℕ)
  let z : ℝ := (N : ℝ) / (d : ℝ)
  let main : ℝ → ℂ := fun y =>
    ((y : ℂ) ^ (1 - Complex.I * (t : ℂ))) /
      (1 - Complex.I * (t : ℂ))
  have hfloor : M ≤ z := by
    dsimp [M, z]
    exact Nat.cast_div_le
  have hfloorUpper : z < M + 1 := by
    dsimp [M, z]
    have hnat : N < (N / d + 1) * d :=
      (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
    have hreal : (N : ℝ) < (((N / d + 1) * d : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    rw [div_lt_iff₀ hdR]
    push_cast at hreal ⊢
    exact hreal
  have hmain : ‖main M - main z‖ ≤ 1 := by
    have hint : (∫ x in M..z, LogPhaseSum.logPhase t x) =
        main z - main M := by
      dsimp [main]
      rw [LogPhaseSum.integral_logPhase]
      ring
    have hnormIntegral :
        ‖∫ x in M..z, LogPhaseSum.logPhase t x‖ ≤ |z - M| := by
      have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x => LogPhaseSum.logPhase t x) (C := (1 : ℝ))
        (a := M) (b := z) (fun x hx => by
          have hxIcc : x ∈ Set.Icc M z := by
            rw [← Set.uIcc_of_le hfloor]
            exact Set.uIoc_subset_uIcc hx
          have hMpos : 0 < M := by
            dsimp [M]
            exact_mod_cast hM
          exact (LogPhaseSum.norm_logPhase t (hMpos.trans_le hxIcc.1)).le)
      simpa using hraw
    rw [hint, norm_sub_rev] at hnormIntegral
    exact hnormIntegral.trans (by
      rw [abs_of_nonneg (sub_nonneg.mpr hfloor)]
      linarith)
  have hsum := norm_sum_Ioc_natLogTwist_sub_main_le_three
    t hM ht ht_small
  change ‖(∑ m ∈ Finset.Ioc 0 (N / d),
      LogPhaseSum.natLogTwist m t) - main z‖ ≤ 4
  calc
    ‖(∑ m ∈ Finset.Ioc 0 (N / d),
        LogPhaseSum.natLogTwist m t) - main z‖ =
        ‖((∑ m ∈ Finset.Ioc 0 (N / d),
          LogPhaseSum.natLogTwist m t) - main M) +
            (main M - main z)‖ := by ring_nf
    _ ≤ ‖(∑ m ∈ Finset.Ioc 0 (N / d),
          LogPhaseSum.natLogTwist m t) - main M‖ +
        ‖main M - main z‖ := norm_add_le _ _
    _ ≤ 3 + 1 := add_le_add (by simpa [main, M] using hsum) hmain
    _ = 4 := by norm_num

end

end Erdos67
