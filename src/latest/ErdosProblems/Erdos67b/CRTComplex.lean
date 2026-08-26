import ErdosProblems.Erdos67b.LogCRTConcentration

/-!
# Complex CRT concentration with a finite uniform mean

Apply the already proved real Hoeffding estimate to real and imaginary
parts and retain explicit constants for the entropy rare-event step.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Erdos67b

noncomputable section

theorem integral_residueMeasure_eq_sum (a : ℕ) [NeZero a] (f : ZMod a → ℝ) :
    (∫ x, f x ∂residueMeasure a) = (a : ℝ)⁻¹ * ∑ x, f x := by
  rw [residueMeasure, uniformMeasure, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ZMod.card, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, Finset.mul_sum]

/-- A complex sum evaluated at the coordinates of one CRT residue. -/
def crtComplexSum {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (f : (i : ι) → ZMod (a i) → ℂ)
    (z : ZMod (∏ i, a i)) : ℂ :=
  ∑ i ∈ s, f i (ZMod.prodEquivPi a hcoprime z i)

/-- The exact finite coordinate mean. -/
def crtComplexMean {ι : Type*} [Fintype ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (s : Finset ι) (f : (i : ι) → ZMod (a i) → ℂ) : ℂ :=
  ∑ i ∈ s, (a i : ℝ)⁻¹ • ∑ x, f i x

theorem crtComplexSum_re {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (f : (i : ι) → ZMod (a i) → ℂ)
    (z : ZMod (∏ i, a i)) :
    (crtComplexSum a hcoprime s f z).re = crtBilinearSum a hcoprime s
      (fun _ ↦ 1) (fun i x ↦ (f i x).re) (fun _ _ ↦ 1) z := by
  simp [crtComplexSum, crtBilinearSum, bilinearSum, bilinearObservable]

theorem crtComplexSum_im {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (f : (i : ι) → ZMod (a i) → ℂ)
    (z : ZMod (∏ i, a i)) :
    (crtComplexSum a hcoprime s f z).im = crtBilinearSum a hcoprime s
      (fun _ ↦ 1) (fun i x ↦ (f i x).im) (fun _ _ ↦ 1) z := by
  simp [crtComplexSum, crtBilinearSum, bilinearSum, bilinearObservable]

theorem crtComplexMean_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (s : Finset ι) (f : (i : ι) → ZMod (a i) → ℂ) :
    (crtComplexMean a s f).re = bilinearMean a s
      (fun _ ↦ 1) (fun i x ↦ (f i x).re) (fun _ _ ↦ 1) := by
  simp [crtComplexMean, bilinearMean, bilinearObservable, integral_residueMeasure_eq_sum]

theorem crtComplexMean_im {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (s : Finset ι) (f : (i : ι) → ZMod (a i) → ℂ) :
    (crtComplexMean a s f).im = bilinearMean a s
      (fun _ ↦ 1) (fun i x ↦ (f i x).im) (fun _ _ ↦ 1) := by
  simp [crtComplexMean, bilinearMean, bilinearObservable, integral_residueMeasure_eq_sum]

/-- Complex Hoeffding on a single uniform CRT residue. -/
theorem crt_bounded_complex_concentration
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)] [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (f : (i : ι) → ZMod (a i) → ℂ) (radius : ι → ℝ≥0)
    (hbound : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ (radius i : ℝ))
    {t : ℝ} (ht : 0 ≤ t) :
    (residueMeasure (∏ i, a i)).real
      {z | t ≤ ‖crtComplexSum a hcoprime s f z - crtComplexMean a s f‖} ≤
      4 * Real.exp (-t ^ 2 / (8 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) := by
  let A : ZMod (∏ i, a i) → ℂ := fun z ↦
    crtComplexSum a hcoprime s f z - crtComplexMean a s f
  have hre := crt_bounded_bilinear_concentration a hcoprime s (fun _ ↦ 1)
    (fun i x ↦ (f i x).re) (fun _ _ ↦ 1) radius
    (by intro i hi x; simpa only [bilinearObservable, one_mul, mul_one] using
      (Complex.abs_re_le_norm (f i x)).trans (hbound i hi x)) (show 0 ≤ t / 2 by positivity)
  have him := crt_bounded_bilinear_concentration a hcoprime s (fun _ ↦ 1)
    (fun i x ↦ (f i x).im) (fun _ _ ↦ 1) radius
    (by intro i hi x; simpa only [bilinearObservable, one_mul, mul_one] using
      (Complex.abs_im_le_norm (f i x)).trans (hbound i hi x)) (show 0 ≤ t / 2 by positivity)
  have hsub : {z | t ≤ ‖A z‖} ⊆ {z | t / 2 ≤ |(A z).re|} ∪ {z | t / 2 ≤ |(A z).im|} := by
    intro z hz
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
    have hnorm := Complex.norm_le_abs_re_add_abs_im (A z)
    change t ≤ ‖A z‖ at hz
    linarith
  have hReEq : {z | t / 2 ≤ |(A z).re|} =
      {z | t / 2 ≤ |crtBilinearSum a hcoprime s (fun _ ↦ 1)
          (fun i x ↦ (f i x).re) (fun _ _ ↦ 1) z -
        bilinearMean a s (fun _ ↦ 1) (fun i x ↦ (f i x).re) (fun _ _ ↦ 1)|} := by
    simp only [A, Complex.sub_re, crtComplexSum_re, crtComplexMean_re]
  have hImEq : {z | t / 2 ≤ |(A z).im|} =
      {z | t / 2 ≤ |crtBilinearSum a hcoprime s (fun _ ↦ 1)
          (fun i x ↦ (f i x).im) (fun _ _ ↦ 1) z -
        bilinearMean a s (fun _ ↦ 1) (fun i x ↦ (f i x).im) (fun _ _ ↦ 1)|} := by
    simp only [A, Complex.sub_im, crtComplexSum_im, crtComplexMean_im]
  have h := (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (hReEq ▸ hre) (hImEq ▸ him)))
  change (residueMeasure (∏ i, a i)).real {z | t ≤ ‖A z‖} ≤ _
  have harg : -(t / 2) ^ 2 / (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0)) =
      -t ^ 2 / (8 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [harg] at h
  linarith

theorem finiteEventMass_uniform_finset
    {α : Type*} [Fintype α] [Nonempty α] (E : Finset α) :
    finiteEventMass (uniformFiniteLaw α) (E : Set α) =
      (E.card : ℝ) / Fintype.card α := by
  classical
  simp [finiteEventMass, uniformFiniteLaw_apply, Set.indicator_apply, div_eq_mul_inv]

/-- Complex CRT tails in exactly the exponential-cardinality form used
by the entropy transfer. -/
theorem crt_complex_tail_card_mul_exp_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)] [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (f : (i : ι) → ZMod (a i) → ℂ) (radius : ι → ℝ≥0)
    (hbound : ∀ i ∈ s, ∀ x, ‖f i x‖ ≤ (radius i : ℝ))
    {t r : ℝ} (ht : 0 ≤ t)
    (hr : r + Real.log 4 ≤ t ^ 2 / (8 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) :
    ((Finset.univ.filter fun z : ZMod (∏ i, a i) ↦
        t ≤ ‖crtComplexSum a hcoprime s f z - crtComplexMean a s f‖).card : ℝ) *
      Real.exp r ≤ (∏ i, a i : ℕ) := by
  classical
  let E : Finset (ZMod (∏ i, a i)) := Finset.univ.filter fun z ↦
    t ≤ ‖crtComplexSum a hcoprime s f z - crtComplexMean a s f‖
  have hE : (E : Set (ZMod (∏ i, a i))) =
      {z | t ≤ ‖crtComplexSum a hcoprime s f z - crtComplexMean a s f‖} := by
    ext z
    simp only [E, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  have htail := crt_bounded_complex_concentration a hcoprime s f radius hbound ht
  have hmass : (E.card : ℝ) / (∏ i, a i : ℕ) ≤
      4 * Real.exp (-t ^ 2 / (8 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) := by
    have hevent := finiteEventMass_uniform_finset E
    rw [finiteEventMass_uniformFiniteLaw, hE] at hevent
    change (residueMeasure (∏ i, a i)).real _ = _ at hevent
    rw [hevent] at htail
    simpa only [ZMod.card] using htail
  have hprod : (0 : ℝ) < (∏ i, a i : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (∏ i, a i))
  have hmul := mul_le_mul_of_nonneg_right hmass (Real.exp_pos r).le
  have hexp : (4 * Real.exp (-t ^ 2 / (8 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0)))) *
      Real.exp r ≤ 1 := by
    rw [mul_assoc, ← Real.exp_add]
    have he := Real.exp_le_exp.mpr (show
      -t ^ 2 / (8 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0)) + r ≤ -Real.log 4 by
        rw [neg_div]; linarith)
    have he' := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 4)
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)] using he'
  have h := hmul.trans hexp
  change (E.card : ℝ) * Real.exp r ≤ _
  have h' : ((E.card : ℝ) * Real.exp r) / (∏ i, a i : ℕ) ≤ 1 := by
    simpa only [div_mul_eq_mul_div] using h
  exact (div_le_one hprod).mp h'

end

end Erdos67b
