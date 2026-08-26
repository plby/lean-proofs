import ErdosProblems.Erdos1002.Sawtooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# L² Fourier series for the sawtooth and Bernoulli mark

This file places the one-period functions from `Erdos1002.Sawtooth` in
`L²(AddCircle 1, ℂ)` with respect to normalized Haar measure.  It then applies
mathlib's complete Fourier Hilbert basis and rewrites every coefficient using
the exact calculations from the preceding file.

The resulting `HasSum` statements are convergence in the `L²` norm.  They do
not assert pointwise equality at the jump points of the sawtooth.
-/

open MeasureTheory Set
open scoped ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

/-- The sawtooth, periodized as a function on the unit additive circle. -/
def sawtoothCircle : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 fun x : ℝ => (sawtooth x : ℂ)

/-- The Bernoulli mark, periodized as a function on the unit additive circle. -/
def bernoulliMarkCircle : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 fun x : ℝ => (bernoulliMark x : ℂ)

theorem sawtoothCircle_coe {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    sawtoothCircle (x : AddCircle (1 : ℝ)) = sawtooth x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using! hx)

theorem bernoulliMarkCircle_coe {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    bernoulliMarkCircle (x : AddCircle (1 : ℝ)) = bernoulliMark x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using! hx)

private theorem sawtooth_memLp_Ioc :
    MemLp (fun x : ℝ => (sawtooth x : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound sawtooth_measurable.complex_ofReal.aestronglyMeasurable (1 / 2)
  filter_upwards with x
  simpa only [Complex.norm_real] using! abs_sawtooth_le_half x

private theorem bernoulliMark_memLp_Ioc :
    MemLp (fun x : ℝ => (bernoulliMark x : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound bernoulliMark_measurable.complex_ofReal.aestronglyMeasurable (1 / 8)
  filter_upwards with x
  simpa only [Complex.norm_real] using! abs_bernoulliMark_le_one_eighth x

theorem sawtoothCircle_memLp :
    MemLp sawtoothCircle 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc : MemLp (fun x : ℝ => (sawtooth x : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    simpa using! sawtooth_memLp_Ioc
  exact (hIoc.memLp_liftIoc.haarAddCircle :
    MemLp (AddCircle.liftIoc 1 0 fun x : ℝ => (sawtooth x : ℂ)) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))

theorem bernoulliMarkCircle_memLp :
    MemLp bernoulliMarkCircle 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc : MemLp (fun x : ℝ => (bernoulliMark x : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    simpa using! bernoulliMark_memLp_Ioc
  exact (hIoc.memLp_liftIoc.haarAddCircle :
    MemLp (AddCircle.liftIoc 1 0 fun x : ℝ => (bernoulliMark x : ℂ)) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))

/-- The `L²` class of the periodized sawtooth. -/
def sawtoothL2 : Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  sawtoothCircle_memLp.toLp sawtoothCircle

/-- The `L²` class of the periodized Bernoulli mark. -/
def bernoulliMarkL2 : Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  bernoulliMarkCircle_memLp.toLp bernoulliMarkCircle

theorem sawtoothL2_coe_ae :
    (sawtoothL2 : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle] sawtoothCircle := by
  exact sawtoothCircle_memLp.coeFn_toLp

theorem bernoulliMarkL2_coe_ae :
    (bernoulliMarkL2 : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      bernoulliMarkCircle := by
  exact bernoulliMarkCircle_memLp.coeFn_toLp

/-- The exact coefficient sequence of the centered sawtooth. -/
def sawtoothFourierCoefficient (m : ℤ) : ℂ :=
  if m = 0 then 0 else 1 / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))

/-- The exact coefficient sequence of the Bernoulli mark. -/
def bernoulliMarkFourierCoefficient (m : ℤ) : ℂ :=
  if m = 0 then 1 / 12 else -(1 / (4 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2))

theorem fourierCoeff_sawtoothL2 (m : ℤ) :
    fourierCoeff (sawtoothL2 : AddCircle (1 : ℝ) → ℂ) m =
      sawtoothFourierCoefficient m := by
  rw [congrFun (fourierCoeff_congr_ae sawtoothL2_coe_ae) m]
  rw [show sawtoothCircle =
      AddCircle.liftIoc 1 0 (fun x : ℝ => (sawtooth x : ℂ)) by rfl]
  rw [fourierCoeff_liftIoc_eq]
  by_cases hm : m = 0
  · subst m
    rw [sawtoothFourierCoefficient]
    simp only [if_pos]
    convert! sawtooth_fourierCoeff_zero using 1
    congr 1
    norm_num
  · rw [sawtoothFourierCoefficient, if_neg hm]
    convert! sawtooth_fourierCoeff_nonzero m hm using 1
    congr 1
    norm_num

theorem fourierCoeff_bernoulliMarkL2 (m : ℤ) :
    fourierCoeff (bernoulliMarkL2 : AddCircle (1 : ℝ) → ℂ) m =
      bernoulliMarkFourierCoefficient m := by
  rw [congrFun (fourierCoeff_congr_ae bernoulliMarkL2_coe_ae) m]
  rw [show bernoulliMarkCircle =
      AddCircle.liftIoc 1 0 (fun x : ℝ => (bernoulliMark x : ℂ)) by rfl]
  rw [fourierCoeff_liftIoc_eq]
  by_cases hm : m = 0
  · subst m
    rw [bernoulliMarkFourierCoefficient]
    simp only [if_pos]
    convert! bernoulliMark_fourierCoeff_zero using 1
    congr 1
    norm_num
  · rw [bernoulliMarkFourierCoefficient, if_neg hm]
    convert! bernoulliMark_fourierCoeff_nonzero m hm using 1
    · congr 1
      norm_num
    · ring_nf

/-- A single Fourier term of the centered sawtooth in `L²(AddCircle 1)`. -/
def sawtoothFourierTerm (m : ℤ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  sawtoothFourierCoefficient m • fourierLp 2 m

/-- A single Fourier term of the Bernoulli mark in `L²(AddCircle 1)`. -/
def bernoulliMarkFourierTerm (m : ℤ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  bernoulliMarkFourierCoefficient m • fourierLp 2 m

/-- The exact Fourier expansion of the sawtooth, converging in `L²`. -/
theorem hasSum_sawtoothFourierSeries :
    HasSum sawtoothFourierTerm sawtoothL2 := by
  simpa only [sawtoothFourierTerm, fourierCoeff_sawtoothL2] using!
    hasSum_fourier_series_L2 sawtoothL2

/-- The exact Fourier expansion of the Bernoulli mark, converging in `L²`. -/
theorem hasSum_bernoulliMarkFourierSeries :
    HasSum bernoulliMarkFourierTerm bernoulliMarkL2 := by
  simpa only [bernoulliMarkFourierTerm, fourierCoeff_bernoulliMarkL2] using!
    hasSum_fourier_series_L2 bernoulliMarkL2

/-! ## The paper's sums indexed by nonzero integers -/

/-- The type of nonzero integer Fourier modes. -/
abbrev NonzeroFourierIndex := {m : ℤ // m ≠ 0}

private def nonzeroEquivFinsetComplZero :
    NonzeroFourierIndex ≃ {m : ℤ // m ∉ ({0} : Finset ℤ)} where
  toFun m := ⟨m, by simpa using! m.property⟩
  invFun m := ⟨m, by simpa using! m.property⟩
  left_inv m := by rfl
  right_inv m := by rfl

/-- The `m`-th term in the paper's nonzero-mode sawtooth series. -/
def sawtoothNonzeroFourierTerm (m : NonzeroFourierIndex) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))) • fourierLp 2 (m : ℤ)

/-- The positive tail term occurring after the minus sign in the Fourier series for `V`. -/
def bernoulliMarkTailTerm (m : NonzeroFourierIndex) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  (1 / (4 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2)) • fourierLp 2 (m : ℤ)

private theorem sawtoothFourierTerm_subtype (m : NonzeroFourierIndex) :
    sawtoothFourierTerm (m : ℤ) = sawtoothNonzeroFourierTerm m := by
  simp [sawtoothFourierTerm, sawtoothFourierCoefficient,
    sawtoothNonzeroFourierTerm, m.property]

private theorem bernoulliMarkFourierTerm_subtype (m : NonzeroFourierIndex) :
    bernoulliMarkFourierTerm (m : ℤ) = -bernoulliMarkTailTerm m := by
  simp [bernoulliMarkFourierTerm, bernoulliMarkFourierCoefficient,
    bernoulliMarkTailTerm, m.property, neg_smul]

theorem summable_sawtoothNonzeroFourierTerm :
    Summable sawtoothNonzeroFourierTerm := by
  have h := hasSum_sawtoothFourierSeries.summable.subtype {m : ℤ | m ≠ 0}
  exact h.congr sawtoothFourierTerm_subtype

theorem summable_bernoulliMarkTailTerm :
    Summable bernoulliMarkTailTerm := by
  have hfull := hasSum_bernoulliMarkFourierSeries.summable.subtype {m : ℤ | m ≠ 0}
  have hneg : Summable (fun m : NonzeroFourierIndex => -bernoulliMarkTailTerm m) :=
    hfull.congr bernoulliMarkFourierTerm_subtype
  simpa only [neg_neg] using! hneg.neg

private theorem tsum_sawtoothNonzeroFourierTerm :
    ∑' m : NonzeroFourierIndex, sawtoothNonzeroFourierTerm m = sawtoothL2 := by
  have hreindex :
      (∑' m : NonzeroFourierIndex, sawtoothNonzeroFourierTerm m) =
        ∑' m : {m : ℤ // m ∉ ({0} : Finset ℤ)}, sawtoothFourierTerm (m : ℤ) := by
    simpa [Function.comp_def, nonzeroEquivFinsetComplZero,
      sawtoothFourierTerm_subtype] using!
      (nonzeroEquivFinsetComplZero.tsum_eq
        (fun m : {m : ℤ // m ∉ ({0} : Finset ℤ)} => sawtoothFourierTerm (m : ℤ)))
  have hdecomp :=
    hasSum_sawtoothFourierSeries.summable.sum_add_tsum_subtype_compl ({0} : Finset ℤ)
  rw [hasSum_sawtoothFourierSeries.tsum_eq] at hdecomp
  rw [← hreindex] at hdecomp
  simpa [sawtoothFourierTerm, sawtoothFourierCoefficient] using! hdecomp

/-- The paper's sum over `m ≠ 0` converges to the sawtooth in `L²`. -/
theorem hasSum_sawtoothNonzeroFourierSeries :
    HasSum sawtoothNonzeroFourierTerm sawtoothL2 := by
  rw [← tsum_sawtoothNonzeroFourierTerm]
  exact summable_sawtoothNonzeroFourierTerm.hasSum

private theorem bernoulliMarkL2_eq_constant_sub_tsum_aux :
    bernoulliMarkL2 =
      (1 / 12 : ℂ) • fourierLp 2 (0 : ℤ) -
        ∑' m : NonzeroFourierIndex, bernoulliMarkTailTerm m := by
  have hreindex :
      (∑' m : NonzeroFourierIndex, -bernoulliMarkTailTerm m) =
        ∑' m : {m : ℤ // m ∉ ({0} : Finset ℤ)}, bernoulliMarkFourierTerm (m : ℤ) := by
    simpa [Function.comp_def, nonzeroEquivFinsetComplZero,
      bernoulliMarkFourierTerm_subtype] using!
      (nonzeroEquivFinsetComplZero.tsum_eq
        (fun m : {m : ℤ // m ∉ ({0} : Finset ℤ)} => bernoulliMarkFourierTerm (m : ℤ)))
  have hdecomp :=
    hasSum_bernoulliMarkFourierSeries.summable.sum_add_tsum_subtype_compl
      ({0} : Finset ℤ)
  rw [hasSum_bernoulliMarkFourierSeries.tsum_eq] at hdecomp
  rw [← hreindex] at hdecomp
  have hseries :
      (1 / 12 : ℂ) • fourierLp 2 (0 : ℤ) +
          ∑' m : NonzeroFourierIndex, -bernoulliMarkTailTerm m = bernoulliMarkL2 := by
    simpa [bernoulliMarkFourierTerm, bernoulliMarkFourierCoefficient] using! hdecomp
  rw [tsum_neg] at hseries
  simpa [sub_eq_add_neg] using! hseries.symm

/-- In `L²`, `V = 1/12 - ∑_{m ≠ 0} e(mx)/(4π²m²)`. -/
theorem bernoulliMarkL2_eq_constant_sub_tsum :
    bernoulliMarkL2 =
      (1 / 12 : ℂ) • fourierLp 2 (0 : ℤ) -
        ∑' m : NonzeroFourierIndex, bernoulliMarkTailTerm m :=
  bernoulliMarkL2_eq_constant_sub_tsum_aux

/-- Equivalently, the positive Fourier tail sums to `1/12 - V` in `L²`. -/
theorem hasSum_bernoulliMarkTail :
    HasSum bernoulliMarkTailTerm
      ((1 / 12 : ℂ) • fourierLp 2 (0 : ℤ) - bernoulliMarkL2) := by
  have htsum : (∑' m : NonzeroFourierIndex, bernoulliMarkTailTerm m) =
      (1 / 12 : ℂ) • fourierLp 2 (0 : ℤ) - bernoulliMarkL2 := by
    rw [bernoulliMarkL2_eq_constant_sub_tsum]
    abel
  rw [← htsum]
  exact summable_bernoulliMarkTailTerm.hasSum

end

end Erdos1002
