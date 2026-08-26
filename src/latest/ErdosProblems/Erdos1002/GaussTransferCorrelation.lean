import ErdosProblems.Erdos1002.GaussTransferAdjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Correlation identities for the Gauss transfer operator

This file turns the setwise Perron--Frobenius identity into an equality of
measures and then into an integral identity.  Keeping this bridge explicit
prevents later weak-law estimates from silently treating the normalized
transfer kernel as an adjoint operator.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

/-- Pushing a measure with density `f` through `m` Gauss iterates gives the
measure whose density is the `m`-fold nonnegative Gauss transfer of `f`. -/
theorem map_gaussOrbit_withDensity_eq_gaussTransferENN_iterate
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (m : ℕ) :
    Measure.map (gaussOrbit m) (gaussMeasure.withDensity f) =
      gaussMeasure.withDensity ((gaussTransferENN^[m]) f) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_gaussOrbit m) hs,
    withDensity_apply f (hs.preimage (measurable_gaussOrbit m)),
    withDensity_apply ((gaussTransferENN^[m]) f) hs]
  exact (setLIntegral_gaussTransferENN_iterate hf m hs).symm

/-- Nonnegative correlation identity in `ℝ≥0∞` form. -/
theorem lintegral_ofReal_mul_comp_gaussOrbit_eq_transferENN
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (m : ℕ) :
    (∫⁻ x, ENNReal.ofReal (f x) *
        ENNReal.ofReal (g (gaussOrbit m x)) ∂gaussMeasure) =
      ∫⁻ y, (gaussTransferENN^[m]) (fun x => ENNReal.ofReal (f x)) y *
        ENNReal.ofReal (g y) ∂gaussMeasure := by
  let ν : Measure ℝ :=
    gaussMeasure.withDensity (fun x => ENNReal.ofReal (f x))
  have hfE : Measurable (fun x : ℝ => ENNReal.ofReal (f x)) :=
    hf.ennreal_ofReal
  have hgE : Measurable (fun x : ℝ => ENNReal.ofReal (g x)) :=
    hg.ennreal_ofReal
  calc
    (∫⁻ x, ENNReal.ofReal (f x) *
        ENNReal.ofReal (g (gaussOrbit m x)) ∂gaussMeasure) =
        ∫⁻ x, ENNReal.ofReal (g (gaussOrbit m x)) ∂ν := by
      unfold ν
      simpa only [Pi.mul_apply] using!
        (lintegral_withDensity_eq_lintegral_mul gaussMeasure hfE
          (hgE.comp (measurable_gaussOrbit m))).symm
    _ = ∫⁻ y, ENNReal.ofReal (g y) ∂Measure.map (gaussOrbit m) ν := by
      exact (lintegral_map hgE (measurable_gaussOrbit m)).symm
    _ = ∫⁻ y, ENNReal.ofReal (g y) ∂gaussMeasure.withDensity
          ((gaussTransferENN^[m]) (fun x => ENNReal.ofReal (f x))) := by
      rw [show Measure.map (gaussOrbit m) ν =
          gaussMeasure.withDensity
            ((gaussTransferENN^[m]) (fun x => ENNReal.ofReal (f x))) by
        unfold ν
        exact map_gaussOrbit_withDensity_eq_gaussTransferENN_iterate hfE m]
    _ = ∫⁻ y, (gaussTransferENN^[m]) (fun x => ENNReal.ofReal (f x)) y *
          ENNReal.ofReal (g y) ∂gaussMeasure := by
      rw [lintegral_withDensity_eq_lintegral_mul gaussMeasure
        (measurable_gaussTransferENN_iterate hfE m) hgE]
      rfl

/-- Real-valued Perron--Frobenius adjoint identity.  The initial observable
is nonnegative and bounded on the Gauss state interval; the second observable
may have either sign.  No integrability premise is hidden: the Bochner map
and density identities are valid for measurable functions, and boundedness
of the first observable supplies finiteness of the transferred density. -/
theorem integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate
    {A : ℝ} {f g : ℝ → ℝ}
    (hfM : Measurable f) (hgM : Measurable g)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (m : ℕ) :
    (∫ x, f x * g (gaussOrbit m x) ∂gaussMeasure) =
      ∫ y, ((gaussTransfer^[m]) f y) * g y ∂gaussMeasure := by
  let fE : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  let ν : Measure ℝ := gaussMeasure.withDensity fE
  let hE : ℝ → ℝ≥0∞ := (gaussTransferENN^[m]) fE
  have hfEM : Measurable fE := hfM.ennreal_ofReal
  have hhEM : Measurable hE :=
    measurable_gaussTransferENN_iterate hfEM m
  have hfEtop : ∀ᵐ x ∂gaussMeasure, fE x < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hhEtop : ∀ᵐ y ∂gaussMeasure, hE y < ∞ := by
    filter_upwards [gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    dsimp only [hE, fE]
    rw [← ofReal_gaussTransfer_iterate_eq_gaussTransferENN_iterate
      hf0 hfA m hycc]
    exact ENNReal.ofReal_lt_top
  calc
    (∫ x, f x * g (gaussOrbit m x) ∂gaussMeasure) =
        ∫ x, g (gaussOrbit m x) ∂ν := by
      unfold ν
      rw [integral_withDensity_eq_integral_toReal_smul
        hfEM hfEtop]
      apply integral_congr_ae
      filter_upwards [gaussMeasure_unit_ae] with x hx
      have hxcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      dsimp only [fE]
      rw [ENNReal.toReal_ofReal (hf0 hxcc)]
      simp only [smul_eq_mul]
    _ = ∫ y, g y ∂Measure.map (gaussOrbit m) ν := by
      exact (integral_map (measurable_gaussOrbit m).aemeasurable
        hgM.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂gaussMeasure.withDensity hE := by
      rw [show Measure.map (gaussOrbit m) ν =
          gaussMeasure.withDensity hE by
        unfold ν hE fE
        exact map_gaussOrbit_withDensity_eq_gaussTransferENN_iterate
          hfM.ennreal_ofReal m]
    _ = ∫ y, (hE y).toReal * g y ∂gaussMeasure := by
      rw [integral_withDensity_eq_integral_toReal_smul hhEM hhEtop]
      simp only [smul_eq_mul]
    _ = ∫ y, ((gaussTransfer^[m]) f y) * g y ∂gaussMeasure := by
      apply integral_congr_ae
      filter_upwards [gaussMeasure_unit_ae] with y hy
      have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
      dsimp only [hE, fE]
      rw [← ofReal_gaussTransfer_iterate_eq_gaussTransferENN_iterate
        hf0 hfA m hycc,
        ENNReal.toReal_ofReal
          ((gaussTransfer_iterate_unit_bounds hf0 hfA m).1 hycc)]

/-- A bounded nonnegative observable remains genuinely integrable after
every real Gauss-transfer iterate.  Measurability is obtained from the
already measurable `ℝ≥0∞` transfer density, rather than assumed for a
pointwise infinite real series. -/
theorem integrable_gaussTransfer_iterate_of_unit_bounds
    {A : ℝ} {f : ℝ → ℝ} (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (m : ℕ) :
    Integrable ((gaussTransfer^[m]) f) gaussMeasure := by
  let fE : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  let hE : ℝ → ℝ≥0∞ := (gaussTransferENN^[m]) fE
  have hfEM : Measurable fE := hfM.ennreal_ofReal
  have hhEM : Measurable hE :=
    measurable_gaussTransferENN_iterate hfEM m
  have hbounds := gaussTransfer_iterate_unit_bounds hf0 hfA m
  have hae : (fun y => (hE y).toReal) =ᵐ[gaussMeasure]
      ((gaussTransfer^[m]) f) := by
    filter_upwards [gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    dsimp only [hE, fE]
    rw [← ofReal_gaussTransfer_iterate_eq_gaussTransferENN_iterate
      hf0 hfA m hycc,
      ENNReal.toReal_ofReal (hbounds.1 hycc)]
  have hEint : Integrable (fun y => (hE y).toReal) gaussMeasure := by
    apply Integrable.of_bound hhEM.ennreal_toReal.aestronglyMeasurable |A|
    filter_upwards [gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    dsimp only [hE, fE]
    rw [← ofReal_gaussTransfer_iterate_eq_gaussTransferENN_iterate
      hf0 hfA m hycc,
      ENNReal.toReal_ofReal (hbounds.1 hycc),
      Real.norm_eq_abs, abs_of_nonneg (hbounds.1 hycc)]
    exact (hbounds.2 hycc).trans (le_abs_self A)
  exact hEint.congr hae

/-- A function with oscillation at most `epsilon` on the unit interval is
within `epsilon` of its Gauss mean at every point of that interval. -/
theorem abs_sub_integral_gaussMeasure_le_of_unit_lipschitz
    {epsilon : ℝ} {h : ℝ → ℝ} (hepsilon : 0 ≤ epsilon)
    (hint : Integrable h gaussMeasure)
    (hlip : GaussUnitLipschitzBound epsilon h)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |h y - ∫ z, h z ∂gaussMeasure| ≤ epsilon := by
  have hpoint : ∀ᵐ z ∂gaussMeasure,
      h y - epsilon ≤ h z ∧ h z ≤ h y + epsilon := by
    filter_upwards [gaussMeasure_unit_ae] with z hz
    have hzcc : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2⟩
    have hdist : |y - z| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2, hzcc.1, hzcc.2]
    have hosc := hlip hy hzcc
    have hmul : epsilon * |y - z| ≤ epsilon := by
      simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left hdist hepsilon
    rw [abs_le] at hosc
    constructor <;> linarith
  have hlower : h y - epsilon ≤ ∫ z, h z ∂gaussMeasure := by
    calc
      h y - epsilon = ∫ _z, h y - epsilon ∂gaussMeasure := by simp
      _ ≤ ∫ z, h z ∂gaussMeasure := by
        exact integral_mono_ae (integrable_const _) hint (hpoint.mono fun _ hz => hz.1)
  have hupper : (∫ z, h z ∂gaussMeasure) ≤ h y + epsilon := by
    calc
      (∫ z, h z ∂gaussMeasure) ≤ ∫ _z, h y + epsilon ∂gaussMeasure := by
        exact integral_mono_ae hint (integrable_const _) (hpoint.mono fun _ hz => hz.2)
      _ = h y + epsilon := by simp
  rw [abs_le]
  constructor <;> linarith

/-- Iterated transfer of a bounded nonnegative Lipschitz observable converges
uniformly on the Gauss state interval to its exact Gauss mean, at the
explicit contraction rate. -/
theorem abs_gaussTransfer_iterate_sub_integral_le
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hfLip : GaussUnitLipschitzBound K f)
    (m : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |(gaussTransfer^[m]) f y - ∫ x, f x ∂gaussMeasure| ≤
      (527 / 540 : ℝ) ^ m * K := by
  have hInt := integrable_gaussTransfer_iterate_of_unit_bounds
    hfM hf0 hfA m
  have hLip := gaussTransfer_iterate_lipschitz hK hf0 hfA hfLip m
  have hmean :
      (∫ y, (gaussTransfer^[m]) f y ∂gaussMeasure) =
        ∫ x, f x ∂gaussMeasure := by
    have hcorr := integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate
      hfM measurable_const hf0 hfA m (g := fun _ => (1 : ℝ))
    simpa only [mul_one] using! hcorr.symm
  rw [← hmean]
  exact abs_sub_integral_gaussMeasure_le_of_unit_lipschitz
    (mul_nonneg (by positivity) hK) hInt hLip hy

/-- Exponential covariance decay for a bounded nonnegative Lipschitz
observable under the actual Gauss dynamics. -/
theorem abs_integral_mul_gaussOrbit_sub_sq_integral_le
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hfLip : GaussUnitLipschitzBound K f)
    (m : ℕ) :
    |(∫ x, f x * f (gaussOrbit m x) ∂gaussMeasure) -
        (∫ x, f x ∂gaussMeasure) ^ 2| ≤
      (527 / 540 : ℝ) ^ m * K * A := by
  let Pm : ℝ → ℝ := (gaussTransfer^[m]) f
  let mean : ℝ := ∫ x, f x ∂gaussMeasure
  have hfInt : Integrable f gaussMeasure := by
    apply Integrable.of_bound hfM.aestronglyMeasurable A
    filter_upwards [gaussMeasure_unit_ae] with x hx
    have hxcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 hxcc)]
    exact hfA hxcc
  have hPmInt : Integrable Pm gaussMeasure := by
    exact integrable_gaussTransfer_iterate_of_unit_bounds hfM hf0 hfA m
  have hprodInt : Integrable (fun y => Pm y * f y) gaussMeasure := by
    have h := hPmInt.bdd_mul hfM.aestronglyMeasurable
      (c := A) (by
        filter_upwards [gaussMeasure_unit_ae] with y hy
        have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 hycc)]
        exact hfA hycc)
    simpa only [mul_comm] using! h
  have hmeanProdInt : Integrable (fun y => mean * f y) gaussMeasure :=
    hfInt.const_mul mean
  have hcorr :
      (∫ x, f x * f (gaussOrbit m x) ∂gaussMeasure) =
        ∫ y, Pm y * f y ∂gaussMeasure := by
    exact integral_mul_comp_gaussOrbit_eq_gaussTransfer_iterate
      hfM hfM hf0 hfA m
  have hrearrange :
      (∫ x, f x * f (gaussOrbit m x) ∂gaussMeasure) -
          (∫ x, f x ∂gaussMeasure) ^ 2 =
        ∫ y, (Pm y - mean) * f y ∂gaussMeasure := by
    rw [hcorr]
    calc
      (∫ y, Pm y * f y ∂gaussMeasure) - mean ^ 2 =
          (∫ y, Pm y * f y ∂gaussMeasure) -
            ∫ y, mean * f y ∂gaussMeasure := by
        rw [integral_const_mul]
        dsimp only [mean]
        ring
      _ = ∫ y, (Pm y * f y - mean * f y) ∂gaussMeasure := by
        rw [integral_sub hprodInt hmeanProdInt]
      _ = ∫ y, (Pm y - mean) * f y ∂gaussMeasure := by
        apply integral_congr_ae
        filter_upwards with y
        ring
  rw [hrearrange]
  rw [show |∫ y, (Pm y - mean) * f y ∂gaussMeasure| =
      ‖∫ y, (Pm y - mean) * f y ∂gaussMeasure‖ by
    exact (Real.norm_eq_abs _).symm]
  have hbound : ∀ᵐ y ∂gaussMeasure,
      ‖(Pm y - mean) * f y‖ ≤
        (527 / 540 : ℝ) ^ m * K * A := by
    filter_upwards [gaussMeasure_unit_ae] with y hy
    have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2⟩
    have hclose := abs_gaussTransfer_iterate_sub_integral_le
      hK hfM hf0 hfA hfLip m hycc
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hf0 hycc)]
    exact mul_le_mul hclose (hfA hycc) (hf0 hycc)
      (mul_nonneg (by positivity : 0 ≤ (527 / 540 : ℝ) ^ m) hK)
  simpa using! norm_integral_le_of_norm_le_const hbound

/-- Gauss invariance for the integral of an arbitrary measurable real
observable, at every finite time. -/
theorem integral_comp_gaussOrbit (h : ℝ → ℝ) (hh : Measurable h)
    (i : ℕ) :
    (∫ x, h (gaussOrbit i x) ∂gaussMeasure) =
      ∫ x, h x ∂gaussMeasure := by
  have hmap := integral_map (μ := gaussMeasure)
    (measurable_gaussOrbit i).aemeasurable hh.aestronglyMeasurable
  have hmeasure : Measure.map (gaussOrbit i) gaussMeasure = gaussMeasure := by
    simpa only [gaussOrbit] using! map_gaussMap_iterate_gaussMeasure i
  rw [hmeasure] at hmap
  exact hmap.symm

/-- Stationarity reduces a two-time product to the actual nonnegative lag. -/
theorem integral_mul_two_gaussOrbits_eq_lag
    {f : ℝ → ℝ} (hfM : Measurable f)
    {i j : ℕ} (hij : i ≤ j) :
    (∫ x, f (gaussOrbit i x) * f (gaussOrbit j x) ∂gaussMeasure) =
      ∫ x, f x * f (gaussOrbit (j - i) x) ∂gaussMeasure := by
  let h : ℝ → ℝ := fun z => f z * f (gaussOrbit (j - i) z)
  have hhM : Measurable h :=
    hfM.mul (hfM.comp (measurable_gaussOrbit (j - i)))
  have hstat := integral_comp_gaussOrbit h hhM i
  calc
    (∫ x, f (gaussOrbit i x) * f (gaussOrbit j x) ∂gaussMeasure) =
        ∫ x, h (gaussOrbit i x) ∂gaussMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [h]
      rw [← gaussOrbit_add_apply_right i (j - i) x,
        Nat.add_sub_of_le hij]
    _ = ∫ x, h x ∂gaussMeasure := hstat
    _ = ∫ x, f x * f (gaussOrbit (j - i) x) ∂gaussMeasure := rfl

/-- Exponential covariance decay at two arbitrary ordered Gauss times. -/
theorem abs_integral_mul_two_gaussOrbits_sub_sq_integral_le
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hfLip : GaussUnitLipschitzBound K f)
    {i j : ℕ} (hij : i ≤ j) :
    |(∫ x, f (gaussOrbit i x) * f (gaussOrbit j x) ∂gaussMeasure) -
        (∫ x, f x ∂gaussMeasure) ^ 2| ≤
      (527 / 540 : ℝ) ^ (j - i) * K * A := by
  rw [integral_mul_two_gaussOrbits_eq_lag hfM hij]
  exact abs_integral_mul_gaussOrbit_sub_sq_integral_le
    hK hfM hf0 hfA hfLip (j - i)

end

end Erdos1002
