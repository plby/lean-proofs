import ErdosProblems.Erdos4.AffineSourceAverage

/-!
# Total exposure and exceptional targets

Summing the anchor discrepancies costs only the square of the fixed
dimension in mean square. Outside the resulting exceptional set, the
principal gain gives a lower bound for the total normalized exposure.
-/

open scoped BigOperators

namespace Erdos4.ExposureBounds

open AffineSourceAverage DivisorCoefficients RestrictedProductNorm

section FiniteEstimates

variable {I Q : Type*} [Fintype I] [Fintype Q]

theorem sum_errors_mean_square (f : I → Q → ℝ) {B : ℝ}
    (hf : ∀ i, (∑ q, f i q ^ 2) ≤ B) :
    (∑ q, (∑ i, f i q) ^ 2) ≤ (Fintype.card I : ℝ) ^ 2 * B := by
  calc
    _ ≤ ∑ q, (Fintype.card I : ℝ) * ∑ i, f i q ^ 2 :=
      Finset.sum_le_sum (fun q _hq => GramBound.sum_sq_le_card_mul_sum_sq (fun i => f i q))
    _ = (Fintype.card I : ℝ) * ∑ i, ∑ q, f i q ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Fintype.card I : ℝ) * ∑ _i : I, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _hi => hf i)) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two, mul_assoc]

theorem large_values_card_le {T : Type*} [DecidableEq T] (s : Finset T)
    (f : T → ℝ) {θ B : ℝ} (hθ : 0 < θ) (hf : (∑ q ∈ s, f q ^ 2) ≤ B) :
    ((s.filter (fun q => θ < |f q|)).card : ℝ) ≤ B / θ ^ 2 := by
  classical
  let bad := s.filter (fun q => θ < |f q|)
  have hb : (bad.card : ℝ) * θ ^ 2 ≤ ∑ q ∈ bad, f q ^ 2 := by
    calc
      _ = ∑ _q ∈ bad, θ ^ 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        have hqθ : θ < |f q| := (Finset.mem_filter.mp hq).2
        have hsq := (sq_le_sq₀ hθ.le (abs_nonneg (f q))).mpr hqθ.le
        simpa only [sq_abs] using hsq
  have htotal : (∑ q ∈ bad, f q ^ 2) ≤ ∑ q ∈ s, f q ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _hq _hnot => sq_nonneg _)
  exact (le_div_iff₀ (sq_pos_of_pos hθ)).mpr (hb.trans (htotal.trans hf))

end FiniteEstimates

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def totalError (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ j : Fin k, discrepancy ell m R Y W h sources j q

theorem totalError_eq (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (q : ℕ) :
    totalError ell m R Y W h sources q =
      (∑ j : Fin k, rawAverage ell m R Y W h sources j q) -
        sources.card * (∑ j : Fin k, principalForm ell m R j) / UnitFourier.unitDensity ell := by
  simp only [totalError, discrepancy, Finset.sum_sub_distrib, principalMean,
    mul_div_assoc, ← Finset.sum_div, ← Finset.mul_sum]

theorem totalError_mean_square (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources targets : Finset ℕ) {B : ℝ}
    (hf : ∀ j : Fin k, (∑ q : targets, discrepancy ell m R Y W h sources j q ^ 2) ≤ B) :
    (∑ q ∈ targets, totalError ell m R Y W h sources q ^ 2) ≤ (k : ℝ) ^ 2 * B := by
  have hh := sum_errors_mean_square (fun (j : Fin k) (q : targets) =>
    discrepancy ell m R Y W h sources j q) hf
  rw [← Finset.sum_coe_sort targets (fun q : ℕ => totalError ell m R Y W h sources q ^ 2)]
  simpa only [Fintype.card_fin, totalError] using hh

noncomputable def badTargets (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources targets : Finset ℕ) (θ : ℝ) : Finset ℕ :=
  targets.filter (fun q => θ < |totalError ell m R Y W h sources q|)

theorem badTargets_card_le (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources targets : Finset ℕ) {θ B : ℝ} (hθ : 0 < θ)
    (hf : ∀ j : Fin k, (∑ q : targets, discrepancy ell m R Y W h sources j q ^ 2) ≤ B) :
    ((badTargets ell m R Y W h sources targets θ).card : ℝ) ≤ (k : ℝ) ^ 2 * B / θ ^ 2 :=
  large_values_card_le targets _ hθ (totalError_mean_square ell m R Y W h sources targets hf)

theorem not_bad_error_le (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources targets : Finset ℕ) (θ : ℝ) (q : ℕ) (hq : q ∈ targets)
    (hgood : q ∉ badTargets ell m R Y W h sources targets θ) :
    |totalError ell m R Y W h sources q| ≤ θ := by
  exact le_of_not_gt (fun hh => hgood (Finset.mem_filter.mpr ⟨hq, hh⟩))

theorem raw_total_lower (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (q : ℕ) (A : ℝ)
    (hgain : (A + 1) * energy (coefficient (k := k) m R ell) ≤
      ∑ j : Fin k, principalForm ell m R j)
    (herr : |totalError ell m R Y W h sources q| ≤
      sources.card * energy (coefficient (k := k) m R ell) / UnitFourier.unitDensity ell) :
    A * sources.card * energy (coefficient (k := k) m R ell) / UnitFourier.unitDensity ell ≤
      ∑ j : Fin k, rawAverage ell m R Y W h sources j q := by
  have hV := UnitFourier.unitDensity_pos ell
  have hmain := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgain (Nat.cast_nonneg sources.card)) hV.le
  have he := (abs_le.mp herr).1
  rw [totalError_eq] at he
  have hsplit : (sources.card : ℝ) * ((A + 1) * energy (coefficient (k := k) m R ell)) /
      UnitFourier.unitDensity ell =
      A * sources.card * energy (coefficient (k := k) m R ell) / UnitFourier.unitDensity ell +
        sources.card * energy (coefficient (k := k) m R ell) / UnitFourier.unitDensity ell := by ring
  rw [hsplit] at hmain
  linarith

noncomputable def exposure (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ p : sources, ∑ j : Fin k, WindowNormalization.probability ell m R Y W h p (q - h j * p)

theorem exposure_nonneg (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (q : ℕ) : 0 ≤ exposure ell m R Y W h sources q :=
  Finset.sum_nonneg (fun p _hp => Finset.sum_nonneg (fun j _hj =>
    WindowNormalization.probability_nonneg ell m R Y W h p (q - h j * p)))

theorem raw_div_le_exposure (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (q : ℕ) {U : ℝ}
    (hZ : ∀ p ∈ sources, 0 < AffineNormalization.normalizer ell m R Y W h p)
    (hZU : ∀ p ∈ sources, AffineNormalization.normalizer ell m R Y W h p ≤ U) :
    (∑ j : Fin k, rawAverage ell m R Y W h sources j q) / U ≤
      exposure ell m R Y W h sources q := by
  unfold rawAverage exposure
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p _hp
  apply Finset.sum_le_sum
  intro j _hj
  exact div_le_div_of_nonneg_left (AffineWeights.weight_nonneg ell m R Y W h p (q - h j * p))
    (hZ p p.property) (hZU p p.property)

theorem exposure_lower (m : ℝ) {R Y W : ℕ} (hW : 0 < W) (hY : 0 < Y) (hR : 1 ≤ R)
    (h : Fin k → ℕ) (sources : Finset ℕ) (q : ℕ) (A : ℝ)
    (hgain : (A + 1) * energy (coefficient (k := k) m R ell) ≤
      ∑ j : Fin k, principalForm ell m R j)
    (herr : |totalError ell m R Y W h sources q| ≤
      sources.card * energy (coefficient (k := k) m R ell) / UnitFourier.unitDensity ell)
    (hZ : ∀ p ∈ sources, 0 < AffineNormalization.normalizer ell m R Y W h p)
    (hZU : ∀ p ∈ sources, AffineNormalization.normalizer ell m R Y W h p ≤
      2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
        energy (coefficient (k := k) m R ell)) :
    A * sources.card / (2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
      UnitFourier.unitDensity ell) ≤ exposure ell m R Y W h sources q := by
  have hρ := FiberAsymptotic.density_pos hW
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hN : 0 < energy (coefficient (k := k) m R ell) :=
    zero_lt_one.trans_le (one_le_coefficient_energy m hR ell)
  have hV := UnitFourier.unitDensity_pos ell
  have hU : 0 < 2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
      energy (coefficient (k := k) m R ell) := by positivity
  calc
    _ = (A * sources.card * energy (coefficient (k := k) m R ell) / UnitFourier.unitDensity ell) /
        (2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
          energy (coefficient (k := k) m R ell)) := by field_simp
    _ ≤ (∑ j : Fin k, rawAverage ell m R Y W h sources j q) /
        (2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
          energy (coefficient (k := k) m R ell)) :=
      div_le_div_of_nonneg_right (raw_total_lower ell m R Y W h sources q A hgain herr) hU.le
    _ ≤ _ := raw_div_le_exposure ell m R Y W h sources q hZ hZU

end Erdos4.ExposureBounds
