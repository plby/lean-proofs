import ErdosProblems.Erdos4.CompleteCover

/-!
# Actual prime exposure outside an explicit exceptional set

The real affine-weight mean-square theorem is combined with the true
principal gain and the actual probability normalization. The coefficient
energy and the weight-window density cancel from the exceptional-set
bound. No unproved prime-average estimate is assumed.
-/

open scoped BigOperators

namespace Erdos4.PrimeExposure

open AffineSourceAverage AffineNormalization DivisorCoefficients RestrictedProductNorm ExposureBounds

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem exists_exceptional_targets {t R : ℕ} {m : ℝ} (hm : 1 ≤ m)
    (ht : 2 ≤ t) (hR : 2 ≤ R)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10) (hell : ∀ l, k + 2 ≤ ell l)
    (h : Fin k → ℕ) (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlocal : ∀ l, 20 * (k : ℝ) ^ 3 ≤ δ * ell l)
    (X Y W : ℕ) (hW : 0 < W) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ) (hsourceCount : 0 < sources.card)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (ProductCharacterEncoding.modulus ell))
    (htcop : ∀ n ∈ targets, n.Coprime (ProductCharacterEncoding.modulus ell))
    (hshift : ∀ j : Fin k, ∀ q ∈ targets, ∀ p ∈ sources, h j * p ≤ q)
    (hcenter : ∀ j : Fin k, ∀ q ∈ targets, ∀ p ∈ sources, q - h j * p ∈ Finset.Icc 1 Y)
    (hcenterW : ∀ j : Fin k, ∀ q ∈ targets, ∀ p ∈ sources, (q - h j * p).Coprime W)
    (hZ : ∀ p ∈ sources, 0 < normalizer ell m R Y W h p ∧
      normalizer ell m R Y W h p ≤
        2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y * energy (coefficient (k := k) m R ell))
    (A : ℝ) (hgain : (A + 1) * energy (coefficient (k := k) m R ell) ≤
      ∑ j : Fin k, principalForm ell m R j) :
    ∃ bad : Finset ℕ, bad ⊆ targets ∧
      (bad.card : ℝ) ≤ 4 * (k : ℝ) ^ 2 * δ ^ 2 * X * Y /
        (Real.log t ^ 2 * sources.card) ∧
      ∀ q ∈ targets, q ∉ bad →
        A * sources.card / (2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Y *
          UnitFourier.unitDensity ell) ≤ exposure ell m R Y W h sources q := by
  classical
  let N := energy (coefficient (k := k) m R ell)
  let V := UnitFourier.unitDensity ell
  let θ := (sources.card : ℝ) * N / V
  let B := (2 * (Y : ℝ) / Real.log t) * ((N / V) * δ) ^ 2 *
    ((2 * (X : ℝ) / Real.log t) * sources.card)
  have hN : 0 < N := zero_lt_one.trans_le (one_le_coefficient_energy m (by omega : 1 ≤ R) ell)
  have hV : 0 < V := UnitFourier.unitDensity_pos ell
  have hS : (0 : ℝ) < sources.card := by exact_mod_cast hsourceCount
  have hθ : 0 < θ := div_pos (mul_pos hS hN) hV
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht)
  have hms : ∀ j : Fin k, (∑ q : targets, discrepancy ell m R Y W h sources j q ^ 2) ≤ B := by
    intro j
    exact discrepancy_mean_square ell hm ht hR hH hinj hRQ hell h hh j hδ0 hδ1 hlocal
      X Y W hX hY sources targets hsources htargets hscop htcop
      (hshift j) (hcenter j) (hcenterW j)
  let bad := badTargets ell m R Y W h sources targets θ
  refine ⟨bad, Finset.filter_subset _ _, ?_, ?_⟩
  · have hb := badTargets_card_le ell m R Y W h sources targets hθ hms
    have heq : (k : ℝ) ^ 2 * B / θ ^ 2 =
        4 * (k : ℝ) ^ 2 * δ ^ 2 * X * Y / (Real.log t ^ 2 * sources.card) := by
      dsimp [B, θ]
      field_simp
      <;> ring
    exact hb.trans_eq heq
  · intro q hq hgood
    have hYpos : 0 < Y := (pow_pos (by omega : 0 < t) 50).trans_le hY
    exact exposure_lower ell m hW hYpos (by omega : 1 ≤ R) h sources q A hgain
      (not_bad_error_le ell m R Y W h sources targets θ q hq hgood)
      (fun p hp => (hZ p hp).1) (fun p hp => (hZ p hp).2)

end Erdos4.PrimeExposure
