import ErdosProblems.Erdos4.NormalizationAsymptotic

/-!
# Prime averages of the actual supported affine weights

The Fourier estimate is transferred to the real arithmetic weights at
positive centers. Its main term is stated using the genuine principal
deletion form, so the principal-gain theorem can be used directly.
-/

open scoped BigOperators

namespace Erdos4.AffineSourceAverage

open DivisorCoefficients RestrictedProductNorm

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def principalForm (m : ℝ) (R : ℕ) (j : Fin k) : ℝ :=
  restrictedForm (fun l => (ell l : ℝ))
    (fun s => ∏ l, LocalCharacterMatrix.deletionMask j (s l))
    (coefficient m R ell) (coefficient m R ell)

noncomputable def principalMean (m : ℝ) (R : ℕ) (j : Fin k) : ℝ :=
  principalForm ell m R j / UnitFourier.unitDensity ell

theorem principalMean_cast (m : ℝ) (R : ℕ) (h : Fin k → ℕ)
    (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l)))) (j : Fin k) :
    (principalMean ell m R j : ℂ) =
      UnitFourier.coefficient ell m R (fun l i => (h i : ZMod (ell l))) j (fun _ => 1) := by
  rw [UnitFourier.principal_coefficient_eq_restrictedForm ell m R _ hh]
  exact Complex.ofReal_div _ _

noncomputable def rawAverage (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (j : Fin k) (q : ℕ) : ℝ :=
  ∑ p : sources, AffineWeights.weight ell m R Y W h p (q - h j * p)

noncomputable def discrepancy (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (j : Fin k) (q : ℕ) : ℝ :=
  rawAverage ell m R Y W h sources j q - sources.card * principalMean ell m R j

theorem discrepancy_cast (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (sources : Finset ℕ) (hs : ∀ p ∈ sources, p.Coprime (ProductCharacterEncoding.modulus ell))
    (j : Fin k) (q : ℕ) (hq : q.Coprime (ProductCharacterEncoding.modulus ell))
    (hshift : ∀ p ∈ sources, h j * p ≤ q)
    (hcenter : ∀ p ∈ sources, q - h j * p ∈ Finset.Icc 1 Y)
    (hcenterW : ∀ p ∈ sources, (q - h j * p).Coprime W) :
    (discrepancy ell m R Y W h sources j q : ℂ) =
      (∑ p : sources, (AnchoredFourierAverage.realSquare ell m R
        (fun l i => (h i : ZMod (ell l))) j
        (AnchoredFourierAverage.unitPoint ell p (hs p p.property) /
          AnchoredFourierAverage.unitPoint ell q hq) : ℂ)) -
        (sources.card : ℂ) * UnitFourier.coefficient ell m R
          (fun l i => (h i : ZMod (ell l))) j (fun _ => 1) := by
  unfold discrepancy rawAverage
  rw [Complex.ofReal_sub, Complex.ofReal_mul, principalMean_cast ell m R h hh,
    Complex.ofReal_natCast, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _hp
  exact congrArg Complex.ofReal (AffineWeights.weight_anchor ell m R Y W h hh j p q
    (hs p p.property) hq (hshift p p.property) (hcenter p p.property) (hcenterW p p.property))

/-- Double prime averaging for the real, supported arithmetic weights. -/
theorem discrepancy_mean_square {t R : ℕ} {m : ℝ} (hm : 1 ≤ m)
    (ht : 2 ≤ t) (hR : 2 ≤ R)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective ell) (hRQ : R ^ 2 ≤ t ^ 10) (hell : ∀ l, k + 2 ≤ ell l)
    (h : Fin k → ℕ) (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (j : Fin k) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hlocal : ∀ l, 20 * (k : ℝ) ^ 3 ≤ δ * ell l)
    (X Y W : ℕ) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (ProductCharacterEncoding.modulus ell))
    (htcop : ∀ n ∈ targets, n.Coprime (ProductCharacterEncoding.modulus ell))
    (hshift : ∀ q ∈ targets, ∀ p ∈ sources, h j * p ≤ q)
    (hcenter : ∀ q ∈ targets, ∀ p ∈ sources, q - h j * p ∈ Finset.Icc 1 Y)
    (hcenterW : ∀ q ∈ targets, ∀ p ∈ sources, (q - h j * p).Coprime W) :
    (∑ q : targets, discrepancy ell m R Y W h sources j q ^ 2) ≤
      (2 * (Y : ℝ) / Real.log t) *
        ((energy (coefficient (k := k) m R ell) / UnitFourier.unitDensity ell) * δ) ^ 2 *
        ((2 * (X : ℝ) / Real.log t) * sources.card) := by
  have hms := AnchoredFourierAverage.source_average_mean_square ell hm ht hR hH hinj hRQ hell
    (fun l i => (h i : ZMod (ell l))) hh j hδ0 hδ1 hlocal X Y hX hY sources targets
    hsources htargets hscop htcop
  have heq (q : targets) :
      ‖(∑ p : sources, (AnchoredFourierAverage.realSquare ell m R
        (fun l i => (h i : ZMod (ell l))) j
        (AnchoredFourierAverage.unitPoint ell p (hscop p p.property) /
          AnchoredFourierAverage.unitPoint ell q (htcop q q.property)) : ℂ)) -
        (sources.card : ℂ) * UnitFourier.coefficient ell m R
          (fun l i => (h i : ZMod (ell l))) j (fun _ => 1)‖ ^ 2 =
        discrepancy ell m R Y W h sources j q ^ 2 := by
    rw [← discrepancy_cast ell m R Y W h hh sources hscop j q (htcop q q.property)
      (hshift q q.property) (hcenter q q.property) (hcenterW q q.property)]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [heq] using hms

theorem rawAverage_lower_of_error (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (sources : Finset ℕ) (j : Fin k) (q : ℕ) {E : ℝ}
    (herr : |discrepancy ell m R Y W h sources j q| ≤ E) :
    sources.card * principalMean ell m R j - E ≤ rawAverage ell m R Y W h sources j q := by
  have hh := (abs_le.mp herr).1
  unfold discrepancy at hh
  linarith

end Erdos4.AffineSourceAverage
