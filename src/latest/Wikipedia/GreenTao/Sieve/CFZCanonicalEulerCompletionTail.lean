import Wikipedia.GreenTao.Sieve.CFZCanonicalEulerCompletion
import Wikipedia.GreenTao.Sieve.CFZCarryFourierTailPolylog

/-!
# Polylogarithmic control of the canonical Euler-completion tail

The complete-support majorant has local factor

`1 + 3m p^(-1-1/log R) + 4^m p^(-2)`,

where `m` is the number of selected CFZ forms.  We compare its two
nonconstant pieces with the Euler products for
`ζ(1 + 1 / log R)` and `ζ(2)`.  The elementary bound
`‖ζ(1 + 1 / log R)‖ ≤ 1 + log R` then gives an explicit
polylogarithmic bound for the whole infinite support mass, and hence for
the genuinely missing completion tail.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## A two-factor Euler comparison -/

/-- A local two-variable Bernoulli estimate, in the form used to compare
the completion majorant with two zeta Euler factors. -/
theorem one_add_nat_mul_add_nat_mul_le_inv_one_sub_pow_mul
    (A B : ℕ) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    1 + (A : ℝ) * x + (B : ℝ) * y ≤
      (1 - x)⁻¹ ^ A * (1 - y)⁻¹ ^ B := by
  have hxden : 0 < 1 - x := sub_pos.mpr hx1
  have hyden : 0 < 1 - y := sub_pos.mpr hy1
  have hxbase : 1 + x ≤ (1 - x)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hxden]
    nlinarith [sq_nonneg x]
  have hybase : 1 + y ≤ (1 - y)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hyden]
    nlinarith [sq_nonneg y]
  have hxpow :
      1 + (A : ℝ) * x ≤ (1 - x)⁻¹ ^ A := by
    calc
      1 + (A : ℝ) * x ≤ (1 + x) ^ A :=
        one_add_mul_le_pow (by linarith) A
      _ ≤ (1 - x)⁻¹ ^ A :=
        pow_le_pow_left₀ (by positivity) hxbase A
  have hypow :
      1 + (B : ℝ) * y ≤ (1 - y)⁻¹ ^ B := by
    calc
      1 + (B : ℝ) * y ≤ (1 + y) ^ B :=
        one_add_mul_le_pow (by linarith) B
      _ ≤ (1 - y)⁻¹ ^ B :=
        pow_le_pow_left₀ (by positivity) hybase B
  calc
    1 + (A : ℝ) * x + (B : ℝ) * y ≤
        (1 + (A : ℝ) * x) * (1 + (B : ℝ) * y) := by
      nlinarith [mul_nonneg
        (mul_nonneg (Nat.cast_nonneg A) hx0)
        (mul_nonneg (Nat.cast_nonneg B) hy0)]
    _ ≤ (1 - x)⁻¹ ^ A * (1 - y)⁻¹ ^ B :=
      mul_le_mul hxpow hypow (by positivity) (by positivity)

/-- The local completion-majorant factor is bounded by the product of
the shifted and square zeta Euler factors. -/
theorem one_add_selectedCFZCanonicalCompletePrimeErrorMajorant_le_zetaFactors
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) (p : Nat.Primes) :
    1 + selectedCFZCanonicalCompletePrimeErrorMajorant e R p ≤
      ‖(1 - (p : ℂ) ^
          (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^
          (3 * Fintype.card (SelectedCFZFormIndex e)) *
        ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^
          (4 ^ Fintype.card (SelectedCFZFormIndex e)) := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  let x : ℝ :=
    (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹ - 1)
  let y : ℝ := (p : ℝ) ^ (-2 : ℝ)
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have hshift : 0 < 1 + (Real.log (R : ℝ))⁻¹ := by
    positivity
  have hpOne : (1 : ℝ) < p := by exact_mod_cast p.prop.two_le
  have hx0 : 0 ≤ x := by
    unfold x
    positivity
  have hx1 : x < 1 := by
    unfold x
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl
      ⟨hpOne, by
        have hinv : 0 < (Real.log (R : ℝ))⁻¹ := inv_pos.mpr hlog
        linarith⟩)
  have hy0 : 0 ≤ y := by
    unfold y
    positivity
  have hy1 : y < 1 := by
    unfold y
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl ⟨hpOne, by norm_num⟩)
  have hlocal :=
    one_add_nat_mul_add_nat_mul_le_inv_one_sub_pow_mul
      (3 * m) (4 ^ m) hx0 hx1 hy0 hy1
  have hxFactor :
      (1 - x)⁻¹ =
        ‖(1 - (p : ℂ) ^
          (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ := by
    rw [norm_primeEulerFactor_ofReal p.prop.two_le hshift]
    congr 2
    unfold x
    congr 1
    ring
  have hyFactor :
      (1 - y)⁻¹ =
        ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ := by
    rw [norm_primeEulerFactor_ofReal p.prop.two_le (by norm_num)]
  unfold selectedCFZCanonicalCompletePrimeErrorMajorant
  change
    1 + ((3 : ℝ) * (m : ℝ) * x +
      (4 : ℝ) ^ m / (p : ℝ) ^ 2) ≤ _
  have hyDiv :
      (4 : ℝ) ^ m / (p : ℝ) ^ 2 =
        ((4 ^ m : ℕ) : ℝ) * y := by
    unfold y
    rw [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv,
      Real.rpow_neg (by positivity), Real.rpow_two]
  rw [hxFactor, hyFactor] at hlocal
  calc
    1 + ((3 : ℝ) * (m : ℝ) * x +
        (4 : ℝ) ^ m / (p : ℝ) ^ 2) =
        1 + (((3 * m : ℕ) : ℝ) * x) +
          (((4 ^ m : ℕ) : ℝ) * y) := by
      rw [hyDiv]
      push_cast
      ring
    _ ≤ _ := by simpa [m] using hlocal

/-! ## The infinite support mass -/

/-- Polylogarithmic exponent supplied by the shifted zeta factor. -/
def selectedCFZCanonicalCompleteSupportPolylogExponent
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  3 * Fintype.card (SelectedCFZFormIndex e)

/-- Radius-independent cost of the absolutely convergent reciprocal-square
Euler factor. -/
noncomputable def selectedCFZCanonicalCompleteSupportPolylogConstant
    {k : ℕ} (e : LinearFormsExponent k) : ℝ :=
  (2 : ℝ) ^ (4 ^ Fintype.card (SelectedCFZFormIndex e))

theorem selectedCFZCanonicalCompleteSupportPolylogConstant_nonneg
    {k : ℕ} (e : LinearFormsExponent k) :
    0 ≤ selectedCFZCanonicalCompleteSupportPolylogConstant e := by
  unfold selectedCFZCanonicalCompleteSupportPolylogConstant
  positivity

/-- Explicit zeta-product bound for the full infinite completion-support
mass. -/
theorem selectedCFZCanonicalCompleteSupportMass_le_zetaProduct
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    selectedCFZCanonicalCompleteSupportMass e R ≤
      ‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^
          selectedCFZCanonicalCompleteSupportPolylogExponent e *
        ‖riemannZeta ((2 : ℝ) : ℂ)‖ ^
          (4 ^ Fintype.card (SelectedCFZFormIndex e)) := by
  let A := selectedCFZCanonicalCompleteSupportPolylogExponent e
  let B := 4 ^ Fintype.card (SelectedCFZFormIndex e)
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have hs :
      1 < ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)).re := by
    change (1 : ℝ) < 1 + (Real.log R)⁻¹
    have hinv : 0 < (Real.log R)⁻¹ := inv_pos.mpr hlog
    linarith
  have htwo : 1 < (((2 : ℝ) : ℂ)).re := by norm_num
  have hzetaShift :
      HasProd
        (fun p : Nat.Primes =>
          ‖(1 - (p : ℂ) ^
            (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ A)
        (‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ A) :=
    (riemannZeta_eulerProduct_hasProd hs).norm.pow A
  have hzetaTwo :
      HasProd
        (fun p : Nat.Primes =>
          ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^ B)
        (‖riemannZeta ((2 : ℝ) : ℂ)‖ ^ B) :=
    (riemannZeta_eulerProduct_hasProd htwo).norm.pow B
  have hright :=
    hzetaShift.mul hzetaTwo
  have hleft :
      HasProd
        (fun p : Nat.Primes =>
          1 + selectedCFZCanonicalCompletePrimeErrorMajorant e R p)
        (selectedCFZCanonicalCompleteSupportMass e R) := by
    rw [selectedCFZCanonicalCompleteSupportMass_eq_tprod e hR]
    exact
      (multipliable_one_add_of_summable_prod
        (summable_selectedCFZCanonicalCompleteSupportMajorant
          e hR)).hasProd
  have hcomparison :
      selectedCFZCanonicalCompleteSupportMass e R ≤
        ‖riemannZeta
            ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ A *
          ‖riemannZeta ((2 : ℝ) : ℂ)‖ ^ B := by
    apply hasProd_le_of_prod_le hleft
    intro s
    calc
      ∏ p ∈ s,
          (1 + selectedCFZCanonicalCompletePrimeErrorMajorant e R p) ≤
          ∏ p ∈ s,
            (‖(1 - (p : ℂ) ^
                (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ A *
              ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^ B) := by
        apply Finset.prod_le_prod
        · intro p _hp
          have hnonneg :=
            selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg e R p
          positivity
        · intro p _hp
          simpa [A, selectedCFZCanonicalCompleteSupportPolylogExponent, B]
            using
              one_add_selectedCFZCanonicalCompletePrimeErrorMajorant_le_zetaFactors
                e hR p
      _ ≤
          ‖riemannZeta
              ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ A *
            ‖riemannZeta ((2 : ℝ) : ℂ)‖ ^ B := by
        apply ge_of_tendsto hright
        filter_upwards [eventually_ge_atTop s] with t hst
        apply Finset.prod_le_prod_of_subset_of_one_le hst
        · intro p _hp
          positivity
        · intro p _hpt _hps
          have hshiftPos :
              0 < 1 + (Real.log (R : ℝ))⁻¹ := by positivity
          have honeShift :
              1 ≤
                ‖(1 - (p : ℂ) ^
                  (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ A :=
            one_le_pow₀
              (one_le_norm_primeEulerFactor_ofReal
                p.prop.two_le hshiftPos)
          have honeTwo :
              1 ≤
                ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^ B :=
            one_le_pow₀
              (one_le_norm_primeEulerFactor_ofReal
                p.prop.two_le (by norm_num))
          calc
            1 = 1 * 1 := by ring
            _ ≤
                ‖(1 - (p : ℂ) ^
                  (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ A *
                ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^ B :=
              mul_le_mul honeShift honeTwo (by positivity) (by positivity)
  simpa [A, B, selectedCFZCanonicalCompleteSupportPolylogExponent] using
    hcomparison

/-- Uniform polylogarithmic bound for the full infinite support mass. -/
theorem selectedCFZCanonicalCompleteSupportMass_le_polylog
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    selectedCFZCanonicalCompleteSupportMass e R ≤
      selectedCFZCanonicalCompleteSupportPolylogConstant e *
        (1 + Real.log R) ^
          selectedCFZCanonicalCompleteSupportPolylogExponent e := by
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have hs : (1 : ℝ) < 1 + (Real.log R)⁻¹ := by
    have hinv : 0 < (Real.log R)⁻¹ := inv_pos.mpr hlog
    linarith
  have hshift :
      ‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ≤
        1 + Real.log R := by
    calc
      ‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ≤
          1 + ((1 + (Real.log R)⁻¹) - 1)⁻¹ :=
        norm_riemannZeta_ofReal_le_one_add_inv_sub_one hs
      _ = 1 + Real.log R := by
        rw [add_sub_cancel_left, inv_inv]
  have htwo :
      ‖riemannZeta ((2 : ℝ) : ℂ)‖ ≤ 2 := by
    have h := norm_riemannZeta_ofReal_le_one_add_inv_sub_one
      (show (1 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hbase : 0 ≤ 1 + Real.log R := by positivity
  calc
    selectedCFZCanonicalCompleteSupportMass e R ≤
        ‖riemannZeta
            ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^
            selectedCFZCanonicalCompleteSupportPolylogExponent e *
          ‖riemannZeta ((2 : ℝ) : ℂ)‖ ^
            (4 ^ Fintype.card (SelectedCFZFormIndex e)) :=
      selectedCFZCanonicalCompleteSupportMass_le_zetaProduct e hR
    _ ≤
        (1 + Real.log R) ^
            selectedCFZCanonicalCompleteSupportPolylogExponent e *
          (2 : ℝ) ^ (4 ^ Fintype.card (SelectedCFZFormIndex e)) := by
      exact mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hshift _)
        (pow_le_pow_left₀ (norm_nonneg _) htwo _)
        (pow_nonneg (norm_nonneg _) _)
        (pow_nonneg hbase _)
    _ =
        selectedCFZCanonicalCompleteSupportPolylogConstant e *
          (1 + Real.log R) ^
            selectedCFZCanonicalCompleteSupportPolylogExponent e := by
      unfold selectedCFZCanonicalCompleteSupportPolylogConstant
      ring

/-- The same explicit polylogarithmic bound for the actual missing
completion-support mass. -/
theorem selectedCFZCanonicalEulerCompletionTailMajorantMass_le_polylog
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    selectedCFZCanonicalEulerCompletionTailMajorantMass e R ≤
      selectedCFZCanonicalCompleteSupportPolylogConstant e *
        (1 + Real.log R) ^
          selectedCFZCanonicalCompleteSupportPolylogExponent e :=
  (selectedCFZCanonicalEulerCompletionTailMajorantMass_le_complete
    e hR).trans
    (selectedCFZCanonicalCompleteSupportMass_le_polylog e hR)

/-- The formerly conditional completion-tail interface is discharged. -/
theorem hasSelectedCFZCanonicalEulerCompletionTailPolylogBound
    {k : ℕ} (e : LinearFormsExponent k) :
    HasSelectedCFZCanonicalEulerCompletionTailPolylogBound e := by
  refine
    ⟨selectedCFZCanonicalCompleteSupportPolylogExponent e,
      selectedCFZCanonicalCompleteSupportPolylogConstant e,
      selectedCFZCanonicalCompleteSupportPolylogConstant_nonneg e, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with R hR
  exact
    selectedCFZCanonicalEulerCompletionTailMajorantMass_le_polylog e hR

/-! ## Pointwise and complementary-box bounds -/

/-- The product-indexed scalar majorant used for the signed completion
tail is summable. -/
theorem SmoothSieveCutoff.summable_selectedCFZCanonicalEulerCompletionTailPointwiseMajorant
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    Summable (fun idx :
        SelectedCFZCanonicalCarryEulerCompletionTailIndex e R =>
      cfzCanonicalCarryCellDensity
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1)
          idx.1.1 *
        (selectedCFZCanonicalCompleteSupportMajorant e R idx.2.1 *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu)) := by
  classical
  unfold SelectedCFZCanonicalCarryEulerCompletionTailIndex
  rw [summable_prod_of_nonneg]
  · constructor
    · intro carry
      have hsupport :=
        summable_selectedCFZCanonicalEulerCompletionTailMajorant e hR
      have hscaled :=
        hsupport.mul_left
          (cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry.1 *
            χ.selectedCFZPairedFourierAbsoluteDensity e tu)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
    · exact Summable.of_finite
  · intro idx
    exact mul_nonneg
      (cfzCanonicalCarryCellDensity_nonneg
        (N := N)
        (fun q : SelectedCFZFormIndex e => q.1)
        idx.1.1)
      (mul_nonneg
        (selectedCFZCanonicalCompleteSupportMajorant_nonneg
          e R idx.2.1)
        (χ.selectedCFZPairedFourierAbsoluteDensity_nonneg e tu))

/-- Summing the scalar pointwise majorant over all carry cells and all
missing supports leaves exactly the tail-support mass times the universal
Schwartz density. -/
theorem SmoothSieveCutoff.tsum_selectedCFZCanonicalEulerCompletionTailPointwiseMajorant
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    (∑' idx :
        SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
      cfzCanonicalCarryCellDensity
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1)
          idx.1.1 *
        (selectedCFZCanonicalCompleteSupportMajorant e R idx.2.1 *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu)) =
      selectedCFZCanonicalEulerCompletionTailMajorantMass e R *
        χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  classical
  have hsum :=
    χ.summable_selectedCFZCanonicalEulerCompletionTailPointwiseMajorant
      (N := N) e hR tu
  unfold SelectedCFZCanonicalCarryEulerCompletionTailIndex at hsum ⊢
  rw [hsum.tsum_prod]
  let D : ℝ := χ.selectedCFZPairedFourierAbsoluteDensity e tu
  let M : ℝ :=
    selectedCFZCanonicalEulerCompletionTailMajorantMass e R
  change
    (∑' carry :
        ↥(cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k),
      ∑' S :
          ↥((↑((primesLEAsPrimes R).powerset) :
            Set (Finset Nat.Primes))ᶜ),
        cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1)
            carry.1 *
          (selectedCFZCanonicalCompleteSupportMajorant e R S.1 * D)) =
      M * D
  have hinner
      (carry :
        ↥(cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k)) :
      (∑' S :
          ↥((↑((primesLEAsPrimes R).powerset) :
            Set (Finset Nat.Primes))ᶜ),
        cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1)
            carry.1 *
          (selectedCFZCanonicalCompleteSupportMajorant e R S.1 * D)) =
        cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1)
            carry.1 * (M * D) := by
    rw [show
        (fun S :
            ↥((↑((primesLEAsPrimes R).powerset) :
              Set (Finset Nat.Primes))ᶜ) =>
          cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry.1 *
            (selectedCFZCanonicalCompleteSupportMajorant e R S.1 * D)) =
          (fun S =>
            (cfzCanonicalCarryCellDensity
                (N := N)
                (fun q : SelectedCFZFormIndex e => q.1)
                carry.1 * D) *
              selectedCFZCanonicalCompleteSupportMajorant e R S.1) by
        funext S
        ring]
    rw [tsum_mul_left]
    unfold M selectedCFZCanonicalEulerCompletionTailMajorantMass
    ring
  rw [show
      (fun carry :
          ↥(cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k) =>
        ∑' S :
            ↥((↑((primesLEAsPrimes R).powerset) :
              Set (Finset Nat.Primes))ᶜ),
          cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry.1 *
            (selectedCFZCanonicalCompleteSupportMajorant e R S.1 * D)) =
        (fun carry =>
          cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry.1 * (M * D)) by
      funext carry
      exact hinner carry]
  let F : (SelectedCFZFormIndex e → ℤ) → ℝ :=
    fun carry =>
      cfzCanonicalCarryCellDensity
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1)
          carry * (M * D)
  change
    (∑' carry :
        ↥(cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k),
      F carry.1) = M * D
  calc
    (∑' carry :
        ↥(cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k),
      F carry.1) =
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          F carry :=
      Finset.tsum_subtype
        (cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k) F
    _ = M * D := by
      unfold F
      rw [← Finset.sum_mul,
        sum_cfzCanonicalCarryCellDensity_eq_one]
      simp

/-- One signed completion-tail term is bounded by its scalar support
majorant. -/
theorem SmoothSieveCutoff.norm_selectedCFZCanonicalCarryEulerCompletionTailIntegrand_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (idx : SelectedCFZCanonicalCarryEulerCompletionTailIndex e R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    ‖χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
        (N := N) (w := w) (b := b) e R idx tu‖ ≤
      cfzCanonicalCarryCellDensity
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1)
          idx.1.1 *
        (selectedCFZCanonicalCompleteSupportMajorant e R idx.2.1 *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu) := by
  have hdensity :
      0 ≤
        cfzCanonicalCarryCellDensity
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1)
          idx.1.1 :=
    cfzCanonicalCarryCellDensity_nonneg
      (N := N)
      (fun q : SelectedCFZFormIndex e => q.1)
      idx.1.1
  have hbase :=
    χ.norm_selectedCFZCanonicalCarryCompleteSupportIntegrand_le
      (N := N) hk hbound hwb e idx.1.1 hR idx.2.1 tu
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
  rw [norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hdensity]
  exact mul_le_mul_of_nonneg_left hbase hdensity

/-- Pointwise domination of the full completion discrepancy by the exact
missing-support mass and the universal paired Schwartz density. -/
theorem SmoothSieveCutoff.norm_cfzCanonicalCarryEulerCompletionDiscrepancy_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    ‖χ.cfzCanonicalCarryEulerCompletionDiscrepancy
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu‖ ≤
      selectedCFZCanonicalEulerCompletionTailMajorantMass e R *
        χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  have htail :=
    χ.summable_selectedCFZCanonicalCarryEulerCompletionTailIntegrand
      (N := N) (w := w) (b := b) hk e hR tu
  have hmajorant :=
    χ.summable_selectedCFZCanonicalEulerCompletionTailPointwiseMajorant
      (N := N) e hR tu
  rw [χ.cfzCanonicalCarryEulerCompletionDiscrepancy_eq_tsum_tail
    (N := N) (w := w) (b := b) hk e hR tu]
  calc
    ‖∑' idx :
          SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
        χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
          (N := N) (w := w) (b := b) e R idx tu‖ ≤
        ∑' idx :
            SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
          ‖χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
            (N := N) (w := w) (b := b) e R idx tu‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ ≤
        ∑' idx :
            SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
          cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              idx.1.1 *
            (selectedCFZCanonicalCompleteSupportMajorant e R idx.2.1 *
              χ.selectedCFZPairedFourierAbsoluteDensity e tu) :=
      htail.norm.tsum_le_tsum
        (fun idx =>
          χ.norm_selectedCFZCanonicalCarryEulerCompletionTailIntegrand_le
            (N := N) hk hbound hwb e hR idx tu)
        hmajorant
    _ =
        selectedCFZCanonicalEulerCompletionTailMajorantMass e R *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu :=
      χ.tsum_selectedCFZCanonicalEulerCompletionTailPointwiseMajorant
        (N := N) e hR tu

/-- The complementary Fourier integral is bounded by the exact missing
support mass times the universal paired Schwartz tail. -/
theorem SmoothSieveCutoff.norm_integral_cfzCanonicalCarryEulerCompletionDiscrepancy_compl_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) (T : ℝ) :
    ‖∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
      χ.cfzCanonicalCarryEulerCompletionDiscrepancy
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu
      ∂(volume.prod volume)‖ ≤
      selectedCFZCanonicalEulerCompletionTailMajorantMass e R *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  have hdom :
      ∀ᵐ tu ∂(volume.prod volume).restrict
          (selectedCFZPairedFourierBox e T)ᶜ,
        ‖χ.cfzCanonicalCarryEulerCompletionDiscrepancy
            (N := N) (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1) tu‖ ≤
          selectedCFZCanonicalEulerCompletionTailMajorantMass e R *
            χ.selectedCFZPairedFourierAbsoluteDensity e tu :=
    ae_of_all _ fun tu =>
      χ.norm_cfzCanonicalCarryEulerCompletionDiscrepancy_le
        (N := N) hk hbound hwb e hR tu
  have hboundIntegral :=
    norm_integral_le_of_norm_le
      ((χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
        (selectedCFZCanonicalEulerCompletionTailMajorantMass e R)
        |>.integrableOn)
      hdom
  simpa [selectedCFZPairedFourierAbsoluteTail,
    integral_const_mul] using hboundIntegral

/-! ## The completed Euler model on the complementary box -/

/-- For one carry cell, the completed support series times the paired
Fourier envelope is bounded by the full complete-support mass. -/
theorem SmoothSieveCutoff.norm_pairedEnvelope_mul_selectedCFZCanonicalCarryCompletePrimeSupportSeries_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
        cfzCanonicalCarryCompletePrimeSupportSeries
          N (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1)
          carry tu.1 tu.2‖ ≤
      selectedCFZCanonicalCompleteSupportMass e R *
        χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  have hseries :=
    summable_selectedCFZCanonicalCarry_unrestrictedPrimeSupportTerm
      (N := N) (w := w) (b := b)
      hk e carry hR tu.1 tu.2
  have hintegrand :=
    hseries.mul_left
      (pairedCutoffFourierEnvelope χ tu.1 tu.2)
  have hmajorant :
      Summable (fun S : Finset Nat.Primes =>
        selectedCFZCanonicalCompleteSupportMajorant e R S *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu) :=
    (summable_selectedCFZCanonicalCompleteSupportMajorant e hR).mul_right
      (χ.selectedCFZPairedFourierAbsoluteDensity e tu)
  unfold cfzCanonicalCarryCompletePrimeSupportSeries
  rw [← tsum_mul_left]
  calc
    ‖∑' S : Finset Nat.Primes,
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry tu.1 tu.2) S‖ ≤
        ∑' S : Finset Nat.Primes,
          ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            unrestrictedPrimeSupportTerm
              (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                N (primorial w) b R
                (fun q : SelectedCFZFormIndex e => q.1)
                carry tu.1 tu.2) S‖ :=
      norm_tsum_le_tsum_norm hintegrand.norm
    _ ≤
        ∑' S : Finset Nat.Primes,
          selectedCFZCanonicalCompleteSupportMajorant e R S *
            χ.selectedCFZPairedFourierAbsoluteDensity e tu :=
      hintegrand.norm.tsum_le_tsum
        (fun S =>
          χ.norm_selectedCFZCanonicalCarryCompleteSupportIntegrand_le
            (N := N) hk hbound hwb e carry hR S tu)
        hmajorant
    _ =
        selectedCFZCanonicalCompleteSupportMass e R *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
      rw [tsum_mul_right]
      rfl

/-- Pointwise bound for the completed carry-weighted Euler integrand.
The exact probability normalization of carry-cell densities removes all
dependence on `N`. -/
theorem SmoothSieveCutoff.norm_cfzCanonicalCarryCompleteEulerIntegrand_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    ‖χ.cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu‖ ≤
      selectedCFZCanonicalCompleteSupportMass e R *
        χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  classical
  unfold SmoothSieveCutoff.cfzCanonicalCarryCompleteEulerIntegrand
    cfzCanonicalCarryCompleteFourierAverage
  rw [Finset.mul_sum]
  calc
    ‖∑ carry ∈ cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k,
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          ((cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry : ℂ) *
            cfzCanonicalCarryCompletePrimeSupportSeries
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry tu.1 tu.2)‖ ≤
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            ((cfzCanonicalCarryCellDensity
                (N := N)
                (fun q : SelectedCFZFormIndex e => q.1)
                carry : ℂ) *
              cfzCanonicalCarryCompletePrimeSupportSeries
                N (primorial w) b R
                (fun q : SelectedCFZFormIndex e => q.1)
                carry tu.1 tu.2)‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry *
            (selectedCFZCanonicalCompleteSupportMass e R *
              χ.selectedCFZPairedFourierAbsoluteDensity e tu) := by
      apply Finset.sum_le_sum
      intro carry hcarry
      have hdensity :
          0 ≤
            cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry :=
        cfzCanonicalCarryCellDensity_nonneg
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1)
          carry
      have hcarryBound :=
        χ.norm_pairedEnvelope_mul_selectedCFZCanonicalCarryCompletePrimeSupportSeries_le
          (N := N) hk hbound hwb e carry hR tu
      rw [show
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              ((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
                cfzCanonicalCarryCompletePrimeSupportSeries
                  N (primorial w) b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry tu.1 tu.2) =
            (cfzCanonicalCarryCellDensity
                (N := N)
                (fun q : SelectedCFZFormIndex e => q.1)
                carry : ℂ) *
              (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                cfzCanonicalCarryCompletePrimeSupportSeries
                  N (primorial w) b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry tu.1 tu.2) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hdensity]
      exact mul_le_mul_of_nonneg_left hcarryBound hdensity
    _ =
        selectedCFZCanonicalCompleteSupportMass e R *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
      rw [← Finset.sum_mul,
        sum_cfzCanonicalCarryCellDensity_eq_one]
      simp

/-- Direct complete-model complementary-box estimate. -/
theorem SmoothSieveCutoff.norm_integral_cfzCanonicalCarryCompleteEulerIntegrand_compl_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) (T : ℝ) :
    ‖∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
      χ.cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu
      ∂(volume.prod volume)‖ ≤
      selectedCFZCanonicalCompleteSupportMass e R *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  have hdom :
      ∀ᵐ tu ∂(volume.prod volume).restrict
          (selectedCFZPairedFourierBox e T)ᶜ,
        ‖χ.cfzCanonicalCarryCompleteEulerIntegrand
            (N := N) (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1) tu‖ ≤
          selectedCFZCanonicalCompleteSupportMass e R *
            χ.selectedCFZPairedFourierAbsoluteDensity e tu :=
    ae_of_all _ fun tu =>
      χ.norm_cfzCanonicalCarryCompleteEulerIntegrand_le
        (N := N) hk hbound hwb e hR tu
  have hboundIntegral :=
    norm_integral_le_of_norm_le
      ((χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
        (selectedCFZCanonicalCompleteSupportMass e R)
        |>.integrableOn)
      hdom
  simpa [selectedCFZPairedFourierAbsoluteTail,
    integral_const_mul] using hboundIntegral

/-! ## Selberg-scaled complementary contributions -/

/-- The two Selberg prefactors times the full complete-support mass. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass
    {k : ℕ} (χ : SmoothSieveCutoff)
    (w R : ℕ) (e : LinearFormsExponent k) : ℝ :=
  |normalizedSelbergScale χ.normalizer R (primorial w)| ^
      Fintype.card (SelectedCFZFormIndex e) *
    |Real.log R ^ 2| ^
      Fintype.card (SelectedCFZFormIndex e) *
    selectedCFZCanonicalCompleteSupportMass e R

theorem
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (w R : ℕ) (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _))
    (selectedCFZCanonicalCompleteSupportMass_nonneg e R)

/-- Exponent after including the two Selberg prefactors. -/
def selectedCFZCanonicalCompleteEulerScaledPolylogExponent
    {k : ℕ} (e : LinearFormsExponent k) : ℕ :=
  Fintype.card (SelectedCFZFormIndex e) +
    selectedCFZCanonicalCompleteSupportPolylogExponent e

/-- Constant after including the two Selberg prefactors. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledPolylogConstant
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) : ℝ :=
  χ.normalizer⁻¹ ^ Fintype.card (SelectedCFZFormIndex e) *
    selectedCFZCanonicalCompleteSupportPolylogConstant e

theorem
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledPolylogConstant_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledPolylogConstant
  exact mul_nonneg
    (pow_nonneg (inv_nonneg.mpr χ.normalizer_pos.le) _)
    (selectedCFZCanonicalCompleteSupportPolylogConstant_nonneg e)

/-- Uniform scaled polylogarithmic mass bound.  It is independent of
`N` and of the reduced residue. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass_le_polylog
    {k : ℕ} (χ : SmoothSieveCutoff)
    (w : ℕ) (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e ≤
      χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e *
        (1 + Real.log R) ^
          selectedCFZCanonicalCompleteEulerScaledPolylogExponent e := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  let E := selectedCFZCanonicalCompleteSupportPolylogExponent e
  let C := selectedCFZCanonicalCompleteSupportPolylogConstant e
  have hbase :
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| ≤
        χ.normalizer⁻¹ * (1 + Real.log R) :=
    χ.abs_normalizedSelbergScale_mul_logSq_le hR w
  have hbaseNonneg :
      0 ≤
        |normalizedSelbergScale
            χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| := by positivity
  have hlogNonneg : 0 ≤ 1 + Real.log R := by
    have hlog :
        0 ≤ Real.log R :=
      (Real.log_pos
        (by exact_mod_cast hR : (1 : ℝ) < R)).le
    linarith
  have hupperBaseNonneg :
      0 ≤ χ.normalizer⁻¹ * (1 + Real.log R) :=
    mul_nonneg
      (inv_nonneg.mpr χ.normalizer_pos.le) hlogNonneg
  have hmass :
      selectedCFZCanonicalCompleteSupportMass e R ≤
        C * (1 + Real.log R) ^ E := by
    simpa only [C, E] using
      selectedCFZCanonicalCompleteSupportMass_le_polylog e hR
  have hmassNonneg :
      0 ≤ selectedCFZCanonicalCompleteSupportMass e R :=
    selectedCFZCanonicalCompleteSupportMass_nonneg e R
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledPolylogConstant
    selectedCFZCanonicalCompleteEulerScaledPolylogExponent
  change
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^ m *
        |Real.log R ^ 2| ^ m *
        selectedCFZCanonicalCompleteSupportMass e R ≤
      (χ.normalizer⁻¹ ^ m * C) *
        (1 + Real.log R) ^ (m + E)
  calc
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^ m *
          |Real.log R ^ 2| ^ m *
          selectedCFZCanonicalCompleteSupportMass e R =
        (|normalizedSelbergScale
            χ.normalizer R (primorial w)| *
          |Real.log R ^ 2|) ^ m *
          selectedCFZCanonicalCompleteSupportMass e R := by
      rw [mul_pow]
    _ ≤
        (χ.normalizer⁻¹ * (1 + Real.log R)) ^ m *
          (C * (1 + Real.log R) ^ E) :=
      mul_le_mul
        (pow_le_pow_left₀ hbaseNonneg hbase m)
        hmass hmassNonneg
        (pow_nonneg hupperBaseNonneg m)
    _ =
        (χ.normalizer⁻¹ ^ m * C) *
          (1 + Real.log R) ^ (m + E) := by
      rw [mul_pow, pow_add]
      ring

/-- Selberg-scaled norm of the completion discrepancy on the
complementary Fourier box. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalEulerCompletionScaledTailNorm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) : ℝ :=
  ‖(normalizedSelbergScale
        χ.normalizer R (primorial w) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      (((Real.log R ^ 2 : ℝ) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.cfzCanonicalCarryEulerCompletionDiscrepancy
            (N := N) (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1) tu
          ∂(volume.prod volume))‖

theorem
    SmoothSieveCutoff.selectedCFZCanonicalEulerCompletionScaledTailNorm_nonneg
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) :
    0 ≤ χ.selectedCFZCanonicalEulerCompletionScaledTailNorm
      (N := N) w b R e T :=
  norm_nonneg _

/-- Selberg-scaled norm of the completed Euler model on the
complementary Fourier box. -/
noncomputable def
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) : ℝ :=
  ‖(normalizedSelbergScale
        χ.normalizer R (primorial w) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      (((Real.log R ^ 2 : ℝ) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.cfzCanonicalCarryCompleteEulerIntegrand
            (N := N) (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1) tu
          ∂(volume.prod volume))‖

theorem
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm_nonneg
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) :
    0 ≤ χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
      (N := N) w b R e T :=
  norm_nonneg _

/-- Scaled completion-discrepancy bound by the full support mass and the
universal Schwartz tail. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalEulerCompletionScaledTailNorm_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) (T : ℝ) :
    χ.selectedCFZCanonicalEulerCompletionScaledTailNorm
        (N := N) w b R e T ≤
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalEulerCompletionScaledTailNorm
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass
  rw [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs]
  let A :=
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^
        Fintype.card (SelectedCFZFormIndex e) *
      |Real.log R ^ 2| ^
        Fintype.card (SelectedCFZFormIndex e)
  have hA : 0 ≤ A := by
    unfold A
    positivity
  have hintegral :=
    χ.norm_integral_cfzCanonicalCarryEulerCompletionDiscrepancy_compl_le
      (N := N) hk hbound hwb e hR T
  have htailLe :
      selectedCFZCanonicalEulerCompletionTailMajorantMass e R ≤
        selectedCFZCanonicalCompleteSupportMass e R :=
    selectedCFZCanonicalEulerCompletionTailMajorantMass_le_complete e hR
  have hschwartz :
      0 ≤ χ.selectedCFZPairedFourierAbsoluteTail e T :=
    χ.selectedCFZPairedFourierAbsoluteTail_nonneg e T
  calc
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^
          Fintype.card (SelectedCFZFormIndex e) *
        (|Real.log R ^ 2| ^
            Fintype.card (SelectedCFZFormIndex e) *
          ‖∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
            χ.cfzCanonicalCarryEulerCompletionDiscrepancy
              (N := N) (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1) tu
            ∂(volume.prod volume)‖) =
        A *
          ‖∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
            χ.cfzCanonicalCarryEulerCompletionDiscrepancy
              (N := N) (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1) tu
            ∂(volume.prod volume)‖ := by
      ring
    _ ≤ A *
        (selectedCFZCanonicalEulerCompletionTailMajorantMass e R *
          χ.selectedCFZPairedFourierAbsoluteTail e T) :=
      mul_le_mul_of_nonneg_left hintegral hA
    _ ≤ A *
        (selectedCFZCanonicalCompleteSupportMass e R *
          χ.selectedCFZPairedFourierAbsoluteTail e T) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right htailLe hschwartz) hA
    _ =
        (|normalizedSelbergScale χ.normalizer R (primorial w)| ^
              Fintype.card (SelectedCFZFormIndex e) *
            |Real.log R ^ 2| ^
              Fintype.card (SelectedCFZFormIndex e) *
            selectedCFZCanonicalCompleteSupportMass e R) *
          χ.selectedCFZPairedFourierAbsoluteTail e T := by
      unfold A
      ring

/-- Scaled completed-model bound by the same full support mass and
universal Schwartz tail. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) (T : ℝ) :
    χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
        (N := N) w b R e T ≤
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass
  rw [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs]
  let A :=
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^
        Fintype.card (SelectedCFZFormIndex e) *
      |Real.log R ^ 2| ^
        Fintype.card (SelectedCFZFormIndex e)
  have hA : 0 ≤ A := by
    unfold A
    positivity
  have hintegral :=
    χ.norm_integral_cfzCanonicalCarryCompleteEulerIntegrand_compl_le
      (N := N) hk hbound hwb e hR T
  calc
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^
          Fintype.card (SelectedCFZFormIndex e) *
        (|Real.log R ^ 2| ^
            Fintype.card (SelectedCFZFormIndex e) *
          ‖∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
            χ.cfzCanonicalCarryCompleteEulerIntegrand
              (N := N) (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1) tu
            ∂(volume.prod volume)‖) =
        A *
          ‖∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
            χ.cfzCanonicalCarryCompleteEulerIntegrand
              (N := N) (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1) tu
            ∂(volume.prod volume)‖ := by
      ring
    _ ≤ A *
        (selectedCFZCanonicalCompleteSupportMass e R *
          χ.selectedCFZPairedFourierAbsoluteTail e T) :=
      mul_le_mul_of_nonneg_left hintegral hA
    _ =
        (|normalizedSelbergScale χ.normalizer R (primorial w)| ^
              Fintype.card (SelectedCFZFormIndex e) *
            |Real.log R ^ 2| ^
              Fintype.card (SelectedCFZFormIndex e) *
            selectedCFZCanonicalCompleteSupportMass e R) *
          χ.selectedCFZPairedFourierAbsoluteTail e T := by
      unfold A
      ring

/-! ## High moments and schedule-uniform decay -/

/-- Quantitative high-moment bound for the scaled completion discrepancy. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalEulerCompletionScaledTailNorm_sqrt_log_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalEulerCompletionScaledTailNorm
        (N := N) w b R e (Real.sqrt (Real.log R)) ≤
      (χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e *
        χ.selectedCFZPairedFourierAbsoluteMoment e
          (2 *
            (selectedCFZCanonicalCompleteEulerScaledPolylogExponent e + 1))) *
        ((1 + Real.log R) ^
            selectedCFZCanonicalCompleteEulerScaledPolylogExponent e /
          (Real.log R) ^
            (selectedCFZCanonicalCompleteEulerScaledPolylogExponent e + 1)) := by
  let E := selectedCFZCanonicalCompleteEulerScaledPolylogExponent e
  let C := χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e
  let M :=
    χ.selectedCFZPairedFourierAbsoluteMoment e (2 * (E + 1))
  have hscaled :
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e ≤
        C * (1 + Real.log R) ^ E := by
    simpa only [C, E] using
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass_le_polylog
        w e hR
  have hscaledNonneg :
      0 ≤ χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e :=
    χ.selectedCFZCanonicalCompleteEulerScaledSupportMass_nonneg w R e
  have hmoment :
      χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)) ≤
        M / (Real.log R) ^ (E + 1) := by
    simpa only [M] using
      χ.selectedCFZPairedFourierAbsoluteTail_sqrt_log_le
        e (E + 1) hR
  have hM : 0 ≤ M :=
    χ.selectedCFZPairedFourierAbsoluteMoment_nonneg e (2 * (E + 1))
  have hlog : 0 < Real.log R :=
    Real.log_pos (by exact_mod_cast hR : (1 : ℝ) < R)
  have hquotient :
      0 ≤ M / (Real.log R) ^ (E + 1) :=
    div_nonneg hM (pow_nonneg hlog.le _)
  calc
    χ.selectedCFZCanonicalEulerCompletionScaledTailNorm
        (N := N) w b R e (Real.sqrt (Real.log R)) ≤
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e *
        χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)) :=
      χ.selectedCFZCanonicalEulerCompletionScaledTailNorm_le
        (N := N) hk hbound hwb e hR _
    _ ≤
        χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e *
          (M / (Real.log R) ^ (E + 1)) :=
      mul_le_mul_of_nonneg_left hmoment hscaledNonneg
    _ ≤
        (C * (1 + Real.log R) ^ E) *
          (M / (Real.log R) ^ (E + 1)) :=
      mul_le_mul_of_nonneg_right hscaled hquotient
    _ =
        (C * M) *
          ((1 + Real.log R) ^ E /
            (Real.log R) ^ (E + 1)) := by
      ring
    _ = _ := by rfl

/-- Quantitative high-moment bound for the scaled completed Euler model. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm_sqrt_log_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
        (N := N) w b R e (Real.sqrt (Real.log R)) ≤
      (χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e *
        χ.selectedCFZPairedFourierAbsoluteMoment e
          (2 *
            (selectedCFZCanonicalCompleteEulerScaledPolylogExponent e + 1))) *
        ((1 + Real.log R) ^
            selectedCFZCanonicalCompleteEulerScaledPolylogExponent e /
          (Real.log R) ^
            (selectedCFZCanonicalCompleteEulerScaledPolylogExponent e + 1)) := by
  let E := selectedCFZCanonicalCompleteEulerScaledPolylogExponent e
  let C := χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e
  let M :=
    χ.selectedCFZPairedFourierAbsoluteMoment e (2 * (E + 1))
  have hscaled :
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e ≤
        C * (1 + Real.log R) ^ E := by
    simpa only [C, E] using
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass_le_polylog
        w e hR
  have hscaledNonneg :
      0 ≤ χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e :=
    χ.selectedCFZCanonicalCompleteEulerScaledSupportMass_nonneg w R e
  have hmoment :
      χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)) ≤
        M / (Real.log R) ^ (E + 1) := by
    simpa only [M] using
      χ.selectedCFZPairedFourierAbsoluteTail_sqrt_log_le
        e (E + 1) hR
  have hM : 0 ≤ M :=
    χ.selectedCFZPairedFourierAbsoluteMoment_nonneg e (2 * (E + 1))
  have hlog : 0 < Real.log R :=
    Real.log_pos (by exact_mod_cast hR : (1 : ℝ) < R)
  have hquotient :
      0 ≤ M / (Real.log R) ^ (E + 1) :=
    div_nonneg hM (pow_nonneg hlog.le _)
  calc
    χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
        (N := N) w b R e (Real.sqrt (Real.log R)) ≤
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e *
        χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)) :=
      χ.selectedCFZCanonicalCompleteEulerScaledTailNorm_le
        (N := N) hk hbound hwb e hR _
    _ ≤
        χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e *
          (M / (Real.log R) ^ (E + 1)) :=
      mul_le_mul_of_nonneg_left hmoment hscaledNonneg
    _ ≤
        (C * (1 + Real.log R) ^ E) *
          (M / (Real.log R) ^ (E + 1)) :=
      mul_le_mul_of_nonneg_right hscaled hquotient
    _ =
        (C * M) *
          ((1 + Real.log R) ^ E /
            (Real.log R) ^ (E + 1)) := by
      ring
    _ = _ := by rfl

/-- A fixed nonnegative constant times the standard polylogarithm-over-one-
extra-log expression tends to zero along every radius sequence tending to
infinity. -/
theorem tendsto_const_mul_one_add_log_pow_div_log_pow_succ
    (E : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (Rseq : ℕ → ℕ)
    (hRseq : Tendsto Rseq atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        K *
          ((1 + Real.log (Rseq n)) ^ E /
            (Real.log (Rseq n)) ^ (E + 1)))
      atTop (𝓝 0) := by
  have hlogTop :
      Tendsto (fun n : ℕ => Real.log (Rseq n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hRseq)
  have hinvLog :
      Tendsto (fun n : ℕ => (Real.log (Rseq n))⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlogTop
  have hupper :
      Tendsto
        (fun n : ℕ => K * (2 : ℝ) ^ E / Real.log (Rseq n))
        atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinvLog :
        Tendsto
          (fun n : ℕ =>
            (K * (2 : ℝ) ^ E) * (Real.log (Rseq n))⁻¹)
          atTop (𝓝 ((K * (2 : ℝ) ^ E) * 0)))
  have hlogOne :
      ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Rseq n) :=
    hlogTop.eventually (eventually_ge_atTop 1)
  apply squeeze_zero'
  · filter_upwards [hlogOne] with n hn
    exact mul_nonneg hK
      (div_nonneg
        (pow_nonneg (by linarith) E)
        (pow_nonneg (by linarith) (E + 1)))
  · filter_upwards [hlogOne] with n hn
    exact mul_le_mul_of_nonneg_left
      (SmoothSieveCutoff.one_add_pow_div_pow_succ_le_inv E hn) hK
  · simpa only [div_eq_mul_inv, mul_assoc] using hupper

/-- Schedule-uniform decay of the scaled completion discrepancy.  The
cyclic modulus, primorial cutoff, residue, and sieve radius may all vary. -/
theorem
    SmoothSieveCutoff.tendsto_selectedCFZCanonicalEulerCompletionScaledTailNorm_sqrt_log
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (Nseq wseq bseq Rseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hbound :
      ∀ n,
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) ≤
          wseq n)
    (hcoprime :
      ∀ n, (primorial (wseq n)).Coprime (bseq n))
    (hRseq : Tendsto Rseq atTop atTop)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        χ.selectedCFZCanonicalEulerCompletionScaledTailNorm
          (N := Nseq n) (wseq n) (bseq n) (Rseq n) e
          (Real.sqrt (Real.log (Rseq n))))
      atTop (𝓝 0) := by
  let E := selectedCFZCanonicalCompleteEulerScaledPolylogExponent e
  let K : ℝ :=
    χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e *
      χ.selectedCFZPairedFourierAbsoluteMoment e (2 * (E + 1))
  have hK : 0 ≤ K :=
    mul_nonneg
      (χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant_nonneg e)
      (χ.selectedCFZPairedFourierAbsoluteMoment_nonneg
        e (2 * (E + 1)))
  have hupper :=
    tendsto_const_mul_one_add_log_pow_div_log_pow_succ
      E hK Rseq hRseq
  have hRtwo : ∀ᶠ n : ℕ in atTop, 2 ≤ Rseq n :=
    hRseq.eventually (eventually_ge_atTop 2)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by
      letI : NeZero (Nseq n) := ⟨hN n⟩
      exact
        χ.selectedCFZCanonicalEulerCompletionScaledTailNorm_nonneg
          (N := Nseq n) (wseq n) (bseq n) (Rseq n) e _
  · filter_upwards [hRtwo] with n hRn
    letI : NeZero (Nseq n) := ⟨hN n⟩
    simpa only [E, K] using
      χ.selectedCFZCanonicalEulerCompletionScaledTailNorm_sqrt_log_le
        (N := Nseq n) hk (hbound n) (hcoprime n) e hRn
  · exact hupper

/-- Schedule-uniform decay of the completed Euler model outside the
growing Fourier box. -/
theorem
    SmoothSieveCutoff.tendsto_selectedCFZCanonicalCompleteEulerScaledTailNorm_sqrt_log
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (Nseq wseq bseq Rseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hbound :
      ∀ n,
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) ≤
          wseq n)
    (hcoprime :
      ∀ n, (primorial (wseq n)).Coprime (bseq n))
    (hRseq : Tendsto Rseq atTop atTop)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
          (N := Nseq n) (wseq n) (bseq n) (Rseq n) e
          (Real.sqrt (Real.log (Rseq n))))
      atTop (𝓝 0) := by
  let E := selectedCFZCanonicalCompleteEulerScaledPolylogExponent e
  let K : ℝ :=
    χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e *
      χ.selectedCFZPairedFourierAbsoluteMoment e (2 * (E + 1))
  have hK : 0 ≤ K :=
    mul_nonneg
      (χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant_nonneg e)
      (χ.selectedCFZPairedFourierAbsoluteMoment_nonneg
        e (2 * (E + 1)))
  have hupper :=
    tendsto_const_mul_one_add_log_pow_div_log_pow_succ
      E hK Rseq hRseq
  have hRtwo : ∀ᶠ n : ℕ in atTop, 2 ≤ Rseq n :=
    hRseq.eventually (eventually_ge_atTop 2)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by
      letI : NeZero (Nseq n) := ⟨hN n⟩
      exact
        χ.selectedCFZCanonicalCompleteEulerScaledTailNorm_nonneg
          (N := Nseq n) (wseq n) (bseq n) (Rseq n) e _
  · filter_upwards [hRtwo] with n hRn
    letI : NeZero (Nseq n) := ⟨hN n⟩
    simpa only [E, K] using
      χ.selectedCFZCanonicalCompleteEulerScaledTailNorm_sqrt_log_le
        (N := Nseq n) hk (hbound n) (hcoprime n) e hRn
  · exact hupper

end Wikipedia.SzemeredisTheorem
