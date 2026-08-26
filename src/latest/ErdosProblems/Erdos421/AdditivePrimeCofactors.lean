import ErdosProblems.Erdos421.CanonicalPrimeSieve
import ErdosProblems.Erdos421.RoughWindowControl

/-! # Actual additive prime-cofactor windows between convolved sieve errors -/

namespace Erdos421

noncomputable def additivePrimeCofactorWindow (P : Finset ℕ) (B z : ℕ) (Y x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 B, (additiveIntegerWeight Y x n).re * primeCofactorWeight P z n

theorem additivePrimeCofactorWindow_upper (P : Finset ℕ) {Q D : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (hD : 1 ≤ D) (z : ℕ) {Y x : ℝ}
    (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    additivePrimeCofactorWindow P B z Y x ≤
      (∑ p ∈ P, (p : ℝ)⁻¹) * canonicalUpperMain D z +
        ‖sieveWindowError (Q * D ^ 2)
          (primeDivisorConvolution P (canonicalUpperSieve D z)) Y x‖ := by
  have hu : additivePrimeCofactorWindow P B z Y x ≤
      ∑ m ∈ Finset.Icc 1 (Q * D ^ 2), primeDivisorConvolution P (canonicalUpperSieve D z) m *
        (additiveDivisorWindow oneSidedSchwartzWindow Y x m).re := by
    rw [finite_sieve_window_identity _ _ hY hx hB]
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (canonicalPrimeUpper_pointwise P hP hD z n)
      (additiveIntegerWeight_re_nonneg hY x n)
  have he := sieveWindowError_re (Q * D ^ 2)
    (primeDivisorConvolution P (canonicalUpperSieve D z)) Y x
  rw [canonicalPrimeUpper_main P hP] at he
  have hn := Complex.re_le_norm (sieveWindowError (Q * D ^ 2)
    (primeDivisorConvolution P (canonicalUpperSieve D z)) Y x)
  linarith

theorem additivePrimeCofactorWindow_lower (P : Finset ℕ) {Q D z : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (hD : 1 ≤ D) (hz : 1 ≤ z) {Y x : ℝ}
    (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    (∑ p ∈ P, (p : ℝ)⁻¹) * canonicalLowerMain D z -
      ‖sieveWindowError (Q * (z * D ^ 2))
        (primeDivisorConvolution P (lowerSieveCoefficient D z)) Y x‖ ≤
          additivePrimeCofactorWindow P B z Y x := by
  have hl : (∑ m ∈ Finset.Icc 1 (Q * (z * D ^ 2)),
      primeDivisorConvolution P (lowerSieveCoefficient D z) m *
        (additiveDivisorWindow oneSidedSchwartzWindow Y x m).re) ≤
          additivePrimeCofactorWindow P B z Y x := by
    rw [finite_sieve_window_identity _ _ hY hx hB]
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (canonicalPrimeLower_pointwise P hP hD hz n)
      (additiveIntegerWeight_re_nonneg hY x n)
  have he := sieveWindowError_re (Q * (z * D ^ 2))
    (primeDivisorConvolution P (lowerSieveCoefficient D z)) Y x
  rw [canonicalPrimeLower_main P hP hD hz] at he
  have hn := (abs_le.mp (Complex.abs_re_le_norm (sieveWindowError (Q * (z * D ^ 2))
    (primeDivisorConvolution P (lowerSieveCoefficient D z)) Y x))).1
  linarith

theorem additivePrimeCofactorWindow_relative_control (P : Finset ℕ) {Q D z : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (hD : 0 < D) (hz : 2 ≤ z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlevel : 16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z)
    {Y x : ℝ} (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    |additivePrimeCofactorWindow P B z Y x -
      (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z| ≤
        ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z +
          ‖sieveWindowError (Q * D ^ 2)
            (primeDivisorConvolution P (canonicalUpperSieve D z)) Y x‖ +
          ‖sieveWindowError (Q * (z * D ^ 2))
            (primeDivisorConvolution P (lowerSieveCoefficient D z)) Y x‖ := by
  have hR : 0 ≤ ∑ p ∈ P, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ ↦ inv_nonneg.mpr (Nat.cast_nonneg p))
  have hu := additivePrimeCofactorWindow_upper P hP hD z hY hx hB
  have hl := additivePrimeCofactorWindow_lower P (z := z) hP hD (by omega) hY hx hB
  have huM := mul_le_mul_of_nonneg_left (canonicalUpperMain_le_one_add hD hz hε hε1 hlevel) hR
  have hlM := mul_le_mul_of_nonneg_left (canonicalLowerMain_ge_one_sub hD hz hε hε1 hlevel) hR
  have hnU := norm_nonneg (sieveWindowError (Q * D ^ 2)
    (primeDivisorConvolution P (canonicalUpperSieve D z)) Y x)
  have hnL := norm_nonneg (sieveWindowError (Q * (z * D ^ 2))
    (primeDivisorConvolution P (lowerSieveCoefficient D z)) Y x)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem additivePrimeCofactorWindow_continuous (P : Finset ℕ) (B z : ℕ) (Y : ℝ) :
    Continuous (additivePrimeCofactorWindow P B z Y) := by
  apply continuous_finsetSum
  intro n hn
  apply Continuous.mul _ continuous_const
  unfold additiveIntegerWeight
  have harg : Continuous (fun x : ℝ ↦ (x - (n : ℝ)) / Y) :=
    (continuous_id.sub continuous_const).div_const Y
  exact Complex.continuous_re.comp
    ((oneSidedSchwartzWindow.continuous.comp harg).const_smul (Y⁻¹ : ℝ))

end Erdos421
