import ErdosProblems.Erdos4.FGKMTConcreteNormalization
import ErdosProblems.Erdos4.FGKMTLawOperations

/-! Normalized center laws for the actual translated rational weights. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductCharacterEncoding

abbrev TranslatedCenter (Y : ℕ) := ↥(Finset.Icc 1 (2 * Y))

def firstTranslatedCenter {Y : ℕ} (hY : 1 ≤ Y) : TranslatedCenter Y :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]

theorem translatedCenter_weight_sum (b : ℝ) (R : ℕ) (h : Fin k → ℕ) (Y p : ℕ) :
    (∑ n : TranslatedCenter Y, maskedTranslatedWeight ell₀ ell₁ b R h Y p n.val) =
      maskedTranslatedNormalizer ell₀ ell₁ b R h Y p :=
  Finset.sum_coe_sort (Finset.Icc 1 (2 * Y))
    (maskedTranslatedWeight ell₀ ell₁ b R h Y p)

noncomputable def rationalCenterLaw (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p : ℕ) : FiniteLaw (TranslatedCenter Y) :=
  FiniteLaw.normalize (fun n => maskedTranslatedWeight ell₀ ell₁ b R h Y p n.val)
    (fun n => maskedTranslatedWeight_nonneg ell₀ ell₁ b R h Y p n.val)
    (firstTranslatedCenter hY)

theorem rationalCenterLaw_weight (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p : ℕ)
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p)
    (n : TranslatedCenter Y) :
    (rationalCenterLaw ell₀ ell₁ b R h hY p).weight n =
      maskedTranslatedWeight ell₀ ell₁ b R h Y p n.val /
        maskedTranslatedNormalizer ell₀ ell₁ b R h Y p := by
  have hsum : (∑ a : TranslatedCenter Y,
      maskedTranslatedWeight ell₀ ell₁ b R h Y p a.val) ≠ 0 := by
    rw [translatedCenter_weight_sum]
    exact hZ.ne'
  rw [rationalCenterLaw, FiniteLaw.normalize_weight _ _ _ _ hsum,
    translatedCenter_weight_sum]

theorem rationalCenterLaw_weight_pos_iff (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p : ℕ)
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p)
    (n : TranslatedCenter Y) :
    0 < (rationalCenterLaw ell₀ ell₁ b R h hY p).weight n ↔
      0 < maskedTranslatedWeight ell₀ ell₁ b R h Y p n.val := by
  rw [rationalCenterLaw_weight ell₀ ell₁ b R h hY p hZ n]
  exact div_pos_iff_of_pos_right hZ

theorem rationalCenterLaw_prob_eq_sum (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p : ℕ)
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p) (E : ℕ → Prop) :
    (rationalCenterLaw ell₀ ell₁ b R h hY p).prob (fun n => E n.val) =
      (∑ n ∈ Finset.Icc 1 (2 * Y),
        if E n then maskedTranslatedWeight ell₀ ell₁ b R h Y p n else 0) /
          maskedTranslatedNormalizer ell₀ ell₁ b R h Y p := by
  calc
    _ = ∑ n : TranslatedCenter Y,
        (if E n.val then maskedTranslatedWeight ell₀ ell₁ b R h Y p n.val else 0) /
          maskedTranslatedNormalizer ell₀ ell₁ b R h Y p := by
      unfold FiniteLaw.prob
      apply Finset.sum_congr rfl
      intro n _
      rw [rationalCenterLaw_weight ell₀ ell₁ b R h hY p hZ n]
      by_cases hn : E n.val <;> simp only [hn, if_true, if_false, zero_div]
    _ = _ := by
      rw [← Finset.sum_div]
      exact congrArg (fun s : ℝ => s / maskedTranslatedNormalizer ell₀ ell₁ b R h Y p)
        (Finset.sum_coe_sort (Finset.Icc 1 (2 * Y))
          (fun n : ℕ => if E n then maskedTranslatedWeight ell₀ ell₁ b R h Y p n else 0))

theorem rationalCenterLaw_weight_le_modulus {b : ℝ} (hb : 0 ≤ b) {R : ℕ} (hR : 1 ≤ R)
    (hell : ∀ l, k + 2 ≤ ell₁ l)
    (htail : (k : ℝ) * LocalIndicatorExpansion.rowCost k * ∑ l, 1 / (ell₁ l : ℝ) ^ 2 ≤ 1)
    (h : Fin k → ℕ)
    (hadm : ∀ l, ∃ x, SmallPrimeGood (fun i => (h i : ZMod (ell₀ l))) x)
    {Y : ℕ} (hY : 1 ≤ Y) (p : ℕ)
    (hlower : smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * Y *
      RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁) ≤
        maskedTranslatedNormalizer ell₀ ell₁ b R h Y p)
    (n : TranslatedCenter Y) :
    (rationalCenterLaw ell₀ ell₁ b R h hY p).weight n ≤
      (Real.exp 1 ^ 2 * (R : ℝ) ^ 4) * (modulus ell₀ : ℝ) / Y := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hMr : (0 : ℝ) < modulus ell₀ := by
    exact_mod_cast (Finset.prod_pos (fun l _ => (Fact.out : (ell₀ l).Prime).pos) :
      0 < modulus ell₀)
  have hα := smallProductDensity_nonneg ell₀ (fun l i => (h i : ZMod (ell₀ l)))
  have hαinv := smallProductDensity_ge_inv ell₀ (fun l i => (h i : ZMod (ell₀ l))) hadm
  have hE := one_le_rationalCoefficient_energy (k := k) b hR ell₁
  have hden : (Y : ℝ) / modulus ell₀ ≤ maskedTranslatedNormalizer ell₀ ell₁ b R h Y p := by
    calc
      _ = (modulus ell₀ : ℝ)⁻¹ * Y := by ring
      _ ≤ smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * Y :=
        mul_le_mul_of_nonneg_right hαinv hYr.le
      _ ≤ smallProductDensity ell₀ (fun l i => (h i : ZMod (ell₀ l))) * Y *
          RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hE (mul_nonneg hα hYr.le)
      _ ≤ _ := hlower
  have hZ := (div_pos hYr hMr).trans_le hden
  rw [rationalCenterLaw_weight ell₀ ell₁ b R h hY p hZ n]
  calc
    _ ≤ (Real.exp 1 ^ 2 * (R : ℝ) ^ 4) /
        maskedTranslatedNormalizer ell₀ ell₁ b R h Y p :=
      div_le_div_of_nonneg_right (maskedTranslatedWeight_le ell₁ ell₀ hb R hell htail h Y p n.val)
        hZ.le
    _ ≤ (Real.exp 1 ^ 2 * (R : ℝ) ^ 4) / ((Y : ℝ) / modulus ell₀) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hYr hMr) hden
    _ = _ := by field_simp

end Erdos4.FGKMT
