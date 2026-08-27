import ErdosProblems.Erdos4.FGKMTTranslatedIncidence
import ErdosProblems.Erdos4.FGKMTGrowingCenterLaw
import ErdosProblems.Erdos4.TupleCollisionMass

/-! The actual center probabilities in the natural-indexed format used by the tuple moments. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]

noncomputable def rationalCenterMass (b : ℝ) (R : ℕ) (h : Fin k → ℕ) (Y p n : ℕ) : ℝ :=
  maskedTranslatedWeight ell₀ ell₁ b R h Y p n / maskedTranslatedNormalizer ell₀ ell₁ b R h Y p

theorem rationalCenterMass_nonneg (b : ℝ) (R : ℕ) (h : Fin k → ℕ) (Y p n : ℕ)
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p) :
    0 ≤ rationalCenterMass ell₀ ell₁ b R h Y p n :=
  div_nonneg (maskedTranslatedWeight_nonneg ell₀ ell₁ b R h Y p n) hZ.le

theorem rationalCenterMass_sum (b : ℝ) (R : ℕ) (h : Fin k → ℕ) (Y p : ℕ)
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p) :
    (∑ n ∈ Finset.Icc 1 (2 * Y), rationalCenterMass ell₀ ell₁ b R h Y p n) = 1 := by
  unfold rationalCenterMass
  rw [← Finset.sum_div]
  change maskedTranslatedNormalizer ell₀ ell₁ b R h Y p /
    maskedTranslatedNormalizer ell₀ ell₁ b R h Y p = 1
  exact div_self hZ.ne'

theorem rationalCenterMass_eq_weight (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p : ℕ)
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p) (n : TranslatedCenter Y) :
    rationalCenterMass ell₀ ell₁ b R h Y p n.val =
      (rationalCenterLaw ell₀ ell₁ b R h hY p).weight n :=
  (rationalCenterLaw_weight ell₀ ell₁ b R h hY p hZ n).symm

theorem rationalCenterMass_hitMass (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (p q : ℕ) (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p) :
    TupleCollisionMass.hitMass h p (2 * Y) (rationalCenterMass ell₀ ell₁ b R h Y p) (q + Y) =
      rationalBaseIncidence ell₀ ell₁ b R h hY p q := by
  rw [rationalBaseIncidence_eq_full ell₀ ell₁ b R h hY p q hq0 hqY,
    rationalCenterLaw_prob_eq_sum ell₀ ell₁ b R h hY p hZ
      (fun n : ℕ => q + Y ∈ translatedSites h p n)]
  rw [Finset.sum_div]
  unfold TupleCollisionMass.hitMass rationalCenterMass
  apply Finset.sum_congr rfl
  intro n _
  change (if q + Y ∈ translatedSites h p n then
    maskedTranslatedWeight ell₀ ell₁ b R h Y p n /
      maskedTranslatedNormalizer ell₀ ell₁ b R h Y p else 0) = _
  split_ifs <;> simp

end Erdos4.FGKMT
