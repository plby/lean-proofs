import ErdosProblems.Erdos4.FGKMTTranslatedIncidence
import ErdosProblems.Erdos4.FGKMTSourceLowerBound

/-! Transfer the proved Fourier source averages to actual center-law incidences. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductCharacterEncoding AnchoredFourierAverage

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]

noncomputable def rationalSourceIncidence (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (sources : Finset ℕ) (a : sources → ℝ) (q : ℕ) : ℝ :=
  ∑ p : sources, a p * rationalBaseIncidence ell₀ ell₁ b R h hY p.val q

theorem rationalSourceIncidence_nonneg (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    {Y : ℕ} (hY : 1 ≤ Y) (sources : Finset ℕ) (a : sources → ℝ)
    (ha : ∀ p, 0 ≤ a p) (q : ℕ) :
    0 ≤ rationalSourceIncidence ell₀ ell₁ b R h hY sources a q :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (ha p)
    (rationalBaseIncidence_nonneg ell₀ ell₁ b R h hY p.val q))

theorem rationalBaseIncidence_lower_of_normalizer_le (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    (hinj : Function.Injective h)
    (hlarge : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    {Y : ℕ} (hY : 1 ≤ Y) (p q : ℕ) (hp0 : 0 < p) (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hshift : ∀ i, h i * p ≤ Y)
    (hp : p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (hq : q.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (hZ : 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p)
    {K : ℝ} (hupper : maskedTranslatedNormalizer ell₀ ell₁ b R h Y p ≤ K) :
    aggregateUnitWeight ell₀ ell₁ b R
      (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l)))
      (unitPoint (Sum.elim ell₀ ell₁) p hp / unitPoint (Sum.elim ell₀ ell₁) q hq) / K ≤
        rationalBaseIncidence ell₀ ell₁ b R h hY p q := by
  rw [rationalBaseIncidence_eq_unitWeight ell₀ ell₁ b R h hinj hlarge hY p q hp0 hq0 hqY
    hshift hp hq hZ]
  exact div_le_div_of_nonneg_left (aggregateUnitWeight_nonneg ell₀ ell₁ b R _ _ _) hZ hupper

theorem rationalSourceIncidence_lower_of_average (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    (hinj : Function.Injective h)
    (hlarge : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    {Y : ℕ} (hY : 1 ≤ Y) (sources : Finset ℕ)
    (hpos : ∀ p : sources, 0 < p.val) (hshift : ∀ p : sources, ∀ i, h i * p.val ≤ Y)
    (hs : ∀ p ∈ sources, p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (a : sources → ℝ) (ha : ∀ p, 0 ≤ a p) (q : ℕ) (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hq : q.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (hZ : ∀ p : sources, 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p.val)
    {K H : ℝ} (hK : 0 < K)
    (hupper : ∀ p : sources, maskedTranslatedNormalizer ell₀ ell₁ b R h Y p.val ≤ K)
    (haverage : H ≤ ∑ p : sources, a p * aggregateUnitWeight ell₀ ell₁ b R
      (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l)))
      (unitPoint (Sum.elim ell₀ ell₁) p (hs p p.property) /
        unitPoint (Sum.elim ell₀ ell₁) q hq)) :
    H / K ≤ rationalSourceIncidence ell₀ ell₁ b R h hY sources a q := by
  calc
    _ ≤ (∑ p : sources, a p * aggregateUnitWeight ell₀ ell₁ b R
        (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l)))
        (unitPoint (Sum.elim ell₀ ell₁) p (hs p p.property) /
          unitPoint (Sum.elim ell₀ ell₁) q hq)) / K :=
      div_le_div_of_nonneg_right haverage hK.le
    _ = ∑ p : sources, a p * (aggregateUnitWeight ell₀ ell₁ b R
        (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l)))
        (unitPoint (Sum.elim ell₀ ell₁) p (hs p p.property) /
          unitPoint (Sum.elim ell₀ ell₁) q hq) / K) := by
      simp only [Finset.sum_div, mul_div_assoc]
    _ ≤ _ := Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
      (rationalBaseIncidence_lower_of_normalizer_le ell₀ ell₁ b R h hinj hlarge hY p.val q
        (hpos p) hq0 hqY (hshift p) (hs p p.property) hq (hZ p) (hupper p)) (ha p))

theorem rationalSourceIncidence_fourier_lower (b : ℝ) (R M : ℕ)
    (hM : (∏ l, ell₀ l) * R ^ 2 ≤ M ^ 2) (h : Fin k → ℕ) (hinj : Function.Injective h)
    (hlarge : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    {Y : ℕ} (hY : 1 ≤ Y) (sources : Finset ℕ)
    (hpos : ∀ p : sources, 0 < p.val) (hshift : ∀ p : sources, ∀ i, h i * p.val ≤ Y)
    (hs : ∀ p ∈ sources, p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (a : sources → ℝ) (ha : ∀ p, 0 ≤ a p) (q : ℕ) (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hq : q.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (hZ : ∀ p : sources, 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p.val)
    {K η ε : ℝ} (hK : 0 < K)
    (hupper : ∀ p : sources, maskedTranslatedNormalizer ell₀ ell₁ b R h Y p.val ≤ K)
    (hhigh : ‖ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
      (highMaskedCoefficient ell₀ ell₁ b R M
        (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l))))
      sources (fun p => (a p : ℂ)) q‖ ≤ η)
    (hlow : ‖ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
      (lowMaskedCoefficient ell₀ ell₁ b R M
        (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l))))
      sources (fun p => (a p : ℂ)) q‖ ≤ ε) :
    ((∑ p : sources, a p) * aggregatePrincipalMass ell₀ ell₁ b R
      (fun l i => (h i : ZMod (ell₀ l))) - η - ε) / K ≤
        rationalSourceIncidence ell₀ ell₁ b R h hY sources a q :=
  rationalSourceIncidence_lower_of_average ell₀ ell₁ b R h hinj hlarge hY sources hpos hshift hs
    a ha q hq0 hqY hq hZ hK hupper
    (aggregate_real_source_average_lower ell₀ ell₁ b R M hM
      (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l))) hlarge
      sources hs a q hq hhigh hlow)

end Erdos4.FGKMT
