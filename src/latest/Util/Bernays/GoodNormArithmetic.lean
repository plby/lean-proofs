import Util.Bernays.GoodNormSupport
import Util.Bernays.NormClassPartition
import Util.Bernays.SquareSupportArithmetic

/-!
# Arithmetic functions for good norms and their genus twists
-/

open scoped Classical

namespace Bernays

noncomputable def coprimeAF (M : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if 0 < n ∧ n.Coprime M then 1 else 0, by simp⟩

theorem coprimeAF_isMultiplicative (M : ℕ) : (coprimeAF M).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [coprimeAF]
  · intro m n hm hn _
    change (if 0 < m * n ∧ (m * n).Coprime M then (1 : ℂ) else 0) =
      (if 0 < m ∧ m.Coprime M then 1 else 0) * (if 0 < n ∧ n.Coprime M then 1 else 0)
    simp only [Nat.pos_iff_ne_zero, mul_ne_zero hm hn, hm, hn, true_and, Nat.coprime_mul_iff_left]
    split_ifs <;> simp_all

theorem coprimeAF_primePower (M : ℕ) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) :
    coprimeAF M (p ^ e) = if p.Coprime M then 1 else 0 := by
  simp only [coprimeAF, ArithmeticFunction.coe_mk, pow_pos hp.pos e, true_and,
    Nat.coprime_pow_left_iff he]

noncomputable def goodIdealNormAF {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) : ArithmeticFunction ℂ :=
  letI := quadraticOrderIsDomain hD
  ⟨fun n => (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) n) : ℂ), by
    rw [goodIdealNormFiber_card_zero hD, Nat.cast_zero]⟩

theorem goodIdealNormAF_isMultiplicative {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    (goodIdealNormAF hD).IsMultiplicative := by
  letI := quadraticOrderIsDomain hD
  constructor
  · change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) 1) : ℂ) = 1
    rw [goodIdealNormFiber_card_one hD, Nat.cast_one]
  · intro m n hc
    change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (m * n)) : ℂ) =
      (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) m) : ℂ) *
        (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) n) : ℂ)
    rw [goodIdealNormFiber_card_mul hD _ m n hc, Nat.cast_mul]

noncomputable def genusWeightAF {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ → ArithmeticFunction ℂ :=
  letI := quadraticOrderIsDomain hD
  fun ψ => ⟨fun n => if n = 0 then 0 else ψ (Additive.ofMul (genusValue hD n)), by simp⟩

theorem genusWeightAF_apply {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ n : ℕ, n ≠ 0 → genusWeightAF hD ψ n = ψ (Additive.ofMul (genusValue hD n)) := by
  letI := quadraticOrderIsDomain hD
  intro ψ n hn
  simp only [genusWeightAF, ArithmeticFunction.coe_mk, if_neg hn]

theorem genusWeightAF_isMultiplicative {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      (genusWeightAF hD ψ).IsMultiplicative := by
  letI := quadraticOrderIsDomain hD
  intro ψ
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · rw [genusWeightAF_apply hD ψ 1 (by decide), genusValue_one]
    exact ψ.map_zero_eq_one
  · intro m n hm hn _
    rw [genusWeightAF_apply hD ψ _ (mul_ne_zero hm hn), genusWeightAF_apply hD ψ m hm,
      genusWeightAF_apply hD ψ n hn, genusValue_mul hD (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn),
      ofMul_mul, AddChar.map_add_eq_mul]

theorem genusWeightAF_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ p : ℕ, p.Prime → ∀ e : ℕ,
      genusWeightAF hD ψ (p ^ e) = ψ (Additive.ofMul (primeGenus hD p)) ^ e := by
  letI := quadraticOrderIsDomain hD
  intro ψ p hp e
  rw [genusWeightAF_apply hD ψ _ (pow_ne_zero _ hp.ne_zero), genusValue_primePower hD hp,
    ofMul_pow, AddChar.map_nsmul_eq_pow]

end Bernays
