/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A local two-root probability bound with all analytic inputs proved.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.TwoRoots
import ErdosProblems.Erdos521.DerivativeEnergy
import ErdosProblems.Erdos521.LocalRootBounds
import ErdosProblems.Erdos521.SmallBall

namespace Erdos521

open MeasureTheory Filter

theorem two_interval_roots_probability_split (n : ℕ) {a b δ : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (hδ : 0 < δ) :
    sequenceLaw.real {ε | 2 ≤ intervalRootCount ε n a b} ≤
      sequenceLaw.real {ε | |powerSum ε (n + 1) b| ≤ δ} +
        24 * (b - a) ^ 4 / (δ ^ 2 * (1 - b) ^ 5) := by
  let S := {ε : ℕ → ℝ | |powerSum ε (n + 1) b| ≤ δ}
  let E := {ε : ℕ → ℝ | δ ^ 2 / (b - a) ^ 3 ≤ secondDerivativeEnergy n a b ε}
  have hL : 0 < b - a := sub_pos.mpr hab
  have ht : 0 < δ ^ 2 / (b - a) ^ 3 := by positivity
  have hsub : {ε | 2 ≤ intervalRootCount ε n a b} ⊆ S ∪ E := by
    intro ε hε
    by_cases hsmall : ε ∈ S
    · exact Or.inl hsmall
    · apply Or.inr
      have hvalue : δ < |(polynomial ε n).eval b| := by
        rw [polynomial_eval]
        exact lt_of_not_ge hsmall
      have hsq : δ ^ 2 ≤ ((polynomial ε n).eval b) ^ 2 := by
        nlinarith [sq_abs ((polynomial ε n).eval b)]
      have hbound := hsq.trans (two_interval_roots_value_sq_le ε n hε)
      apply (div_le_iff₀ (pow_pos hL 3)).mpr
      simpa only [secondDerivativeEnergy, mul_comm] using hbound
  have hE : sequenceLaw.real E ≤
      (∫ ε, secondDerivativeEnergy n a b ε ∂sequenceLaw) / (δ ^ 2 / (b - a) ^ 3) :=
    measureReal_le_integral_div_of_ae sequenceLaw (secondDerivativeEnergy_integrable n ha hab.le hb.le)
      (Eventually.of_forall (secondDerivativeEnergy_nonneg n hab.le)) ht (Eventually.of_forall fun _ h ↦ h)
  have hE' : sequenceLaw.real E ≤ 24 * (b - a) ^ 4 / (δ ^ 2 * (1 - b) ^ 5) := by
    apply hE.trans
    calc
      (∫ ε, secondDerivativeEnergy n a b ε ∂sequenceLaw) / (δ ^ 2 / (b - a) ^ 3) ≤
          (24 * (b - a) / (1 - b) ^ 5) / (δ ^ 2 / (b - a) ^ 3) :=
        div_le_div_of_nonneg_right (integral_secondDerivativeEnergy_le n ha hab.le hb) ht.le
      _ = _ := by field_simp
  exact ((measureReal_mono hsub).trans (measureReal_union_le S E)).trans (add_le_add le_rfl hE')

theorem two_interval_roots_probability (n L : ℕ) (hL : 2 * L ≤ n + 1) {a b δ : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb₀ : 1 / 2 ≤ b) (hb₁ : b < 1) (hδ : 0 < δ) :
    let c : ℝ := 1 / (4 * Real.pi ^ 2)
    sequenceLaw.real {ε | 2 ≤ intervalRootCount ε n a b} ≤
      Real.exp (1 / 2) *
        (Real.sqrt (Real.pi / (c * geometricVariance b (n + 1) / δ ^ 2)) +
          Real.exp (-c * geometricVariance b (n + 1)) +
          2 * Real.exp (-(δ * (b ^ L)⁻¹) ^ 2 / 2)) +
        24 * (b - a) ^ 4 / (δ ^ 2 * (1 - b) ^ 5) := by
  apply (two_interval_roots_probability_split n ha hab hb₁ hδ).trans
  exact add_le_add (powerSum_smallBall n L hL hb₀ hb₁.le hδ) le_rfl

end Erdos521
