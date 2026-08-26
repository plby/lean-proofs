import ErdosProblems.Erdos421.RoughBaseAsymptotic
import ErdosProblems.Erdos421.RoughBuchstabMain
import ErdosProblems.Erdos421.RoughCofactorParameters

/-! # The quantitative assertion used for finite Buchstab induction -/

namespace Erdos421

def RoughCountEstimate (n : ℕ) (C : ℝ) : Prop :=
  ∀ A ε : ℝ, 0 ≤ A → 0 < ε → ∃ B > 1, ∀ b : ℝ, B ≤ b →
    ∀ a : ℝ, b / 2 ≤ a → a ≤ b → ∀ z : ℕ, 2 ≤ z → (z : ℝ) ≤ b →
      b ≤ (z : ℝ) ^ (n + 2) →
      |((roughInRealInterval a b z).card : ℝ) - roughCountMain n a b z| ≤
        ε * b / (Real.log b) ^ A + C * (b - a) ^ 2 / (b * (Real.log b) ^ 2)

theorem roughCountEstimate_zero : RoughCountEstimate 0 8 := by
  intro A ε hA hε
  exact rough_base_asymptotic hA hε

theorem roughCountMain_eq_base (n : ℕ) {a b : ℝ} {z : ℕ}
    (hz : 2 ≤ z) (hzb : (z : ℝ) ≤ b) (hbz : b ≤ (z : ℝ) ^ 2) :
    roughCountMain n a b z = roughCountMain 0 a b z := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hbp : 0 < b := by linarith
  have hlz := Real.log_pos hz1
  have hlog := log_le_nat_power_scale hbp hbz
  norm_num only [Nat.cast_ofNat] at hlog
  have hs : Real.log b / Real.log z ≤ 2 := (div_le_iff₀ hlz).mpr hlog
  unfold roughCountMain
  rw [finiteBuchstab_of_le_two n hs, finiteBuchstab]

end Erdos421
