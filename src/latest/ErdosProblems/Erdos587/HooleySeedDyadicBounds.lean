import ErdosProblems.Erdos587.HooleySeedCostBounds
import ErdosProblems.Erdos587.DyadicScaleBudgets

/-! # Uniform dyadic budgets for the lattice seed -/

open Filter

namespace Erdos587.CFP

theorem delta_eventually_shifted_polynomial_le_two_pow (a p : ℕ) :
    ∀ᶠ t : ℕ in atTop, a * (t + 1) ^ p ≤ 2 ^ t := by
  filter_upwards [eventually_nat_polynomial_le_two_pow (a * 2 ^ p) p,
    eventually_ge_atTop 1] with t ht hpos
  calc
    a * (t + 1) ^ p ≤ a * (2 * t) ^ p :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = (a * 2 ^ p) * t ^ p := by rw [mul_pow]; ring
    _ ≤ 2 ^ t := ht

theorem delta_eventually_dyadic_polynomial_power (a b p E : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      a * (b * 2 ^ t * (t + 1) ^ p) ^ E ≤ 2 ^ ((E + 1) * t) := by
  filter_upwards [delta_eventually_shifted_polynomial_le_two_pow (a * b ^ E) (p * E)]
    with t ht
  calc
    a * (b * 2 ^ t * (t + 1) ^ p) ^ E =
        ((a * b ^ E) * (t + 1) ^ (p * E)) * 2 ^ (E * t) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t E]
      ring
    _ ≤ 2 ^ t * 2 ^ (E * t) := Nat.mul_le_mul_right _ ht
    _ = 2 ^ ((E + 1) * t) := by rw [← pow_add]; congr 1; ring

def deltaSeedCostCeiling (d₀ : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (d₀ + 1), deltaSeedCostConstant d

lemma deltaSeedCostConstant_le_ceiling {d d₀ : ℕ} (hd : d ≤ d₀) :
    deltaSeedCostConstant d ≤ deltaSeedCostCeiling d₀ := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega))

lemma deltaSeedPower_mono : Monotone deltaSeedPower := by
  intro d e hde
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hde 1) 2)

theorem delta_eventually_uniform_seed_power (d₀ a p b : ℕ)
    (hb : deltaSeedPower d₀ + 1 ≤ b) :
    ∀ᶠ t : ℕ in atTop, ∀ d ≤ d₀, ∀ D : ℕ, 0 < D →
      D ≤ a * 2 ^ t * (t + 1) ^ p →
      deltaSeedCostConstant d * D ^ deltaSeedPower d ≤ 2 ^ (b * t) := by
  filter_upwards [delta_eventually_dyadic_polynomial_power
    (deltaSeedCostCeiling d₀) a p (deltaSeedPower d₀)] with t ht
  intro d hd D hD hbound
  calc
    deltaSeedCostConstant d * D ^ deltaSeedPower d ≤
        deltaSeedCostCeiling d₀ * D ^ deltaSeedPower d₀ := Nat.mul_le_mul
      (deltaSeedCostConstant_le_ceiling hd) (Nat.pow_le_pow_right hD (deltaSeedPower_mono hd))
    _ ≤ deltaSeedCostCeiling d₀ * (a * 2 ^ t * (t + 1) ^ p) ^ deltaSeedPower d₀ :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbound _)
    _ ≤ 2 ^ ((deltaSeedPower d₀ + 1) * t) := ht
    _ ≤ 2 ^ (b * t) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ hb)

theorem delta_eventually_uniform_seed_budgets (d₀ a p b : ℕ)
    (hb : deltaSeedPower d₀ + 1 ≤ b) :
    ∀ᶠ t : ℕ in atTop, ∀ d ≤ d₀, ∀ D c I : ℕ, 0 < D →
      D ≤ a * 2 ^ t * (t + 1) ^ p → c ≤ D → I ≤ D ^ d →
      let h := 2 ^ (b * t)
      let q := denseBoxCount D d
      let F := nvDenseFactor D d * (q + 1) ^ d
      let J := (2 * q * F) ^ d
      q * (c * h) + J ^ 2 ≤ h ^ 2 ∧
        ∀ L : Fin d → ℕ, (∀ i, 0 < L i) → ∀ i,
          2 * F * (GeneralizedAP.deltaSeedLatticeFactor d * (I * (L i + 1) + 1) +
            J * L i + 1) ≤ 2 * (h * L i) := by
  filter_upwards [delta_eventually_uniform_seed_power d₀ a p b hb] with t ht
  intro d hd D c I hD hbound hc hI
  exact delta_seed_budgets_of_power_bound d D c (2 ^ (b * t)) I hD hc hI
    (ht d hd D hD hbound)

end Erdos587.CFP
