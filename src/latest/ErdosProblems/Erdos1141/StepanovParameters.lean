import ErdosProblems.Erdos1141.StepanovRootCount
import Mathlib.Data.Nat.Sqrt

/-!
# Parameters for the quadratic Stepanov construction
-/

namespace Pollack17.Stepanov

open Polynomial

theorem constraints_lt_coefficients {A B D d : ℕ}
    (hB : 1 ≤ B) (hD : D + 1 = 2 * B) (hA : 4 * (d + 1) * B ^ 2 < A) :
    D * (A + B + D * d + 1) < 2 * A * B := by
  have hDle : D ≤ 2 * B := by omega
  have hDd : D * d ≤ 2 * B * d := Nat.mul_le_mul_right d hDle
  have hinner : B + D * d + 1 ≤ 2 * B * (d + 1) := by nlinarith
  have hcost : D * (B + D * d + 1) ≤ 4 * (d + 1) * B ^ 2 := by
    calc
      D * (B + D * d + 1) ≤ (2 * B) * (2 * B * (d + 1)) :=
        Nat.mul_le_mul hDle hinner
      _ = _ := by ring
  have hDA : D * A + A = 2 * A * B := by
    calc
      D * A + A = (D + 1) * A := by ring
      _ = 2 * A * B := by rw [hD]; ring
  calc
    D * (A + B + D * d + 1) = D * A + D * (B + D * d + 1) := by ring
    _ < D * A + A := Nat.add_lt_add_left (hcost.trans_lt hA) _
    _ = 2 * A * B := hDA

theorem half_characteristic_parameters {p B d : ℕ} (hp : 0 < p) (hB : 1 ≤ B)
    (hsmall : 16 * (d + 1) * B ^ 2 ≤ p) :
    let A := (p - 1) / 2
    let D := 2 * B - 1
    A + A ≤ p ∧ D ≤ p ∧ D * (A + B + D * d + 1) < 2 * A * B := by
  dsimp only
  let A := (p - 1) / 2
  let D := 2 * B - 1
  have hdiv := Nat.div_mul_le_self (p - 1) 2
  have hmod := Nat.mod_add_div (p - 1) 2
  have hmodlt := Nat.mod_lt (p - 1) (by norm_num : 0 < 2)
  have hAlower : p ≤ 2 * A + 2 := by dsimp [A]; omega
  have hAupper : A + A ≤ p := by dsimp [A]; omega
  have hD : D + 1 = 2 * B := by dsimp [D]; omega
  have hBsq : B ≤ B ^ 2 := by nlinarith
  have hterm : 1 ≤ (d + 1) * B ^ 2 := by
    change 0 < (d + 1) * B ^ 2
    positivity
  have hprod : B ^ 2 ≤ (d + 1) * B ^ 2 := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hlarge : 4 * (d + 1) * B ^ 2 < A := by nlinarith
  have hDp : D ≤ p := by nlinarith
  exact ⟨hAupper, hDp, constraints_lt_coefficients hB hD hlarge⟩

theorem quadratic_fiber_card_bound_small_square
    {K : Type*} [Field K] {p B : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) {x₀ : K} (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1)
    (hB : 1 ≤ B) (hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p)
    (S : Finset K)
    (hS : ∀ x ∈ S, x ^ p = x ∧ f.eval x ≠ 0 ∧ f.eval x ^ ((p - 1) / 2) = 1) :
    2 * (2 * B - 1) * S.card ≤ p * (2 * B - 1) + p * (f.natDegree + 2) := by
  obtain ⟨hA, hDp, hdim⟩ := half_characteristic_parameters
    (Fact.out : p.Prime).pos hB hsmall
  have hcount := quadratic_fiber_card_bound f hf hroot le_rfl hA hDp hdim S hS
  have hD : (2 * B - 1) + 1 = 2 * B := by omega
  have hAd := Nat.mul_le_mul_right f.natDegree hA
  nlinarith

end Pollack17.Stepanov
