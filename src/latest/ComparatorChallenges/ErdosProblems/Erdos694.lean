/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import ErdosProblems.Axioms

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise
namespace Erdos694

open Filter Asymptotics Topology
open scoped BigOperators Nat

noncomputable def R (x : ℕ) : ℝ :=
  ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
    let mmax := sSup {m | Nat.totient m = n}
    let mmin := sInf {m | Nat.totient m = n}
    (mmax : ℝ) / mmin
namespace LowerConstruction

open Filter
open scoped BigOperators Nat

noncomputable def smallPrimes (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter Nat.Prime

noncomputable def P (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, p

noncomputable def A (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, (p - 1)

noncomputable def largeFactors (Y U : ℕ) : Finset ℕ :=
  U.primeFactors.filter fun q => Y < q

noncomputable def Q (Y U : ℕ) : ℕ :=
  ∏ q ∈ largeFactors Y U, q
end LowerConstruction

end Erdos694

open Filter Asymptotics Topology
open scoped BigOperators Nat
open Filter

namespace Erdos694

open scoped Classical in
theorem totient_sq_ge_half (m : ℕ) (_hm : 1 ≤ m) : m ≤ 2 * (Nat.totient m) ^ 2 := by
  sorry

open scoped Classical in
theorem landau_max_ratio :
    Tendsto
      (fun T : ℝ => (⨆ m ∈ Set.Icc 1 ⌊T⌋₊,
        (m : ℝ) / Nat.totient m) / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log T)))
      atTop (𝓝 1) := by
  sorry

open scoped Classical in
theorem R_upper_bound :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log x) := by
  sorry

end Erdos694
namespace Erdos694.LowerConstruction

open scoped Classical in
lemma totient_a_eq_totient_b (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (hU_pos : 0 < U) (hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    Nat.totient (ℓ * Q Y U) = Nat.totient (P Y * U * Q Y U) := by
  sorry

end Erdos694.LowerConstruction
namespace Erdos694

open scoped Classical in
theorem collision_at_height :
    ∀ (C : ℝ) (L : ℕ), 1 ≤ C → 1 ≤ L →
      (∀ M : ℕ, 1 ≤ M →
        ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L) →
      ∀ ε : ℝ, 0 < ε →
        ∃ K : ℝ, 0 < K ∧
          ∀ᶠ Y : ℕ in atTop,
            ∃ a b n : ℕ,
              1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧
              Nat.totient a = n ∧ Nat.totient b = n ∧
              (b : ℝ) / a ≥
                (Real.exp Real.eulerMascheroniConstant - ε) * Real.log Y ∧
              (n : ℝ) ≤ Real.exp (K * Y) := by
  sorry

open scoped Classical in
theorem totient_collision_construction :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧ n ≤ x ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        (b : ℝ) / a ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  sorry

open scoped Classical in
theorem R_lower_bound :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  sorry

open scoped Classical in
theorem totient_fibre_extremes :
    Tendsto
      (fun x : ℕ => R x / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := by
  sorry

open scoped Classical in
theorem permanence_step (a b r : ℕ)
    (hab : Nat.totient a = Nat.totient b) (hr : Nat.Prime r) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b) :
    Nat.totient (r * a) = Nat.totient (r * b) := by
  sorry

open scoped Classical in
theorem infinitely_many_collisions (a b : ℕ) (hb : 1 ≤ b) (hgt : b < a)
    (hab : Nat.totient a = Nat.totient b) :
    {N : ℕ | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧ y < x ∧ b * x ≥ a * y}.Infinite := by
  sorry

open scoped Classical in
theorem erdos_694_asymptotic :
    Tendsto
      (fun x : ℕ => R x /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := by
  sorry

end Erdos694
