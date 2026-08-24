/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos395

open scoped Classical in
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

abbrev SignVec (m : ℕ) := Fin m → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

def signedSum {n : ℕ} (z : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i, (sign (ε i) : ℂ) * z i

theorem erdos_395 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 0 < n → ∀ (z : Fin n → ℂ),
        (∀ i, ‖z i‖ = 1) →
        c / (n : ℝ) ≤
          uniformProbability (fun ε : SignVec n ↦
            ‖signedSum z ε‖ ≤ Real.sqrt 2) := by
  sorry

end Erdos395
