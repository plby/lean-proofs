import Mathlib

open scoped BigOperators
open Classical Finset

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos395

noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

end Erdos395

namespace Erdos395

abbrev SignVec (m : ℕ) := Fin m → Bool

end Erdos395

namespace Erdos395

def sign (b : Bool) : ℝ := if b then 1 else -1

end Erdos395

namespace Erdos395

def signedSum {n : ℕ} (z : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i, (sign (ε i) : ℂ) * z i

end Erdos395

namespace Erdos395

theorem erdos395 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 0 < n → ∀ (z : Fin n → ℂ),
        (∀ i, ‖z i‖ = 1) →
        c / (n : ℝ) ≤
          uniformProbability (fun ε : SignVec n ↦
            ‖signedSum z ε‖ ≤ Real.sqrt 2) := by
  sorry

end Erdos395

end
